import argparse
import os
import time
import re
import json
import asyncio
import logging
import signal
from playwright.async_api import async_playwright

logging.basicConfig(level=logging.INFO, format="%(asctime)s %(levelname)s %(message)s")

MOBILE_UA = "Mozilla/5.0 (Linux; Android 13; vivo V60) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/119.0.0.0 Mobile Safari/537.36"

MOBILE_VIEWPORT = {"width": 412, "height": 915}  # Typical Android phone size

LAUNCH_ARGS = [
    "--disable-dev-shm-usage",
    "--no-sandbox",
    "--disable-gpu",
    "--disable-extensions",
    "--disable-sync",
    "--disable-background-networking",
    "--disable-background-timer-throttling",
    "--disable-renderer-backgrounding",
    "--mute-audio",
]


async def launch_chromium(playwright, headless):
    try:
        return await playwright.chromium.launch(headless=headless, args=LAUNCH_ARGS)
    except Exception:
        logging.exception(
            "Chromium launch failed (executable=%s, cwd=%s)",
            playwright.chromium.executable_path,
            os.getcwd(),
        )
        raise


def sanitize_input(raw):
    """
    Fix shell-truncated input (e.g., when '&' breaks in CMD or bot execution).
    If input comes as a list (from nargs='+'), join it back into a single string.
    """
    if isinstance(raw, list):
        raw = " ".join(raw)
    return raw

def parse_messages(names_arg):
    """
    Robust parser for messages:
    - If names_arg is a .txt file, first try JSON-lines parsing (one JSON string per line, supporting multi-line messages).
    - If that fails, read the entire file content as a single block and split only on explicit separators '&' or 'and' (preserving newlines within each message for ASCII art).
    - For direct string input, treat as single block and split only on separators.
    This ensures ASCII art (multi-line blocks without separators) is preserved as a single message.
    """
    # Handle argparse nargs possibly producing a list
    if isinstance(names_arg, list):
        names_arg = " ".join(names_arg)

    content = None  
    is_file = isinstance(names_arg, str) and names_arg.endswith('.txt') and os.path.exists(names_arg)  

    if is_file:  
        # Try JSON-lines first (each line is a JSON-encoded string, possibly with \n for multi-line)  
        try:  
            msgs = []  
            with open(names_arg, 'r', encoding='utf-8') as f:  
                lines = [ln.rstrip('\n') for ln in f if ln.strip()]  # Skip empty lines  
            for ln in lines:  
                m = json.loads(ln)  
                if isinstance(m, str):  
                    msgs.append(m)  
                else:  
                    raise ValueError("JSON line is not a string")  
            if msgs:  
                # Normalize each message (preserve \n for art)  
                out = []  
                for m in msgs:  
                    #m = unicodedata.normalize("NFKC", m)  
                    #m = re.sub(r'[\u200B-\u200F\uFEFF\u202A-\u202E\u2060-\u206F]', '', m)  
                    out.append(m)  
                return out  
        except Exception:  
            pass  # Fall through to block parsing on any error  

        # Fallback: read entire file as one block for separator-based splitting  
        try:  
            with open(names_arg, 'r', encoding='utf-8') as f:  
                content = f.read()  
        except Exception as e:  
            raise ValueError(f"Failed to read file {names_arg}: {e}")  
    else:  
        # Direct string input  
        content = str(names_arg)  

    if content is None:  
        raise ValueError("No valid content to parse")  

    # Normalize content (preserve \n for ASCII art)  
    #content = unicodedata.normalize("NFKC", content)  
    #content = content.replace("\r\n", "\n").replace("\r", "\n")  
    #content = re.sub(r'[\u200B-\u200F\uFEFF\u202A-\u202E\u2060-\u206F]', '', content)  

    # Normalize ampersand-like characters to '&' for consistent splitting  
    content = (  
        content.replace('﹠', '&')  
        .replace('＆', '&')  
        .replace('⅋', '&')  
        .replace('ꓸ', '&')  
        .replace('︔', '&')  
    )  

    # Split only on explicit separators: '&' or the word 'and' (case-insensitive, with optional whitespace)  
    # This preserves multi-line blocks like ASCII art unless explicitly separated  
    pattern = r'\s*(?:&|\band\b)\s*'  
    parts = [part.strip() for part in re.split(pattern, content, flags=re.IGNORECASE) if part.strip()]  
    return parts

async def login(args, storage_path, headless):
    """
    Async login function to handle initial Instagram login and save storage state.
    """
    async with async_playwright() as p:
        browser = None
        context = None
        try:
            browser = await launch_chromium(p, headless)
            context = await browser.new_context(
                user_agent=MOBILE_UA,
                viewport=MOBILE_VIEWPORT,
                is_mobile=True,
                has_touch=True,
                device_scale_factor=2,
                color_scheme="dark"
            )
            page = await context.new_page()
            print("Logging in to Instagram...")
            await page.goto("https://www.instagram.com/", timeout=60000)
            await page.wait_for_selector('input[name="username"]', timeout=30000)
            await page.fill('input[name="username"]', args.username)
            await page.fill('input[name="password"]', args.password)
            await page.click('button[type="submit"]')
            await page.wait_for_url("**/home**", timeout=60000)
            print("Login successful, saving storage state.")
            await context.storage_state(path=storage_path)
            return True
        finally:
            try:
                if context is not None:
                    await context.close()
            finally:
                if browser is not None:
                    await browser.close()

async def init_page(page, url, dm_selector):
    """
    Initialize a single page by navigating to the URL with retries.
    Returns True if successful, False otherwise.
    """
    init_success = False
    for init_try in range(3):
        try:
            await page.goto("https://www.instagram.com/", timeout=60000)
            await page.goto(url, timeout=60000)
            await page.wait_for_selector(dm_selector, timeout=30000)
            init_success = True
            break
        except Exception as init_e:
            print(f"Tab for {url[:30]}... try {init_try+1}/3 failed: {init_e}")
            if init_try < 2:
                await asyncio.sleep(2)
    return init_success

async def sender(tab_id, messages, page):
    """
    Async sender coroutine: Cycles through messages in an infinite loop, preloading/reloading pages every 60s to avoid issues.
    Preserves newlines in messages for multi-line content like ASCII art.
    Uses shared context to create new pages for reloading.
    Enhanced with retry logic: If selector not visible or send fails, retry up to 2 times (press Enter to clear if stuck, then refill), skip if all retries fail, never crash.
    """
    dm_selector = '[contenteditable="true"][role="textbox"]'
    print(f"Tab {tab_id} ready, starting infinite message loop.")
    current_page = page
    cycle_start = time.time()
    msg_index = 0
    while True:
        elapsed = time.time() - cycle_start
        if elapsed >= 60:
            try:
                print(f"Tab {tab_id} reloading thread after {elapsed:.1f}s")
                # Same URL ka hard reload, kahin aur nahi jayega
                await current_page.reload(timeout=60000)
                await current_page.wait_for_selector(dm_selector, timeout=30000)
            except Exception as reload_e:
                print(f"Tab {tab_id} reload failed after {elapsed:.1f}s: {reload_e}")
                raise Exception(f"Tab {tab_id} reload failed: {reload_e}")
            cycle_start = time.time()
            continue
        msg = messages[msg_index]
        send_success = False
        max_retries = 2
        for retry in range(max_retries):
            try:
                if not current_page.locator(dm_selector).is_visible():
                    print(f"Tab {tab_id} selector not visible on retry {retry+1}/{max_retries} for '{msg[:50]}...', attempting Enter to clear.")
                    try:
                        await current_page.press(dm_selector, 'Enter')
                        await asyncio.sleep(0.2)
                    except:
                        pass  # Ignore clear failure
                    await asyncio.sleep(0.5)  # Wait for potential update
                    continue  # Retry visibility check

                await current_page.click(dm_selector)
                # DO NOT replace \n with space: Preserve multi-line for ASCII art
                # Instagram DM supports multi-line messages via fill()
                await current_page.fill(dm_selector, msg)
                await current_page.press(dm_selector, 'Enter')
                print(f"Tab {tab_id} sent message {msg_index + 1}/{len(messages)} on retry {retry+1}")
                send_success = True
                break
            except Exception as send_e:
                print(f"Tab {tab_id} send error on retry {retry+1}/{max_retries} for message {msg_index + 1}: {send_e}")
                if retry < max_retries - 1:
                    print(f"Tab {tab_id} retrying after brief pause...")
                    await asyncio.sleep(0.5)
                else:
                    print(f"Tab {tab_id} all retries failed for message {msg_index + 1}, triggering restart.")
        if not send_success:
            raise Exception(f"Tab {tab_id} failed to send after {max_retries} retries")
        await asyncio.sleep(0.24)  # Brief delay between successful sends
        msg_index = (msg_index + 1) % len(messages)

async def main():
    parser = argparse.ArgumentParser(description="Instagram DM Auto Sender using Playwright")
    parser.add_argument('--username', default=os.environ.get("INSTAGRAM_USERNAME"), help='Instagram username (required for initial login)')
    parser.add_argument('--thread-url', required=True, help='Full Instagram direct thread URLs (comma-separated for multiple)')
    parser.add_argument('--names', nargs='+', required=True, help='Messages list, direct string, or .txt file (split on & or "and" for multiple; preserves newlines for art)')
    parser.add_argument('--headless', default='true', choices=['true', 'false'], help='Run in headless mode (default: true)')
    parser.add_argument('--storage-state', required=True, help='Path to JSON file for login state (persists session)')
    parser.add_argument('--tabs', type=int, default=1, help='Number of parallel tabs per thread URL (1-5, default 1)')
    args = parser.parse_args()
    args.password = os.environ.get("INSTAGRAM_PASSWORD")
    args.names = sanitize_input(args.names)  # Handle bot/shell-truncated inputs

    loop = asyncio.get_running_loop()
    main_task = asyncio.current_task()
    if main_task is not None:
        loop.add_signal_handler(signal.SIGTERM, main_task.cancel)

    thread_urls = [u.strip() for u in args.thread_url.split(',') if u.strip()]
    if not thread_urls:
        print("Error: No valid thread URLs provided.")
        return

    headless = args.headless == 'true'  
    storage_path = args.storage_state  
    do_login = not os.path.exists(storage_path)  

    if do_login:  
        if not args.username or not args.password:  
            print("Error: Username and password required for initial login.")  
            return  
        success = await login(args, storage_path, headless)
        if not success:
            return
    else:  
        print("Using existing storage state, skipping login.")  

    try:  
        messages = parse_messages(args.names)  
    except ValueError as e:  
        print(f"Error parsing messages: {e}")  
        return  

    if not messages:  
        print("Error: No valid messages provided.")  
        return  

    print(f"Parsed {len(messages)} messages.")  

    tabs = min(max(args.tabs, 1), 5)  
    total_tabs = len(thread_urls) * tabs
    print(f"Using {tabs} tabs per URL across {len(thread_urls)} URLs (total: {total_tabs} tabs).")  

    async with async_playwright() as p:
        browser = None
        context = None
        pages = []
        tasks = []
        try:
            browser = await launch_chromium(p, headless)
            context = await browser.new_context(
                storage_state=storage_path,
                user_agent=MOBILE_UA,
                viewport=MOBILE_VIEWPORT,
                is_mobile=True,
                has_touch=True,
                device_scale_factor=2,
                color_scheme="dark"
            )
            dm_selector = '[contenteditable="true"][role="textbox"]'
            while True:
                # Close previous pages and cancel tasks if any
                for page in pages:
                    try:
                        await page.close()
                    except Exception:
                        logging.exception("Failed to close a browser page before retrying")
                pages = []
                for task in tasks:
                    task.cancel()
                if tasks:
                    await asyncio.gather(*tasks, return_exceptions=True)
                tasks = []

                # Create all pages first
                page_urls = []
                for url in thread_urls:
                    for _ in range(tabs):
                        page = await context.new_page()
                        page_urls.append((page, url))

                # Initialize all pages concurrently
                init_tasks = [asyncio.create_task(init_page(page, url, dm_selector)) for page, url in page_urls]
                init_results = await asyncio.gather(*init_tasks, return_exceptions=True)

                # Filter successful initializations
                for result, (page, url) in zip(init_results, page_urls):
                    if isinstance(result, Exception) or not result:
                        print(f"Tab for {url} failed to initialize after 3 tries, skipping.")
                        try:
                            await page.close()
                        except Exception:
                            logging.exception("Failed to close an uninitialized browser page")
                    else:
                        pages.append(page)
                        print(f"Tab {len(pages)} ready for {url[:50]}...")

                if not pages:
                    print("No tabs could be initialized, exiting.")
                    return

                actual_tabs = len(pages)
                tasks = [
                    asyncio.create_task(sender(j + 1, messages, pages[j]))
                    for j in range(actual_tabs)
                ]
                print(f"Starting {actual_tabs} tab(s) in infinite message loop. Press Ctrl+C to stop.")

                pending = set(tasks)
                while pending:
                    done, pending = await asyncio.wait(pending, return_when=asyncio.FIRST_COMPLETED)
                    for task in done:
                        if task.exception():
                            exc = task.exception()
                            print(f"Tab task raised exception: {exc}")
                            # Cancel remaining tasks
                            for t in list(pending):
                                t.cancel()
                            await asyncio.gather(*pending, return_exceptions=True)
                            pending.clear()
                            break
                    else:
                        continue
                    break  # If we broke due to exception, exit inner while
        except asyncio.CancelledError:
            logging.info("Received shutdown request; closing browser resources.")
        except KeyboardInterrupt:
            print("\nStopping all tabs...")
        finally:
            for task in tasks:
                if not task.done():
                    task.cancel()
            if tasks:
                await asyncio.gather(*tasks, return_exceptions=True)
            for page in pages:
                try:
                    await page.close()
                except Exception:
                    logging.exception("Failed to close a browser page during cleanup")
            try:
                if context is not None:
                    await context.close()
            except Exception:
                logging.exception("Failed to close the browser context during cleanup")
            try:
                if browser is not None:
                    await browser.close()
            except Exception:
                logging.exception("Failed to close Chromium during cleanup")

if __name__ == "__main__":
    asyncio.run(main())