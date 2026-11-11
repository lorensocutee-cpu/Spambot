import datetime
import json
import os
import time
import random
import logging
import traceback
import unicodedata
import re
import math
import urllib.parse
import subprocess
import pty
import errno
import sys
from typing import Dict, List
from playwright.async_api import async_playwright, TimeoutError as PlaywrightTimeoutError
import threading
import uuid
import signal
from telegram import Update
from telegram.ext import Application, CommandHandler, MessageHandler, filters, ConversationHandler, ContextTypes
import asyncio
from dotenv import load_dotenv
from instagrapi import Client
from instagrapi.exceptions import ChallengeRequired, TwoFactorRequired, PleaseWaitFewMinutes, RateLimitError, LoginRequired
import psutil

PROJECT_DIR = os.path.dirname(os.path.abspath(__file__))
ENV_FILE = os.path.join(PROJECT_DIR, ".env")
load_dotenv(ENV_FILE)

os.umask(0o077)
MESSAGE_PROCESS_LOG = os.path.join(PROJECT_DIR, "msg.log")
if os.path.isfile(ENV_FILE):
    os.chmod(ENV_FILE, 0o600)

logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(levelname)s - %(message)s',
    handlers=[
        logging.FileHandler(os.path.join(PROJECT_DIR, 'instagram_bot.log')),
        logging.StreamHandler()
    ]
)
for noisy_logger in ("telegram", "httpx", "httpcore"):
    logging.getLogger(noisy_logger).setLevel(logging.WARNING)

user_fetching = set()
user_cancel_fetch = set()  # new set
AUTHORIZED_FILE = os.path.join(PROJECT_DIR, 'authorized_users.json')
TASKS_FILE = os.path.join(PROJECT_DIR, 'tasks.json')


def _required_environment_variable(name: str) -> str:
    value = os.environ.get(name)
    if value is None or not value.strip():
        raise RuntimeError(f"Required environment variable {name} is not set")
    return value.strip()


try:
    OWNER_TG_ID = int(_required_environment_variable('OWNER_TG_ID'))
except ValueError:
    raise RuntimeError("Environment variable OWNER_TG_ID must be an integer") from None
if OWNER_TG_ID <= 0:
    raise RuntimeError("Environment variable OWNER_TG_ID must be a positive integer")

BOT_TOKEN = _required_environment_variable('BOT_TOKEN')
USER_AGENT = "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/128.0.0.0 Safari/537.36"
TELEGRAM_TEXT_LIMIT = 4096


class BrowserLaunchError(RuntimeError):
    """Raised when the Playwright browser cannot be started."""


async def launch_chromium(playwright, **options):
    try:
        return await playwright.chromium.launch(**options)
    except Exception:
        logging.exception(
            "[PLAYWRIGHT] Chromium launch failed (executable=%s, cwd=%s). "
            "Install the browser and Linux libraries with "
            "'python -m playwright install chromium' and "
            "'sudo python -m playwright install-deps chromium'.",
            playwright.chromium.executable_path,
            PROJECT_DIR,
        )
        raise BrowserLaunchError(
            "Chromium could not be started; see the server log for the missing executable or Linux library."
        ) from None


authorized_users = []  # list of {'id': int, 'username': str}
users_data: Dict[int, Dict] = {}  # unlocked data {'accounts': list, 'default': int, 'pairs': dict or None, 'switch_minutes': int, 'threads': int}
users_pending: Dict[int, Dict] = {}  # pending challenges
users_tasks: Dict[int, List[Dict]] = {}  # tasks per user
persistent_tasks = []
running_processes: Dict[int, subprocess.Popen] = {}
waiting_for_otp = {}
user_queues = {}
user_fetching = set()

# Ensure sessions directory exists
os.makedirs(os.path.join(PROJECT_DIR, 'sessions'), mode=0o700, exist_ok=True)
os.chmod(os.path.join(PROJECT_DIR, 'sessions'), 0o700)
for sensitive_name in os.listdir(PROJECT_DIR):
    sensitive_path = os.path.join(PROJECT_DIR, sensitive_name)
    if sensitive_name == os.path.basename(AUTHORIZED_FILE) or (
        sensitive_name.startswith("user_") and sensitive_name.endswith(".json")
    ):
        if os.path.isfile(sensitive_path):
            os.chmod(sensitive_path, 0o600)
for session_name in os.listdir(os.path.join(PROJECT_DIR, "sessions")):
    session_path = os.path.join(PROJECT_DIR, "sessions", session_name)
    if os.path.isfile(session_path):
        os.chmod(session_path, 0o600)
if os.path.exists(os.path.join(PROJECT_DIR, "instagram_bot.log")):
    os.chmod(os.path.join(PROJECT_DIR, "instagram_bot.log"), 0o600)


def log_exception_safely(
    message: str,
    *sensitive_values: str,
    exc: BaseException | None = None,
) -> None:
    if exc is None:
        details = traceback.format_exc()
    else:
        details = "".join(
            traceback.format_exception(type(exc), exc, exc.__traceback__)
        )
    for secret in (BOT_TOKEN, *sensitive_values):
        if secret:
            details = details.replace(secret, "[REDACTED]")
    logging.error("%s\n%s", message, details.rstrip())


def _truncate_telegram_text(message: str) -> str:
    if len(message) <= TELEGRAM_TEXT_LIMIT:
        return message
    return message[: TELEGRAM_TEXT_LIMIT - 3] + "..."


async def reply_error_safely(update: Update, message: str) -> None:
    reply_target = update.effective_message
    if reply_target is None:
        logging.error("Unable to send an error reply: update has no effective message")
        return
    try:
        await reply_target.reply_text(_truncate_telegram_text(message))
    except Exception:
        log_exception_safely("Failed to send a concise Telegram error reply")


async def telegram_error_handler(
    update: Update | None,
    context: ContextTypes.DEFAULT_TYPE,
) -> None:
    error = context.error
    if error is None:
        logging.error("Telegram reported an update error without an exception")
        return

    sensitive_values = []
    user_id = update.effective_user.id if update and update.effective_user else None
    if user_id is not None:
        user_record = users_data.get(user_id)
        accounts = user_record.get("accounts", []) if isinstance(user_record, dict) else []
        for account in accounts if isinstance(accounts, list) else []:
            password = account.get("password") if isinstance(account, dict) else None
            if isinstance(password, str):
                sensitive_values.append(password)

    user_data = context.user_data or {}
    if isinstance(user_data, dict):
        for key, value in user_data.items():
            if any(part in str(key).lower() for part in ("password", "session", "token", "secret")):
                if isinstance(value, str):
                    sensitive_values.append(value)

    for key, value in os.environ.items():
        if any(part in key.lower() for part in ("password", "session", "token", "secret")):
            sensitive_values.append(value)

    try:
        log_exception_safely(
            "[TELEGRAM] Unhandled update error",
            *sensitive_values,
            exc=error,
        )
    except Exception:
        logging.error("[TELEGRAM] Failed to record an unhandled update error")

    if update is not None:
        try:
            await reply_error_safely(
                update,
                "❌ An unexpected error occurred. Please try again later.",
            )
        except Exception:
            logging.error("[TELEGRAM] Failed to send the concise error reply")


def _launch_message_process(command: List[str], username: str, password: str) -> subprocess.Popen:
    child_env = os.environ.copy()
    child_env.pop("BOT_TOKEN", None)
    child_env.pop("OWNER_TG_ID", None)
    child_env["INSTAGRAM_USERNAME"] = username
    child_env["INSTAGRAM_PASSWORD"] = password
    for key in tuple(child_env):
        if key not in ("INSTAGRAM_USERNAME", "INSTAGRAM_PASSWORD") and any(
            sensitive_part in key.upper()
            for sensitive_part in ("TOKEN", "PASSWORD", "SECRET", "SESSION")
        ):
            child_env.pop(key, None)

    try:
        with open(MESSAGE_PROCESS_LOG, "a", encoding="utf-8") as process_log:
            return subprocess.Popen(
                command,
                cwd=PROJECT_DIR,
                env=child_env,
                stdout=process_log,
                stderr=subprocess.STDOUT,
                start_new_session=True,
            )
    except OSError:
        logging.exception(
            "[PROCESS] Could not start worker (executable=%s, cwd=%s, log=%s)",
            command[0] if command else "<missing>",
            PROJECT_DIR,
            MESSAGE_PROCESS_LOG,
        )
        raise


def _stop_message_process(proc: subprocess.Popen, timeout: float = 3.0) -> bool:
    if proc.poll() is not None:
        return True
    try:
        os.killpg(proc.pid, signal.SIGTERM)
    except ProcessLookupError:
        pass
    except OSError:
        logging.exception("[PROCESS] Could not request graceful worker shutdown (pid=%s)", proc.pid)
        return False

    try:
        proc.wait(timeout=timeout)
    except subprocess.TimeoutExpired:
        try:
            os.killpg(proc.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        except OSError:
            logging.exception("[PROCESS] Could not force-stop worker process group (pid=%s)", proc.pid)
            return False
        try:
            proc.wait(timeout=timeout)
        except subprocess.TimeoutExpired:
            logging.error("[PROCESS] Worker did not exit after SIGKILL (pid=%s)", proc.pid)
            return False
    except OSError:
        logging.exception("[PROCESS] Failed while waiting for worker shutdown (pid=%s)", proc.pid)
        return False
    return True


def _stop_task_processes(task: Dict) -> bool:
    process_ids = task.get("proc_list")
    if not isinstance(process_ids, list):
        process_ids = []
    current_proc = task.get("proc")
    if isinstance(current_proc, subprocess.Popen) and current_proc.pid not in process_ids:
        process_ids = [*process_ids, current_proc.pid]

    stopped = True
    for pid in dict.fromkeys(process_ids):
        proc = running_processes.get(pid)
        if proc is None and isinstance(current_proc, subprocess.Popen) and current_proc.pid == pid:
            proc = current_proc
        if proc is None:
            logging.warning("[PROCESS] No live process handle for task PID %s; not signaling a potentially reused PID", pid)
            stopped = False
            continue
        stopped = _stop_message_process(proc) and stopped
        running_processes.pop(pid, None)
    return stopped


def _stop_persisted_message_process(task: Dict) -> bool:
    pid = task.get("pid")
    if isinstance(pid, bool) or not isinstance(pid, int) or pid <= 1:
        return False

    try:
        process = psutil.Process(pid)
        command = process.cmdline()
        names_file = os.path.realpath(_project_path(task["names_file"]))
        script_file = os.path.realpath(os.path.join(PROJECT_DIR, "msg.py"))
        if (
            len(command) < 2
            or os.path.realpath(command[1]) != script_file
            or "--names" not in command
            or os.path.realpath(command[command.index("--names") + 1]) != names_file
            or "--thread-url" not in command
            or command[command.index("--thread-url") + 1] != task["target_thread_url"]
        ):
            logging.warning("[TASKS] Not stopping stale PID %s: command does not match task", pid)
            return False

        expected_start = task.get("process_started_at", task.get("last_switch_time", task.get("start_time")))
        if not _is_finite_number(expected_start):
            logging.warning("[TASKS] Not stopping stale PID %s: task has no valid process start time", pid)
            return False
        if abs(process.create_time() - expected_start) > 120:
            logging.warning("[TASKS] Not stopping stale PID %s: process start time does not match task", pid)
            return False

        processes = process.children(recursive=True) + [process]
        for child in processes:
            try:
                child.terminate()
            except psutil.NoSuchProcess:
                continue
        _, alive = psutil.wait_procs(processes, timeout=3)
        for child in alive:
            try:
                child.kill()
            except psutil.NoSuchProcess:
                continue
        if alive:
            _, still_alive = psutil.wait_procs(alive, timeout=3)
            if still_alive:
                logging.error("[TASKS] Worker process tree did not stop for task PID %s", pid)
                return False
        return True
    except psutil.NoSuchProcess:
        return True
    except (psutil.AccessDenied, OSError, KeyError, ValueError, IndexError):
        logging.exception("[TASKS] Could not safely stop stale worker PID %s", pid)
        return False


def _project_path(path: str) -> str:
    return os.path.abspath(path if os.path.isabs(path) else os.path.join(PROJECT_DIR, path))


def _is_valid_instagram_username(username: str) -> bool:
    return isinstance(username, str) and re.fullmatch(r"[A-Za-z0-9._]{1,30}", username) is not None


def _is_finite_number(value) -> bool:
    if isinstance(value, bool) or not isinstance(value, (int, float)):
        return False
    try:
        return math.isfinite(value)
    except OverflowError:
        return False


def _is_within_project(path: str) -> bool:
    try:
        return os.path.commonpath((os.path.realpath(PROJECT_DIR), os.path.realpath(path))) == os.path.realpath(PROJECT_DIR)
    except ValueError:
        return False

# === PATCH: Fix instagrapi invalid timestamp bug ===
def _sanitize_timestamps(obj):
    """Keep representable epoch-microsecond timestamps expected by instagrapi."""
    if isinstance(obj, dict):
        new_obj = {}
        for k, v in obj.items():
            if type(v) is int and k.endswith("_timestamp_us"):
                try:
                    datetime.datetime.fromtimestamp(v // 1_000_000)
                except (OverflowError, OSError, ValueError):
                    new_obj[k] = None
                else:
                    new_obj[k] = v
            else:
                new_obj[k] = _sanitize_timestamps(v)
        return new_obj
    elif isinstance(obj, list):
        return [_sanitize_timestamps(i) for i in obj]
    else:
        return obj


async def playwright_login_and_save_state(username: str, password: str, user_id: int) -> str:
    """
    Async Playwright login.
    - Instagram me login karta hai
    - storage_state ko sessions/<user>_<username>_state.json me save karta hai
    - file path return karta hai
    """
    if not _is_valid_instagram_username(username):
        raise ValueError("Invalid Instagram username")
    username = username.lower()
    COOKIE_FILE = os.path.join(PROJECT_DIR, "sessions", f"{user_id}_{username}_state.json")

    async with async_playwright() as p:
        browser = None
        try:
            browser = await launch_chromium(
                p,
                headless=True,
                args=[
                    "--disable-gpu",
                    "--no-sandbox",
                    "--disable-dev-shm-usage",
                    "--disable-blink-features=AutomationControlled",
                ],
            )

            context = await browser.new_context(
                user_agent=USER_AGENT,
                viewport={"width": 1280, "height": 720},
            )
            page = await context.new_page()

            login_url = "https://www.instagram.com/accounts/login/?__coig_login=1"
            logging.info("[PLOGIN-ASYNC] Goto %s", login_url)

            await page.goto(login_url, wait_until="domcontentloaded", timeout=60000)
            await page.wait_for_timeout(3000)

            logging.info(
                "[PLOGIN-ASYNC] After goto -> URL=%s TITLE=%s",
                page.url,
                await page.title(),
            )

            username_inputs = await page.locator('input[name="username"]').count()
            if username_inputs == 0:
                logging.warning(
                    "[PLOGIN-ASYNC] Username field not found. URL=%s",
                    page.url,
                )
                await page.wait_for_timeout(5000)
                username_inputs = await page.locator('input[name=\"username\"]').count()

            if username_inputs == 0:
                logging.warning(
                    "[PLOGIN-ASYNC] Login form NOT loaded. URL=%s",
                    page.url,
                )
                raise ValueError("ERROR_010: Instagram login form not loaded")

            username_input = page.locator('input[name="username"]')
            password_input = page.locator('input[name="password"]')
            login_button = page.locator('button[type="submit"]').first

            await username_input.click()
            await page.wait_for_timeout(random.randint(300, 900))
            await username_input.fill("")
            await username_input.type(username, delay=random.randint(60, 140))

            await page.wait_for_timeout(random.randint(300, 900))
            await password_input.click()
            await page.wait_for_timeout(random.randint(200, 700))
            await password_input.fill("")
            await password_input.type(password, delay=random.randint(60, 140))

            await page.wait_for_timeout(random.randint(400, 1000))
            await login_button.click()
            logging.info("[PLOGIN-ASYNC] Submitted login form for %s", username)

            await page.wait_for_timeout(5000)

            current_url = page.url
            logging.info("[PLOGIN-ASYNC] After login URL=%s", current_url)

            otp_locator = page.locator('input[name="verificationCode"]')
            otp_count = await otp_locator.count()

            if otp_count > 0 or "challenge" in current_url or "two_factor" in current_url:
                logging.info(
                    "[PLOGIN-ASYNC] OTP / challenge detected for user %s (url=%s, otp_count=%s)",
                    username,
                    current_url,
                    otp_count,
                )
                raise ValueError("ERROR_OTP: OTP / challenge required")

            logging.info("[PLOGIN-ASYNC] No OTP required, login looks successful. URL=%s", current_url)
            await page.wait_for_timeout(4000)

            await context.storage_state(path=COOKIE_FILE)
            logging.info("[PLOGIN-ASYNC] storage_state saved")
        finally:
            if browser is not None:
                await browser.close()

    return COOKIE_FILE


# 🧩 Monkeypatch instagrapi to fix validation crash
try:
    import instagrapi.extractors as extractors
    _orig_extract_reply_message = extractors.extract_reply_message

    def patched_extract_reply_message(data):
        data = _sanitize_timestamps(data)
        return _orig_extract_reply_message(data)

    extractors.extract_reply_message = patched_extract_reply_message
    print("[Patch] Applied timestamp sanitizer to instagrapi extractors ✅")
except Exception as e:
    print(f"[Patch Warning] Could not patch instagrapi: {e}")
# === END PATCH ===

def _read_json_file(path: str):
    try:
        with open(path, "r", encoding="utf-8") as file:
            return json.load(file)
    except (OSError, UnicodeError, json.JSONDecodeError):
        logging.exception("[JSON] Could not read JSON file %s", path)
        return None


def _write_json_atomic(path: str, data) -> None:
    temp_path = f"{path}.{uuid.uuid4().hex}.tmp"
    try:
        with open(temp_path, "w", encoding="utf-8") as file:
            json.dump(data, file, indent=2)
        os.chmod(temp_path, 0o600)
        os.replace(temp_path, path)
    finally:
        if os.path.exists(temp_path):
            os.remove(temp_path)


def load_authorized() -> None:
    global authorized_users
    authorized_users = []
    if os.path.exists(AUTHORIZED_FILE):
        loaded_users = _read_json_file(AUTHORIZED_FILE)
        if isinstance(loaded_users, list):
            seen_ids = set()
            for entry in loaded_users:
                if not isinstance(entry, dict):
                    logging.warning("[AUTH] Ignoring malformed authorized-user entry")
                    continue
                user_id = entry.get("id")
                if isinstance(user_id, bool) or not isinstance(user_id, int) or user_id <= 0:
                    logging.warning("[AUTH] Ignoring authorized-user entry with invalid id")
                    continue
                if user_id in seen_ids:
                    continue
                username = entry.get("username", "")
                authorized_users.append({
                    "id": user_id,
                    "username": username if isinstance(username, str) else "",
                })
                seen_ids.add(user_id)
        elif loaded_users is not None:
            logging.error("[AUTH] Authorized-user JSON must contain a list; ignoring its contents")

    if not any(user["id"] == OWNER_TG_ID for user in authorized_users):
        authorized_users.append({"id": OWNER_TG_ID, "username": "owner"})

load_authorized()


def load_users_data() -> None:
    global users_data
    users_data = {}
    for file in os.listdir(PROJECT_DIR):
        if file.startswith('user_') and file.endswith('.json'):
            user_id_str = file[5:-5]
            if user_id_str.isdigit():
                user_id = int(user_id_str)
                path = os.path.join(PROJECT_DIR, file)
                data = _read_json_file(path)
                if not isinstance(data, dict):
                    logging.error("[USERS] Ignoring invalid user data in %s", file)
                    continue

                raw_accounts = data.get("accounts")
                if not isinstance(raw_accounts, list):
                    logging.error("[USERS] Ignoring %s: accounts must be a list", file)
                    continue
                accounts = []
                for account in raw_accounts:
                    if not isinstance(account, dict):
                        logging.warning("[USERS] Ignoring malformed account in %s", file)
                        continue
                    username = account.get("ig_username")
                    password = account.get("password", "")
                    storage_state = account.get("storage_state", {})
                    if (
                        not _is_valid_instagram_username(username)
                        or not isinstance(password, str)
                        or not isinstance(storage_state, dict)
                    ):
                        logging.warning("[USERS] Ignoring invalid account data in %s", file)
                        continue
                    accounts.append({
                        "ig_username": username.strip().lower(),
                        "password": password,
                        "storage_state": storage_state,
                    })

                default = data.get("default")
                if not accounts:
                    default = None
                elif (
                    isinstance(default, bool)
                    or not isinstance(default, int)
                    or not 0 <= default < len(accounts)
                ):
                    default = 0

                pairs = data.get("pairs")
                if pairs is not None:
                    pair_list = pairs.get("list") if isinstance(pairs, dict) else None
                    pair_index = pairs.get("default_index") if isinstance(pairs, dict) else None
                    account_names = {account["ig_username"] for account in accounts}
                    if (
                        not isinstance(pair_list, list)
                        or not pair_list
                        or not all(isinstance(name, str) and name in account_names for name in pair_list)
                        or isinstance(pair_index, bool)
                        or not isinstance(pair_index, int)
                        or not 0 <= pair_index < len(pair_list)
                    ):
                        logging.warning("[USERS] Discarding invalid account pairs in %s", file)
                        pairs = None

                switch_minutes = data.get("switch_minutes", 10)
                if (
                    isinstance(switch_minutes, bool)
                    or not isinstance(switch_minutes, int)
                    or switch_minutes < 5
                ):
                    switch_minutes = 10

                threads = data.get("threads", 1)
                if isinstance(threads, bool) or not isinstance(threads, int) or not 1 <= threads <= 5:
                    threads = 1

                users_data[user_id] = {
                    "accounts": accounts,
                    "default": default,
                    "pairs": pairs,
                    "switch_minutes": switch_minutes,
                    "threads": threads,
                }

load_users_data()

def save_authorized():
    _write_json_atomic(AUTHORIZED_FILE, authorized_users)

def save_user_data(user_id: int, data: Dict):
    _write_json_atomic(os.path.join(PROJECT_DIR, f'user_{user_id}.json'), data)

def is_authorized(user_id: int) -> bool:
    return any(u['id'] == user_id for u in authorized_users)

def is_owner(user_id: int) -> bool:
    return user_id == OWNER_TG_ID

def future_expiry(days=365):
    """Return Unix seconds, the unit Playwright expects for cookie expiry."""
    return int(time.time()) + days*24*3600

def convert_for_playwright(insta_file, playwright_file):
    data = _read_json_file(insta_file)
    if not isinstance(data, dict):
        raise ValueError(f"Invalid instagrapi settings file: {insta_file}")

    cookies = []
    auth = data.get("authorization_data", {})
    if not isinstance(auth, dict):
        raise ValueError("Invalid authorization_data in instagrapi settings")
    for name, value in auth.items():
        if not isinstance(name, str) or not isinstance(value, str):
            raise ValueError("Invalid cookie entry in instagrapi settings")
        cookies.append({
            "name": name,
            "value": urllib.parse.unquote(value),
            "domain": ".instagram.com",
            "path": "/",
            "expires": future_expiry(),
            "httpOnly": True,
            "secure": True,
            "sameSite": "Lax"
        })

    playwright_state = {
        "cookies": cookies,
        "origins": [{"origin": "https://www.instagram.com", "localStorage": []}]
    }

    _write_json_atomic(playwright_file, playwright_state)

def get_storage_state_from_instagrapi(settings: Dict):
    cl = Client()
    cl.set_settings(settings)

    # Collect cookies from instagrapi structures (compatible with multiple instagrapi versions)
    cookies_dict = {}
    if hasattr(cl, "session") and cl.session:
        try:
            cookies_dict = cl.session.cookies.get_dict()
        except Exception:
            cookies_dict = {}
    elif hasattr(cl, "private") and hasattr(cl.private, "cookies"):
        try:
            cookies_dict = cl.private.cookies.get_dict()
        except Exception:
            cookies_dict = {}
    elif hasattr(cl, "_http") and hasattr(cl._http, "cookies"):
        try:
            cookies_dict = cl._http.cookies.get_dict()
        except Exception:
            cookies_dict = {}

    cookies = []
    for name, value in cookies_dict.items():
        cookies.append({
            "name": name,
            "value": value,
            "domain": ".instagram.com",
            "path": "/",
            "expires": int(time.time()) + 365*24*3600,
            "httpOnly": True,
            "secure": True,
            "sameSite": "Lax"
        })

    storage_state = {
        "cookies": cookies,
        "origins": [{"origin": "https://www.instagram.com", "localStorage": []}]
    }
    return storage_state

def instagrapi_login(username, password):
    if not _is_valid_instagram_username(username):
        raise ValueError("Invalid Instagram username")
    username = username.lower()
    cl = Client()
    session_file = os.path.join(PROJECT_DIR, f"{username}_session.json")
    playwright_file = os.path.join(PROJECT_DIR, f"{username}_state.json")
    try:
        cl.login(username, password)
        cl.dump_settings(session_file)
        convert_for_playwright(session_file, playwright_file)
    except (ChallengeRequired, TwoFactorRequired):
        raise ValueError("ERROR_004: Login challenge or 2FA required")
    except (PleaseWaitFewMinutes, RateLimitError):
        raise ValueError("ERROR_002: Rate limit exceeded")
    except Exception as e:
        raise ValueError(f"ERROR_007: Login failed - {str(e)}")
    state = _read_json_file(playwright_file)
    if not isinstance(state, dict):
        raise ValueError(f"Invalid Playwright storage state: {playwright_file}")
    return state

def list_group_chats(user_id, storage_state, username, password, max_groups=10, amount=10):
    username = username.strip().lower()
    norm_username = username.strip().lower()
    session_file = os.path.join(PROJECT_DIR, "sessions", f"{user_id}_{norm_username}_session.json")
    playwright_file = os.path.join(PROJECT_DIR, "sessions", f"{user_id}_{norm_username}_state.json")
    cl = Client()
    updated = False
    new_state = None

    # Load existing session if available
    if os.path.exists(session_file):
        try:
            cl.load_settings(session_file)
        except Exception:
            pass

    try:
        threads = cl.direct_threads(amount=amount)
        time.sleep(random.uniform(1.0, 3.0))
    except LoginRequired:
        cl.login(username, password)
        cl.dump_settings(session_file)
        convert_for_playwright(session_file, playwright_file)
        updated = True
        threads = cl.direct_threads(amount=amount)
        time.sleep(random.uniform(1.0, 3.0))

    groups = []
    for thread in threads:
        if len(groups) >= max_groups:
            break
        if getattr(thread, "is_group", False):
            member_count = len(getattr(thread, "users", [])) + 1
            if member_count < 3:
                continue

            title = getattr(thread, "thread_title", None) or getattr(thread, "title", None)
            if not title or title.strip() == "":
                try:
                    users_part = ", ".join([u.username for u in getattr(thread, "users", [])][:3])
                    display = users_part if users_part else "<no name>"
                except Exception:
                    display = "<no name>"
            else:
                display = title

            url = f"https://www.instagram.com/direct/t/{getattr(thread, 'thread_id', getattr(thread, 'id', 'unknown'))}"
            groups.append({'display': display, 'url': url})

    if updated and os.path.exists(playwright_file):
        new_state = get_storage_state_from_instagrapi(cl.get_settings())
        _write_json_atomic(playwright_file, new_state)
    elif os.path.exists(playwright_file):
        new_state = _read_json_file(playwright_file)
        if not isinstance(new_state, dict):
            raise ValueError(f"Invalid Playwright storage state: {playwright_file}")
    else:
        new_state = storage_state

    return groups, new_state

def get_dm_thread_url(user_id, username, password, target_username):
    norm_username = username.strip().lower()
    session_file = os.path.join(PROJECT_DIR, "sessions", f"{user_id}_{norm_username}_session.json")
    playwright_file = os.path.join(PROJECT_DIR, "sessions", f"{user_id}_{norm_username}_state.json")
    cl = Client()
    updated = False

    if os.path.exists(session_file):
        try:
            cl.load_settings(session_file)
        except Exception:
            pass

    try:
        threads = cl.direct_threads(amount=10)
        time.sleep(random.uniform(1.0, 3.0))
    except LoginRequired:
        cl.login(username, password)
        cl.dump_settings(session_file)
        convert_for_playwright(session_file, playwright_file)
        updated = True
        threads = cl.direct_threads(amount=10)
        time.sleep(random.uniform(1.0, 3.0))

    for thread in threads:
        if not getattr(thread, 'is_group', True) and len(getattr(thread, 'users', [])) == 1:
            try:
                user = thread.users[0]
                if user.username == target_username:
                    thread_id = getattr(thread, 'thread_id', getattr(thread, 'id', None))
                    if thread_id:
                        url = f"https://www.instagram.com/direct/t/{thread_id}/"
                        if updated:
                            settings = cl.get_settings()
                            new_state = get_storage_state_from_instagrapi(settings)
                            _write_json_atomic(playwright_file, new_state)
                        return url
            except Exception:
                continue

    return None

def perform_login(page, username, password):
    try:
        page.evaluate("""() => {
            Object.defineProperty(navigator, 'webdriver', { get: () => undefined });
            Object.defineProperty(navigator, 'languages', { get: () => ['en-US', 'en'] });
            Object.defineProperty(navigator, 'plugins', { get: () => [1, 2, 3, 4, 5] });
            window.chrome = { app: {}, runtime: {} };
            const originalQuery = window.navigator.permissions.query;
            window.navigator.permissions.query = (parameters) => (
                parameters.name === 'notifications' ?
                Promise.resolve({ state: 'denied' }) :
                originalQuery(parameters)
            );
            const getParameter = WebGLRenderingContext.prototype.getParameter;
            WebGLRenderingContext.prototype.getParameter = function(parameter) {
                if (parameter === 37445) return 'Google Inc. (Intel)';
                if (parameter === 37446) return 'ANGLE (Intel, Intel(R) UHD Graphics 630 (0x00003E9B) Direct3D11 vs_5_0 ps_5_0, D3D11)';
                return getParameter.call(this, parameter);
            };
        }""")

        username_locator = page.locator('input[name="username"]')
        username_locator.wait_for(state='visible', timeout=10000)
        username_locator.focus()
        time.sleep(random.uniform(0.5, 1.5))
        for char in username:
            username_locator.press(char)
            time.sleep(random.uniform(0.05, 0.15))

        password_locator = page.locator('input[name="password"]')
        password_locator.wait_for(state='visible', timeout=10000)
        time.sleep(random.uniform(0.5, 1.5))
        password_locator.focus()
        time.sleep(random.uniform(0.3, 0.8))
        for char in password:
            password_locator.press(char)
            time.sleep(random.uniform(0.05, 0.15))

        time.sleep(random.uniform(1.0, 2.5))

        submit_locator = page.locator('button[type="submit"]')
        submit_locator.wait_for(state='visible', timeout=10000)
        if not submit_locator.is_enabled():
            raise Exception("Submit button not enabled")
        submit_locator.click()

        try:
            page.wait_for_url(lambda url: 'accounts/login' not in url and 'challenge' not in url and 'two_factor' not in url, timeout=60000)
            
            if page.locator('[role="alert"]').count() > 0:
                error_text = page.locator('[role="alert"]').inner_text().lower()
                if 'incorrect' in error_text or 'wrong' in error_text:
                    raise ValueError("ERROR_001: Invalid credentials")
                elif 'wait' in error_text or 'few minutes' in error_text or 'too many' in error_text:
                    raise ValueError("ERROR_002: Rate limit exceeded")
                else:
                    raise ValueError(f"ERROR_003: Login error - {error_text}")
        except PlaywrightTimeoutError:
            current_url = page.url
            page_content = page.content().lower()
            if 'challenge' in current_url:
                raise ValueError("ERROR_004: Login challenge required")
            elif 'two_factor' in current_url or 'verify' in current_url:
                raise ValueError("ERROR_005: 2FA verification required")
            elif '429' in page_content or 'rate limit' in page_content or 'too many requests' in page_content:
                raise ValueError("ERROR_002: Rate limit exceeded")
            elif page.locator('[role="alert"]').count() > 0:
                error_text = page.locator('[role="alert"]').inner_text().lower()
                raise ValueError(f"ERROR_006: Login failed - {error_text}")
            else:
                raise ValueError("ERROR_007: Login timeout or unknown error")

        logging.info("Login successful")
    except Exception as e:
        logging.error(f"Login failed: {str(e)}")
        raise

# ---------------- Globals for PTY ----------------
APP = None
LOOP = None
SESSIONS = {}
SESSIONS_LOCK = threading.Lock()

# ---------------- Child PTY login ----------------
def child_login(user_id: int, username: str, password: str):
    cl = Client()
    username = username.strip().lower()
    if not _is_valid_instagram_username(username):
        raise ValueError("Invalid Instagram username")
    session_file = os.path.join(PROJECT_DIR, "sessions", f"{user_id}_{username}_session.json")
    playwright_file = os.path.join(PROJECT_DIR, "sessions", f"{user_id}_{username}_state.json")
    try:
        print(f"[{username}] ⚙️ Attempting login.. if you are stucked here check your gmail or messages check for otp and enter otp here eg: 192122.")
        cl.login(username, password)
        cl.dump_settings(session_file)
        convert_for_playwright(session_file, playwright_file)
        print(f"[{username}] ✅ Logged in successfully. Session saved: {session_file}")
    except TwoFactorRequired:
        print(f" Enter code (6 digits) for {username} (2FA): ", end="", flush=True)
        otp = input().strip()
        try:
            cl.login(username, password, verification_code=otp)
            cl.dump_settings(session_file)
            convert_for_playwright(session_file, playwright_file)
            print(f"[{username}] ✅ OTP resolved. Logged in. Session saved: {session_file}")
        except Exception:
            log_exception_safely("[LOGIN] Two-factor verification failed", username, password)
            print(f"[{username}] ❌ OTP failed. Check the server logs.")
    except ChallengeRequired:
        print(f" Enter code (6 digits) for {username} (Challenge): ", end="", flush=True)
        otp = input().strip()
        try:
            cl.challenge_resolve(cl.last_json, security_code=otp)
            cl.dump_settings(session_file)
            convert_for_playwright(session_file, playwright_file)
            print(f"[{username}] ✅ OTP resolved. Logged in. Session saved: {session_file}")
        except Exception:
            log_exception_safely("[LOGIN] Challenge verification failed", username, password)
            print(f"[{username}] ❌ Challenge verification failed. Check the server logs.")
    except Exception:
        log_exception_safely("[LOGIN] Instagram login failed", username, password)
        print(f"[{username}] ❌ Login failed. Check the server logs.")
    finally:
        time.sleep(0.5)
        sys.exit(0)

# ---------------- PTY reader thread ----------------
def reader_thread(user_id: int, chat_id: int, master_fd: int, username: str, password: str):
    global APP, LOOP
    buf = b""
    while True:
        try:
            data = os.read(master_fd, 1024)
            if not data:
                break
            buf += data
            while b"\n" in buf or len(buf) > 2048:
                if b"\n" in buf:
                    line, buf = buf.split(b"\n", 1)
                    text = line.decode(errors="ignore").strip()
                else:
                    text = buf.decode(errors="ignore")
                    buf = b""
                if not text:
                    continue
                if text.startswith("Code entered"):
                    continue
                lower = text.lower()
                if (
                    len(text) > 300
                    or "cdninstagram.com" in lower
                    or "http" in lower
                    or "{" in text
                    or "}" in text
                    or "debug" in lower
                    or "info" in lower
                    or "urllib3" in lower
                    or "connection" in lower
                    or "starting new https" in lower
                    or "instagrapi" in lower
                ):
                    continue
                try:
                    if APP and LOOP:
                        asyncio.run_coroutine_threadsafe(
                            APP.bot.send_message(chat_id=chat_id, text=f"🔥{text}"), LOOP
                        )
                except Exception:
                    logging.error("[THREAD] send_message failed")
        except OSError as e:
            if e.errno == errno.EIO:
                break
            else:
                logging.error("[THREAD] PTY read error: %s", e)
                break
        except Exception as e:
            logging.error("[THREAD] Unexpected error: %s", e)
            break
    try:
        playwright_file = os.path.join(PROJECT_DIR, "sessions", f"{user_id}_{username}_state.json")
        if os.path.exists(playwright_file):
            state = _read_json_file(playwright_file)
            if not isinstance(state, dict):
                raise ValueError(f"Invalid Playwright storage state: {playwright_file}")
            if user_id in users_data:
                data = users_data[user_id]
            else:
                data = {'accounts': [], 'default': None, 'pairs': None, 'switch_minutes': 10, 'threads': 1}
            # normalize incoming username
            norm_username = username.strip().lower()

            for i, acc in enumerate(data['accounts']):
                if acc.get('ig_username', '').strip().lower() == norm_username:
                    # overwrite existing entry for exact same username (normalized)
                    data['accounts'][i] = {'ig_username': norm_username, 'password': password, 'storage_state': state}
                    data['default'] = i
                    break
            else:
                # not found -> append new normalized account
                data['accounts'].append({'ig_username': norm_username, 'password': password, 'storage_state': state})
                data['default'] = len(data['accounts']) - 1
            save_user_data(user_id, data)
            users_data[user_id] = data
            if APP and LOOP:
                asyncio.run_coroutine_threadsafe(APP.bot.send_message(chat_id=chat_id, text="✅ Login successful and saved securely! 🎉"), LOOP)
        else:
            if APP and LOOP:
                asyncio.run_coroutine_threadsafe(APP.bot.send_message(chat_id=chat_id, text="⚠️ Login failed. No session saved."), LOOP)
    except Exception:
        log_exception_safely("[LOGIN] Failed to save account data", password)
        if APP and LOOP:
            asyncio.run_coroutine_threadsafe(
                APP.bot.send_message(chat_id=chat_id, text="⚠️ Could not save account data. Check the server logs."),
                LOOP,
            )
    finally:
        with SESSIONS_LOCK:
            if user_id in SESSIONS:
                try:
                    os.close(SESSIONS[user_id]["master_fd"])
                except Exception:
                    pass
                SESSIONS.pop(user_id, None)

# ---------------- Relay input ----------------
async def relay_input(update: Update, context: ContextTypes.DEFAULT_TYPE):
    user_id = update.effective_user.id
    text = update.message.text
    with SESSIONS_LOCK:
        info = SESSIONS.get(user_id)
    if not info:
        return
    master_fd = info["master_fd"]
    try:
        os.write(master_fd, (text + "\n").encode())
    except OSError:
        log_exception_safely("[PTY] Failed to relay input")
        await reply_error_safely(update, "❌ Could not relay input to the login process.")
    except Exception:
        log_exception_safely("[PTY] Unexpected input relay failure")
        await reply_error_safely(update, "❌ Could not relay input to the login process.")

async def handle_text(update: Update, context: ContextTypes.DEFAULT_TYPE):
    user_id = update.effective_user.id
    text = update.message.text.strip()
    if user_id in waiting_for_otp:
        if len(text) == 6 and text.isdigit():
            user_queues[user_id].put(text)
            del waiting_for_otp[user_id]
            await update.message.reply_text("✅ Code submitted to browser! 🔄")
            return
        else:
            await update.message.reply_text("❌ Invalid code. Please enter 6-digit code.")
            return
    # Fallback to relay
    await relay_input(update, context)

# ---------------- Kill command ----------------
async def cmd_kill(update: Update, context: ContextTypes.DEFAULT_TYPE):
    user_id = update.effective_user.id
    with SESSIONS_LOCK:
        info = SESSIONS.get(user_id)
    if not info:
        await update.message.reply_text("No active PTY session.")
        return
    pid = info["pid"]
    master_fd = info["master_fd"]
    try:
        process = psutil.Process(pid)
        process.terminate()
        try:
            await asyncio.to_thread(process.wait, 3)
        except psutil.TimeoutExpired:
            process.kill()
            await asyncio.to_thread(process.wait, 3)
    except psutil.NoSuchProcess:
        logging.info("[PTY] Login process already exited (pid=%s)", pid)
    except (psutil.AccessDenied, OSError):
        logging.exception("[PTY] Could not stop login process (pid=%s)", pid)
        await reply_error_safely(update, "❌ Could not stop the login process. Check the server logs.")
        return
    try:
        os.close(master_fd)
    except OSError:
        logging.exception("[PTY] Could not close login terminal descriptor (pid=%s)", pid)
    with SESSIONS_LOCK:
        SESSIONS.pop(user_id, None)
    await update.message.reply_text(f"🛑 Stopped login terminal (pid={pid}) successfully.")

# ---------------- Flush command ----------------
async def flush(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    user_id = update.effective_user.id
    if not is_owner(user_id):
        await update.message.reply_text("⚠️ you are not an admin ⚠️")
        return
    global users_tasks, persistent_tasks
    stopped_count = 0
    failed_count = 0
    for uid, tasks in users_tasks.items():
        for task in tasks[:]:
            if not await asyncio.to_thread(_stop_task_processes, task):
                failed_count += 1
                continue
            if task.get('type') == 'message_attack' and 'names_file' in task:
                names_file = _project_path(task['names_file'])
                if _is_within_project(names_file) and os.path.exists(names_file):
                    os.remove(names_file)
            logging.info(f"{time.strftime('%Y-%m-%d %H:%M:%S')} Task stop user={uid} task={task['id']} by flush")
            mark_task_stopped_persistent(task['id'])
            tasks.remove(task)
            stopped_count += 1
        users_tasks[uid] = tasks
    await update.message.reply_text(
        f"🛑 Stopped {stopped_count} task(s) globally; {failed_count} could not be stopped. 🛑"
    )

PSID_SESSION, PSID_USERNAME = range(2)
USERNAME, PASSWORD = range(2)
PLO_USERNAME, PLO_PASSWORD = range(2)
SLOG_SESSION, SLOG_USERNAME = range(2)

async def start(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    await update.message.reply_text("Welcome to Spyther's spam bot ⚡ type /help to see available commands")

async def help_command(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    user_id = update.effective_user.id
    if not is_authorized(user_id):
        await update.message.reply_text("⚠️ You are not authorised to use, dm owner to gain access! @spyther ⚠️")
        return
    help_text = """
🌟 Available commands: 🌟
 /help ⚡ - Show this help
 /login 📱 - Login to Instagram account
 /plogin 🔐 - Browser login
 /slogin 🔑 - Login with session ID
 /psid 🗝️- Login with browser session ID
 /viewmyac 👀 - View your saved accounts
 /setig 🔄 <number> - Set default account
 /pair 📦 ig1-ig2 - Create account pair for rotation
 /unpair ✨ - to unpair paired accounts (unpair all or unpair <account>
 /switch ⏱️ <min> - Set switch interval (5+ min)
 /threads 🔢 <1-5> - Set number of threads
 /viewpref ⚙️ - View preferences
 /attack 💥 - Start sending messages
 /pattack 💥 - Start sending messages (manual thread URL)
 /stop 🛑 <pid/all> - Stop tasks
 /task 📋 - View ongoing tasks
 /logout 🚪 <username> - Logout and remove account
 /kill 🛑 - Kill active login session
 /usg 📊 - System usage
    """
    if is_owner(user_id):
        help_text += """
Admin commands: 👑
 /add ➕ <tg_id> - Add authorized user
 /remove ➖ <tg_id> - Remove authorized user
 /users 📜 - List authorized users
 /flush 🧹 - Stop all tasks globally
        """
    await update.message.reply_text(help_text)

async def psid_start(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    user_id = update.effective_user.id
    if not is_authorized(user_id):
        await update.message.reply_text("⚠️ Not authorized.")
        return ConversationHandler.END

    await update.message.reply_text("🔑 Enter your Instagram sessionid:")
    return PSID_SESSION
    
async def playwright_test_session(sessionid: str):
    async with async_playwright() as p:
        browser = None
        context = None
        try:
            browser = await launch_chromium(p, headless=True)
            context = await browser.new_context()
            await context.add_cookies([{
                "name": "sessionid",
                "value": sessionid,
                "domain": ".instagram.com",
                "path": "/",
                "httpOnly": True,
                "secure": True
            }])
            page = await context.new_page()
            await page.goto("https://www.instagram.com/")
            await page.wait_for_timeout(8000)

            success = await page.locator("text=Log in").count() == 0
            state = await context.storage_state()
            return success, state
        finally:
            try:
                if context is not None:
                    await context.close()
            finally:
                if browser is not None:
                    await browser.close()
    
async def psid_get_session(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    sessionid = update.message.text.strip()
    user_id = update.effective_user.id

    await update.message.reply_text("🔄 Testing session with Playwright...")

    try:
        success, state = await playwright_test_session(sessionid)
        if not success:
            await update.message.reply_text("❌ Login FAILED (invalid / checkpointed session)")
            return ConversationHandler.END

        context.user_data['psid_state'] = state
        context.user_data['psid_sessionid'] = sessionid
        await update.message.reply_text("✅ Login SUCCESS\nEnter username to save:")
        return PSID_USERNAME
    except BrowserLaunchError:
        await reply_error_safely(
            update,
            "❌ Browser setup failed on the server. Please ask the administrator to install Playwright's Linux dependencies.",
        )
        return ConversationHandler.END
    except Exception:
        log_exception_safely("[PSID] Session validation failed", sessionid)
        await reply_error_safely(update, "❌ Could not validate the session. Please try again later.")
        return ConversationHandler.END
        
async def psid_get_username(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    username = update.message.text.strip().lower()
    user_id = update.effective_user.id
    if not _is_valid_instagram_username(username):
        await update.message.reply_text("⚠️ Enter a valid Instagram username. ⚠️")
        return PSID_USERNAME

    state = context.user_data['psid_state']
    os.makedirs(os.path.join(PROJECT_DIR, "sessions"), mode=0o700, exist_ok=True)

    # Save Playwright
    pw_file = os.path.join(PROJECT_DIR, "sessions", f"{user_id}_{username}_state.json")
    if not isinstance(state, dict):
        raise ValueError("Invalid Playwright storage state received from session validation")
    _write_json_atomic(pw_file, state)

    # Save in bot memory
    if user_id not in users_data:
        users_data[user_id] = {'accounts': [], 'default': None, 'pairs': None, 'switch_minutes': 10, 'threads': 1}

    users_data[user_id]['accounts'].append({
        "ig_username": username,
        "password": "",
        "storage_state": state
    })
    users_data[user_id]['default'] = len(users_data[user_id]['accounts']) - 1
    save_user_data(user_id, users_data[user_id])
    context.user_data.pop('psid_sessionid', None)
    context.user_data.pop('psid_state', None)

    await update.message.reply_text(f"🎉 Session saved!\nUser: {username}\nPlaywright ready.")
    return ConversationHandler.END
    


async def login_start(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    user_id = update.effective_user.id
    if not is_authorized(user_id):
        await update.message.reply_text("⚠️ You are not authorised to use, dm owner to gain access! @spyther ⚠️")
        return ConversationHandler.END
    await update.message.reply_text("📱 Enter Instagram username: 📱")
    return USERNAME

async def get_username(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    # Normalize username: remove surrounding spaces and lowercase
    username = update.message.text.strip().lower()
    if not _is_valid_instagram_username(username):
        await update.message.reply_text("⚠️ Enter a valid Instagram username. ⚠️")
        return USERNAME
    context.user_data['ig_username'] = username
    await update.message.reply_text("🔒 Enter password: 🔒")
    return PASSWORD

async def get_password(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    user_id = update.effective_user.id
    chat_id = update.effective_chat.id
    username = context.user_data['ig_username']
    password = update.message.text.strip()
    
    with SESSIONS_LOCK:
        if user_id in SESSIONS:
            await update.message.reply_text("⚠️ PTY session already running. Use /kill first.")
            return ConversationHandler.END

    pid, master_fd = pty.fork()
    if pid == 0:
        try:
            child_login(user_id, username, password)
        except SystemExit:
            os._exit(0)
        except Exception:
            log_exception_safely("[LOGIN] Unexpected child-process failure", username, password)
            print("[CHILD] Login process failed. Check the server logs.")
            os._exit(1)
    else:
        t = threading.Thread(target=reader_thread, args=(user_id, chat_id, master_fd, username, password), daemon=True)
        t.start()
        with SESSIONS_LOCK:
            SESSIONS[user_id] = {"pid": pid, "master_fd": master_fd, "thread": t, "username": username, "password": password, "chat_id": chat_id}
        
    return ConversationHandler.END

# --- /plogin handlers (ASYNC, NO THREAD) ---
async def plogin_start(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    user_id = update.effective_user.id
    if not is_authorized(user_id):
        await update.message.reply_text("⚠️ You are not authorised to use, dm owner to gain access! @spyther ⚠️")
        return ConversationHandler.END

    await update.message.reply_text("🔐 Enter Instagram username for Playwright login: ")
    return PLO_USERNAME


async def plogin_get_username(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    username = update.message.text.strip().lower()
    if not _is_valid_instagram_username(username):
        await update.message.reply_text("⚠️ Enter a valid Instagram username. ⚠️")
        return PLO_USERNAME
    context.user_data['pl_username'] = username
    await update.message.reply_text("🔒 Enter password: 🔒")
    return PLO_PASSWORD


async def plogin_get_password(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    user_id = update.effective_user.id
    chat_id = update.effective_chat.id
    username = context.user_data['pl_username']
    password = update.message.text.strip()

    await update.message.reply_text("🔄 Starting Playwright login... (async, no threads)")

    try:
        # 1) Playwright se login + storage_state save
        state_file = await playwright_login_and_save_state(username, password, user_id)

        # 2) JSON state load karke Instagrapi me convert karo (tumhara purana logic reuse)
        logging.info("[PLOGIN] Loading storage_state from %s", state_file)
        state = _read_json_file(state_file)
        if not isinstance(state, dict):
            raise ValueError(f"Invalid Playwright storage state: {state_file}")

        cookies = [c for c in state.get('cookies', []) if c.get('domain') == '.instagram.com']
        logging.info("[PLOGIN] cookies for .instagram.com = %s", len(cookies))

        # Extract sessionid cookie (Playwright → Instagrapi)
        sessionid = None
        for c in cookies:
            if c.get("name") == "sessionid":
                sessionid = c.get("value")
                break

        if not sessionid:
            logging.error("[PLOGIN] sessionid cookie not found in storage_state")
            raise ValueError("ERROR_011: sessionid cookie not found – cannot init Instagrapi client")

        cl = Client()
        logging.info("[PLOGIN] Logging into Instagrapi using sessionid (len=%s)", len(sessionid))

        # Instagrapi new valid method
        cl.login_by_sessionid(sessionid)

        session_file = os.path.join(PROJECT_DIR, "sessions", f"{user_id}_{username}_session.json")
        logging.info("[PLOGIN] Dumping Instagrapi settings to %s", session_file)
        cl.dump_settings(session_file)

        # 3) users_data update (same tumhara code)
        logging.info("[PLOGIN] Updating users_data for user_id=%s", user_id)
        if user_id not in users_data:
            users_data[user_id] = {
                'accounts': [],
                'default': None,
                'pairs': None,
                'switch_minutes': 10,
                'threads': 1,
            }
            save_user_data(user_id, users_data[user_id])

        data = users_data[user_id]
        found = False
        for i, acc in enumerate(data['accounts']):
            if acc.get('ig_username', '').strip().lower() == username:
                acc['password'] = password
                acc['storage_state'] = state
                data['default'] = i
                found = True
                logging.info("[PLOGIN] Updated existing account index=%s", i)
                break

        if not found:
            data['accounts'].append({
                'ig_username': username,
                'password': password,
                'storage_state': state,
            })
            data['default'] = len(data['accounts']) - 1
            logging.info("[PLOGIN] Added new account, total=%s", len(data['accounts']))

        save_user_data(user_id, data)

        await update.message.reply_text("✅ Playwright login successful! Sessions saved. 🎉")

    except ValueError:
        log_exception_safely("[PLOGIN] Login validation failed", username, password)
        await reply_error_safely(
            update,
            "❌ Login failed. Check the credentials and complete any required challenge or 2FA.",
        )

    except Exception:
        log_exception_safely("[PLOGIN] Unexpected browser or server error", username, password)
        await reply_error_safely(
            update,
            "❌ Login failed because of a browser or server error. Please try again later.",
        )

    return ConversationHandler.END

# --- /slogin handlers ---
async def slogin_start(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    user_id = update.effective_user.id
    if not is_authorized(user_id):
        await update.message.reply_text("⚠️ You are not authorised to use, dm owner to gain access! @spyther ⚠️")
        return ConversationHandler.END
    await update.message.reply_text("🔑 Enter session ID: ")
    return SLOG_SESSION

async def slogin_get_session(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    sessionid = update.message.text.strip()
    user_id = update.effective_user.id
    temp_file = os.path.join(PROJECT_DIR, f"temp_session_{user_id}_{int(time.time())}.json")
    cl = Client()
    try:
        cl.login_by_sessionid(sessionid)
        cl.dump_settings(temp_file)
        context.user_data['temp_session_file'] = temp_file
        await update.message.reply_text("✅ Valid session ID! 📝 Enter username to save:")
        return SLOG_USERNAME
    except LoginRequired:
        os.remove(temp_file) if os.path.exists(temp_file) else None
        await update.message.reply_text("❌ Invalid session ID.")
        return ConversationHandler.END
    except Exception:
        os.remove(temp_file) if os.path.exists(temp_file) else None
        log_exception_safely("[SLOGIN] Session validation failed", sessionid)
        await reply_error_safely(update, "❌ Could not validate the session. Please try again later.")
        return ConversationHandler.END

async def slogin_get_username(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    username = update.message.text.strip().lower()
    user_id = update.effective_user.id
    if not _is_valid_instagram_username(username):
        await update.message.reply_text("⚠️ Enter a valid Instagram username. ⚠️")
        return SLOG_USERNAME
    temp_file = context.user_data['temp_session_file']
    session_file = os.path.join(PROJECT_DIR, "sessions", f"{user_id}_{username}_session.json")
    os.makedirs(os.path.join(PROJECT_DIR, "sessions"), mode=0o700, exist_ok=True)
    os.rename(temp_file, session_file)

    # Generate playwright state
    settings = _read_json_file(session_file)
    if not isinstance(settings, dict):
        raise ValueError(f"Invalid instagrapi settings file: {session_file}")
    state = get_storage_state_from_instagrapi(settings)
    playwright_file = os.path.join(PROJECT_DIR, "sessions", f"{user_id}_{username}_state.json")
    _write_json_atomic(playwright_file, state)

    # Save to user data
    if user_id not in users_data:
        users_data[user_id] = {'accounts': [], 'default': None, 'pairs': None, 'switch_minutes': 10, 'threads': 1}
        save_user_data(user_id, users_data[user_id])
    data = users_data[user_id]
    found = False
    for i, acc in enumerate(data['accounts']):
        if acc.get('ig_username', '').strip().lower() == username:
            acc['password'] = ''  # No password for session
            acc['storage_state'] = state
            data['default'] = i
            found = True
            break
    if not found:
        data['accounts'].append({'ig_username': username, 'password': '', 'storage_state': state})
        data['default'] = len(data['accounts']) - 1
    save_user_data(user_id, data)

    await update.message.reply_text(f"✅ Session saved for {username}! Playwright & Instagrapi files created. 🎉")
    return ConversationHandler.END

async def viewmyac(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    user_id = update.effective_user.id
    if not is_authorized(user_id):
        await update.message.reply_text("⚠️ You are not authorised to use, dm owner to gain access! @spyther ⚠️")
        return
    if user_id not in users_data:
        await update.message.reply_text("❌ You haven't saved any account. Use /login to save one. ❌")
        return
    data = users_data[user_id]
    msg = "👀 Your saved account list 👀\n"
    for i, acc in enumerate(data['accounts']):
        default = " (default) ⭐" if data['default'] == i else ""
        msg += f"{i+1}. {acc['ig_username']}{default}\n"
    await update.message.reply_text(msg)

async def setig(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    user_id = update.effective_user.id
    if not is_authorized(user_id):
        await update.message.reply_text("⚠️ You are not authorised to use, dm owner to gain access! @spyther ⚠️")
        return
    if not context.args or not context.args[0].isdigit():
        await update.message.reply_text("❗ Usage: /setig <number> ❗")
        return
    num = int(context.args[0]) - 1
    if user_id not in users_data:
        await update.message.reply_text("❌ No accounts saved. ❌")
        return
    data = users_data[user_id]
    if num < 0 or num >= len(data['accounts']):
        await update.message.reply_text("⚠️ Invalid number. ⚠️")
        return
    data['default'] = num
    save_user_data(user_id, data)
    acc = data['accounts'][num]['ig_username']
    await update.message.reply_text(f"✅ {num+1}. {acc} now is your default account. ⭐")

async def logout_command(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    user_id = update.effective_user.id
    if not is_authorized(user_id):
        await update.message.reply_text("⚠️ You are not authorised to use, dm owner to gain access! @spyther ⚠️")
        return
    if not context.args:
        await update.message.reply_text("❗ Usage: /logout <username> ❗")
        return
    username = context.args[0].strip().lower()
    if not _is_valid_instagram_username(username):
        await update.message.reply_text("⚠️ Invalid Instagram username. ⚠️")
        return
    if user_id not in users_data:
        await update.message.reply_text("❌ No accounts saved. ❌")
        return
    data = users_data[user_id]
    for i, acc in enumerate(data['accounts']):
        if acc['ig_username'] == username:
            del data['accounts'][i]
            if data['default'] == i:
                data['default'] = 0 if data['accounts'] else None
            elif data['default'] > i:
                data['default'] -= 1
            # Update pairs if exists
            if data['pairs']:
                pl = data['pairs']['list']
                if username in pl:
                    pl.remove(username)
                    if not pl:
                        data['pairs'] = None
                    else:
                        data['pairs']['default_index'] = 0
            break
    else:
        await update.message.reply_text("⚠️ Account not found. ⚠️")
        return
    save_user_data(user_id, data)
    session_file = os.path.join(PROJECT_DIR, "sessions", f"{user_id}_{username}_session.json")
    state_file = os.path.join(PROJECT_DIR, "sessions", f"{user_id}_{username}_state.json")
    if os.path.exists(session_file):
        os.remove(session_file)
    if os.path.exists(state_file):
        os.remove(state_file)
    await update.message.reply_text(f"✅ Logged out and removed {username}. Files deleted. ✅")

# New commands
async def pair_command(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    user_id = update.effective_user.id
    if not is_authorized(user_id):
        await update.message.reply_text("⚠️ You are not authorised to use, dm owner to gain access! @spyther⚠️")
        return
    if not context.args:
        await update.message.reply_text("❗ Usage: /pair iguser1-iguser2-iguser3 ❗")
        return
    arg_str = '-'.join(context.args)
    us = [u.strip() for u in arg_str.split('-') if u.strip()]
    if len(us) < 2:
        await update.message.reply_text("❗ Provide at least one more account. ❗")
        return
    if user_id not in users_data or not users_data[user_id]['accounts']:
        await update.message.reply_text("❌ No accounts saved. Use /login first. ❌")
        return
    data = users_data[user_id]
    accounts_set = {acc['ig_username'] for acc in data['accounts']}
    missing = [u for u in us if u not in accounts_set]
    if missing:
        await update.message.reply_text(f"⚠️ Can't find that account: {missing[0]}. Save it again with /login. ⚠️")
        return
    data['pairs'] = {'list': us, 'default_index': 0}
    # Set default to first in pair
    first_u = us[0]
    for i, acc in enumerate(data['accounts']):
        if acc['ig_username'] == first_u:
            data['default'] = i
            break
    save_user_data(user_id, data)
    await update.message.reply_text(f"✅ Pair created! {len(us)} accounts saved.\nDefault: {first_u} ⭐\nUse /attack to start sending messages with pairing & switching.")

async def unpair_command(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    user_id = update.effective_user.id
    if not is_authorized(user_id):
        await update.message.reply_text("⚠️ You are not authorised to use, dm owner to gain access! @spyther ⚠️")
        return

    if user_id not in users_data or not users_data[user_id].get('pairs'):
        await update.message.reply_text("❌ No active pair found. Use /pair first. ❌")
        return

    data = users_data[user_id]
    pair_info = data['pairs']
    pair_list = pair_info['list']

    # --- no arguments case ---
    if not context.args:
        msg = "👥 Current pair list:\n"
        for i, u in enumerate(pair_list, 1):
            mark = "⭐" if i - 1 == pair_info.get('default_index', 0) else ""
            msg += f"{i}. {u} {mark}\n"
        msg += "\nUse `/unpair all` to remove all pairs or `/unpair <username>` to remove one."
        await update.message.reply_text(msg)
        return

    arg = context.args[0].strip().lower()

    # --- unpair all ---
    if arg == "all":
        data['pairs'] = None
        save_user_data(user_id, data)
        await update.message.reply_text("🧹 All paired accounts removed successfully.")
        return

    # --- unpair specific account ---
    target = arg
    if target not in pair_list:
        await update.message.reply_text(f"⚠️ {target} is not in current pair list. ⚠️")
        return

    pair_list.remove(target)
    if not pair_list:
        data['pairs'] = None
        msg = f"✅ Removed {target}. No pairs left."
    else:
        # adjust default index if needed
        if pair_info.get('default_index', 0) >= len(pair_list):
            pair_info['default_index'] = 0
        msg = f"✅ Removed {target}. Remaining pairs: {', '.join(pair_list)}"

    save_user_data(user_id, data)
    await update.message.reply_text(msg)

async def switch_command(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    user_id = update.effective_user.id
    if not is_authorized(user_id):
        await update.message.reply_text("⚠️ You are not authorised to use, dm owner to gain access! @spyther ⚠️")
        return
    if not context.args or not context.args[0].isdigit():
        await update.message.reply_text("❗ Usage: /switch <minutes> ❗")
        return
    min_ = int(context.args[0])
    data = users_data.get(user_id)
    if not isinstance(data, dict):
        await update.message.reply_text("❌ No account preferences found. Use /login first. ❌")
        return
    if not data.get('pairs') or len(data['pairs']['list']) < 2:
        await update.message.reply_text("⚠️ No pair found. Use /pair first. ⚠️")
        return
    if min_ < 5:
        await update.message.reply_text("⚠️ Minimum switch interval is 5 minutes. ⚠️")
        return
    data['switch_minutes'] = min_
    save_user_data(user_id, data)
    await update.message.reply_text(f"⏱️ Switch interval set to {min_} minutes.")

async def threads_command(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    user_id = update.effective_user.id
    if not is_authorized(user_id):
        await update.message.reply_text("⚠️ You are not authorised to use, dm owner to gain access! @spyther ⚠️")
        return
    if not context.args or not context.args[0].isdigit():
        await update.message.reply_text("❗ Usage: /threads <1-5> ❗")
        return
    n = int(context.args[0])
    if n < 1 or n > 5:
        await update.message.reply_text("⚠️ threads must be between 1 and 5. ⚠️")
        return
    if user_id not in users_data:
        users_data[user_id] = {'accounts': [], 'default': None, 'pairs': None, 'switch_minutes': 10, 'threads': 1}
        save_user_data(user_id, users_data[user_id])
    data = users_data[user_id]
    data['threads'] = n
    save_user_data(user_id, data)
    await update.message.reply_text(f"🔁 Threads set to {n}.")

async def viewpref(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    user_id = update.effective_user.id
    if not is_authorized(user_id):
        await update.message.reply_text("⚠️ You are not authorised to use, dm owner to gain access! @spyther ⚠️")
        return
    if user_id not in users_data:
        await update.message.reply_text("❌ No data. Use /login. ❌")
        return
    data = users_data[user_id]
    saved_accounts = ', '.join([acc['ig_username'] for acc in data['accounts']])
    msg = "🔧 Your bot preferences:\n"
    if data.get('pairs'):
        pl = data['pairs']['list']
        msg += f"Pairs: yes — {len(pl)} accounts\n"
        default_idx = data['pairs']['default_index']
        default_u = pl[default_idx]
        msg += f"Default: {default_u} ⭐\n"
    else:
        msg += "Pairs: no\n"
    switch_min = data.get('switch_minutes', 10)
    msg += f"⏱️ Switch interval: {switch_min} minutes\n"
    threads = data.get('threads', 1)
    msg += f"🧵 Threads: {threads}\n"
    msg += f"👤 Saved accounts: {saved_accounts}\n"
    # Check running attacks
    tasks = users_tasks.get(user_id, [])
    running_attacks = [t for t in tasks if t.get('type') == 'message_attack' and t['status'] == 'running' and t['proc'].poll() is None]
    if running_attacks:
        task = running_attacks[0]  # Assume one
        pid = task['pid']
        ttype = task['target_type']
        tdisplay = task['target_display']
        disp = f"dm -> @{tdisplay}" if ttype == 'dm' else tdisplay
        msg += f"\nActive attack PID {pid} ({disp})\n"
        msg += "Spamming...!\n"
        pair_list = task['pair_list']
        curr_idx = task['pair_index']
        curr_u = pair_list[curr_idx]
        for u in pair_list:
            if u == curr_u:
                msg += f"using - {u}\n"
            else:
                msg += f"cooldown - {u}\n"
    await update.message.reply_text(msg)

MODE, SELECT_GC, TARGET, MESSAGES = range(4)
P_MODE, P_TARGET_DISPLAY, P_THREAD_URL, P_MESSAGES = range(4)

async def attack_start(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    user_id = update.effective_user.id
    if not is_authorized(user_id):
        await update.message.reply_text("⚠️ You are not authorised to use, dm owner to gain access! @spyther ⚠️")
        return ConversationHandler.END
    if user_id not in users_data or not users_data[user_id]['accounts']:
        await update.message.reply_text("❗ Please /login first. ❗")
        return ConversationHandler.END
    data = users_data[user_id]
    if data['default'] is None:
        data['default'] = 0
        save_user_data(user_id, data)
    await update.message.reply_text("Where you want to send msgs ? dm or gc")
    return MODE

async def get_mode(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    user_id = update.effective_user.id
    text = update.message.text.lower().strip()
    data = users_data[user_id]

    if 'dm' in text:
        context.user_data['mode'] = 'dm'
        await update.message.reply_text("Enter target username (for DM):")
        return TARGET

    elif 'gc' in text:
        acc = data['accounts'][data['default']]
        fetch_msg = await update.message.reply_text("🔍 Fetching last 10 GC threads...")

        user_fetching.add(user_id)
        try:
            groups, new_state = await asyncio.to_thread(
                list_group_chats,
                user_id,
                acc['storage_state'],
                acc['ig_username'],
                acc['password'],
                max_groups=10,
                amount=10
            )
        finally:
            user_fetching.discard(user_id)
            try:
                await fetch_msg.delete()
            except:
                pass

        # ✅ Agar beech me /cancel aaya tha to result ignore karo
        if user_id in user_cancel_fetch:
            user_cancel_fetch.discard(user_id)
            await update.message.reply_text("❌ Fetching cancelled. Ignoring result. ❌")
            return ConversationHandler.END

        if new_state != acc['storage_state']:
            acc['storage_state'] = new_state
            save_user_data(user_id, data)

        context.user_data['groups'] = groups
        context.user_data['mode'] = 'gc'

        if not groups:
            await update.message.reply_text("❌ No group chats found. ❌")
            return ConversationHandler.END

        msg = "🔢 Select a GC by number: 🔢\n"
        for i, g in enumerate(groups):
            msg += f"{i+1}. {g['display']}\n"

        await update.message.reply_text(msg)
        return SELECT_GC

    else:
        await update.message.reply_text("Please reply with 'dm' or 'gc'")
        return MODE

async def select_gc_handler(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    user_id = update.effective_user.id
    text = update.message.text.strip()
    try:
        num = int(text) - 1
        groups = context.user_data['groups']
        if 0 <= num < len(groups):
            g = groups[num]
            context.user_data['thread_url'] = g['url']
            context.user_data['target_display'] = g['display']
            await update.message.reply_text("Send messages like: msg1 & msg2 & msg3 or upload .txt file")
            return MESSAGES
        else:
            await update.message.reply_text("⚠️ Invalid number. Please select 1-{}. ⚠️".format(len(groups)))
            return SELECT_GC
    except ValueError:
        await update.message.reply_text("⚠️ Please send a number. ⚠️")
        return SELECT_GC

async def get_target_handler(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    user_id = update.effective_user.id
    target_u = update.message.text.strip().lstrip('@')
    if not _is_valid_instagram_username(target_u):
        await update.message.reply_text("⚠️ Invalid Instagram username. ⚠️")
        return TARGET
    target_u = target_u.lower()
    context.user_data['target_display'] = target_u
    data = users_data[user_id]
    acc = data['accounts'][data['default']]
    thread_url = await asyncio.to_thread(
        get_dm_thread_url, user_id, acc['ig_username'], acc['password'], target_u
    )
    if not thread_url:
        await update.message.reply_text("❌ Could not lock thread id with default account.")
        return ConversationHandler.END
    context.user_data['thread_url'] = thread_url
    await update.message.reply_text("Send messages like: msg1 & msg2 & msg3 or upload .txt file")
    return MESSAGES
    
async def get_messages_file(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    user_id = update.effective_user.id
    document = update.message.document

    if not document:
        await update.message.reply_text("❌ Please upload a .txt file.")
        return ConversationHandler.END

    file = await document.get_file()

    randomid = str(uuid.uuid4())[:8]
    names_file = os.path.join(PROJECT_DIR, f"{user_id}_{randomid}.txt")

    # Save uploaded .txt file
    try:
        await file.download_to_drive(names_file)
    except Exception:
        log_exception_safely("[MESSAGES] Could not download uploaded message file")
        if os.path.exists(names_file):
            os.remove(names_file)
        await reply_error_safely(update, "❌ Could not save the uploaded message file.")
        return ConversationHandler.END

    # store file path in context so get_messages can use it
    context.user_data['uploaded_names_file'] = names_file

    # Reuse same logic as text handler
    return await get_messages(update, context)

async def get_messages(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    user_id = update.effective_user.id

    # Check if we came from file upload handler
    uploaded_file = context.user_data.pop('uploaded_names_file', None)

    if uploaded_file and os.path.exists(uploaded_file):
        # Use already saved .txt file from upload
        names_file = uploaded_file
        raw_text = f"[USING_UPLOADED_FILE:{os.path.basename(uploaded_file)}]"
        logging.debug("USING UPLOADED FILE: %r", uploaded_file)
    else:
        # Normal text input flow
        raw_text = (update.message.text or "").strip()
        logging.debug("Received message input (%d characters)", len(raw_text))

        # Normalize to handle fullwidth & etc.
        text = unicodedata.normalize("NFKC", raw_text)

        # Always make a temp file
        randomid = str(uuid.uuid4())[:8]
        names_file = os.path.join(PROJECT_DIR, f"{user_id}_{randomid}.txt")

        # Write raw text directly so the message worker handles separators correctly.
        try:
            with open(names_file, 'w', encoding='utf-8') as f:
                f.write(text)
        except Exception:
            log_exception_safely("[MESSAGES] Failed to create the input file")
            await reply_error_safely(update, "❌ Could not save the input. Please try again.")
            return ConversationHandler.END

    data = users_data[user_id]
    pairs = data.get('pairs')
    pair_list = pairs['list'] if pairs else [data['accounts'][data['default']]['ig_username']]
    if len(pair_list) == 1:
        warning = "⚠️ Warning: You may get chat ban if you use a single account too long. Use /pair to make multi-account rotation.\n\n"
    else:
        warning = ""
    switch_minutes = data.get('switch_minutes', 10)
    threads_n = data.get('threads', 1)
    tasks = users_tasks.get(user_id, [])
    running_msg = [t for t in tasks if t.get('type') == 'message_attack' and t['status'] == 'running' and t['proc'].poll() is None]
    if len(running_msg) >= 5:
        await update.message.reply_text("⚠️ Max 5 message attacks running. Stop one first. ⚠️")
        if os.path.exists(names_file):
            os.remove(names_file)
        return ConversationHandler.END

    thread_url = context.user_data['thread_url']
    target_display = context.user_data['target_display']
    target_mode = context.user_data['mode']
    start_idx = pairs['default_index'] if pairs else 0
    start_u = pair_list[start_idx]
    start_acc = next(acc for acc in data['accounts'] if acc['ig_username'] == start_u)
    start_pass = start_acc['password']
    start_u = start_u.strip().lower()
    state_file = os.path.join(PROJECT_DIR, "sessions", f"{user_id}_{start_u}_state.json")
    if not os.path.exists(state_file):
        _write_json_atomic(state_file, start_acc['storage_state'])

    cmd = [
        sys.executable, os.path.join(PROJECT_DIR, "msg.py"),
        "--thread-url", thread_url,
        "--names", _project_path(names_file),
        "--tabs", str(threads_n),
        "--headless", "true",
        "--storage-state", _project_path(state_file)
    ]
    try:
        proc = _launch_message_process(cmd, start_u, start_pass)
    except Exception:
        log_exception_safely("[PROCESS] Failed to start the message worker", start_pass)
        if os.path.exists(names_file):
            os.remove(names_file)
        await reply_error_safely(update, "❌ Could not start the browser task. Check the server logs and try again.")
        return ConversationHandler.END
    running_processes[proc.pid] = proc
    pid = proc.pid
    task_id = str(uuid.uuid4())
    task = {
        "id": task_id,
        "user_id": user_id,
        "type": "message_attack",
        "pair_list": pair_list,
        "pair_index": start_idx,
        "switch_minutes": switch_minutes,
        "threads": threads_n,
        "names_file": names_file,
        "target_thread_url": thread_url,
        "target_type": target_mode,
        "target_display": target_display,
        "last_switch_time": time.time(),
        "status": "running",
        "cmd": cmd,
        "pid": pid,
        "display_pid": pid,
        "proc_list": [pid],
        "proc": proc,
        "start_time": time.time(),
        "process_started_at": time.time(),
    }
    persistent_tasks.append(task)
    save_persistent_tasks()
    tasks.append(task)
    users_tasks[user_id] = tasks
    logging.info(f"{time.strftime('%Y-%m-%d %H:%M:%S')} Message attack start user={user_id} task={task_id} target={target_display} pid={pid}")

    status = "Spamming...!\n"
    curr_u = pair_list[task['pair_index']]
    for u in pair_list:
        if u == curr_u:
            status += f"using - {u}\n"
        else:
            status += f"cooldown - {u}\n"
    status += f"To stop 🛑 type /stop {task['display_pid']} or /stop all to stop all processes."

    sent_msg = await update.message.reply_text(warning + status)
    task['status_chat_id'] = update.message.chat_id
    task['status_msg_id'] = sent_msg.message_id
    return ConversationHandler.END

async def pattack_start(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    user_id = update.effective_user.id
    if not is_authorized(user_id):
        await update.message.reply_text("⚠️ You are not authorised to use, dm owner to gain access! @spyther ⚠️")
        return ConversationHandler.END
    if user_id not in users_data or not users_data[user_id]['accounts']:
        await update.message.reply_text("❗ Please /login first. ❗")
        return ConversationHandler.END
    data = users_data[user_id]
    if data['default'] is None:
        data['default'] = 0
        save_user_data(user_id, data)
    await update.message.reply_text("Where do you want to send messages? dm or gc")
    return P_MODE

async def p_get_mode(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    text = update.message.text.lower().strip()

    if 'dm' in text:
        context.user_data['mode'] = 'dm'
        await update.message.reply_text("Enter target username (for display):")
        return P_TARGET_DISPLAY

    elif 'gc' in text:
        context.user_data['mode'] = 'gc'
        await update.message.reply_text("Enter group name (for display):")
        return P_TARGET_DISPLAY

    else:
        await update.message.reply_text("Please reply with 'dm' or 'gc'")
        return P_MODE

async def p_get_target_display(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    target_display = update.message.text.strip()
    if not target_display:
        await update.message.reply_text("⚠️ Invalid input. ⚠️")
        return P_TARGET_DISPLAY
    context.user_data['target_display'] = target_display
    if context.user_data['mode'] == 'dm':
        await update.message.reply_text("Enter username thread url:")
    else:
        await update.message.reply_text("Enter gc thread url:")
    return P_THREAD_URL

async def p_get_thread_url(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    thread_url = update.message.text.strip()
    parsed_url = urllib.parse.urlparse(thread_url)
    if (
        parsed_url.scheme != "https"
        or parsed_url.netloc != "www.instagram.com"
        or not parsed_url.path.startswith("/direct/t/")
        or not parsed_url.path.removeprefix("/direct/t/").strip("/")
    ):
        await update.message.reply_text("⚠️ Invalid thread URL. It should be like https://www.instagram.com/direct/t/{id}/ ⚠️")
        return P_THREAD_URL
    context.user_data['thread_url'] = thread_url
    await update.message.reply_text("Send messages like: msg1 & msg2 & msg3 or upload .txt file")
    return P_MESSAGES

async def p_get_messages_file(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    document = update.message.document
    if document is None:
        await update.message.reply_text("❌ Please upload a .txt file.")
        return ConversationHandler.END
    uploaded_file = await document.get_file()
    names_file = os.path.join(
        PROJECT_DIR,
        f"{update.effective_user.id}_{uuid.uuid4().hex[:8]}.txt",
    )
    try:
        await uploaded_file.download_to_drive(names_file)
    except Exception:
        log_exception_safely("[PATTACK] Could not download message file")
        if os.path.exists(names_file):
            os.remove(names_file)
        await reply_error_safely(update, "❌ Could not save the uploaded message file.")
        return ConversationHandler.END
    context.user_data["uploaded_names_file"] = names_file
    return await get_messages(update, context)

async def p_get_messages(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    return await get_messages(update, context)

def load_persistent_tasks() -> bool:
    global persistent_tasks
    if os.path.exists(TASKS_FILE):
        try:
            with open(TASKS_FILE, 'r', encoding='utf-8') as f:
                loaded_tasks = json.load(f)
        except (OSError, UnicodeError, json.JSONDecodeError):
            log_exception_safely("[TASKS] Could not load persistent task data")
            persistent_tasks = []
            return False
        if not isinstance(loaded_tasks, list):
            logging.error("[TASKS] Persistent task data must be a list; ignoring it")
            persistent_tasks = []
            return False
        invalid_count = sum(
            not isinstance(task, dict)
            or not isinstance(task.get("id"), str)
            or not task.get("id")
            or task.get("type") != "message_attack"
            or task.get("status") not in ("running", "stopped", "completed")
            for task in loaded_tasks
        )
        if invalid_count:
            logging.warning("[TASKS] Ignoring %d malformed or unsupported task record(s)", invalid_count)
        persistent_tasks = [
            task for task in loaded_tasks
            if isinstance(task, dict)
            and isinstance(task.get("id"), str)
            and bool(task.get("id"))
            and task.get("type") == "message_attack"
            and task.get("status") in ("running", "stopped", "completed")
        ]
    else:
        persistent_tasks = []
    return True

def save_persistent_tasks():
    """
    Safely write persistent_tasks to TASKS_FILE.
    Removes runtime-only values (like 'proc') and ensures JSON-safe data.
    """
    safe_list = []
    for t in persistent_tasks:
        cleaned = {}
        for k, v in t.items():
            if k == 'proc':
                continue
            if isinstance(v, (int, float, str, bool, dict, list, type(None))):
                cleaned[k] = v
            else:
                try:
                    json.dumps(v)
                    cleaned[k] = v
                except Exception:
                    cleaned[k] = str(v)
        safe_list.append(cleaned)

    _write_json_atomic(TASKS_FILE, safe_list)

def mark_task_stopped_persistent(task_id: str):
    global persistent_tasks
    for task in persistent_tasks:
        if task.get('id') == task_id:
            task['status'] = 'stopped'
            save_persistent_tasks()
            break

def update_task_pid_persistent(task_id: str, new_pid: int, runtime_task: Dict | None = None):
    global persistent_tasks
    for task in persistent_tasks:
        if task.get('id') == task_id:
            task['pid'] = new_pid
            if runtime_task is not None:
                for key in (
                    "process_started_at",
                    "proc_list",
                    "pair_index",
                    "pair_list",
                    "last_switch_time",
                    "status_chat_id",
                    "status_msg_id",
                ):
                    if key in runtime_task:
                        task[key] = runtime_task[key]
            save_persistent_tasks()
            break

def mark_task_completed_persistent(task_id: str):
    global persistent_tasks
    for task in persistent_tasks:
        if task.get('id') == task_id:
            task['status'] = 'completed'
            save_persistent_tasks()
            break

def restore_tasks_on_start():
    if not load_persistent_tasks():
        print("⚠️ Task restoration skipped because persistent task data is invalid.")
        return
    running_tasks = [
        task for task in persistent_tasks
        if task.get('type') == 'message_attack' and task.get('status') == 'running'
    ]
    print(f"🔄 Restoring {len(running_tasks)} running message attacks...")
    for task in persistent_tasks[:]:
        if task.get('type') == 'message_attack' and task.get('status') == 'running':
            pair_list = task.get('pair_list')
            pair_index = task.get('pair_index')
            old_pid = task.get('pid')
            user_id = task.get('user_id')
            required_strings = (
                task.get('id'),
                task.get('names_file'),
                task.get('target_thread_url'),
                task.get('target_display'),
            )
            names_file = _project_path(task["names_file"]) if isinstance(task.get("names_file"), str) else ""
            if (
                not all(isinstance(value, str) and value for value in required_strings)
                or not _is_within_project(names_file)
                or not names_file.lower().endswith(".txt")
                or not task['target_thread_url'].startswith("https://www.instagram.com/direct/t/")
                or isinstance(old_pid, bool)
                or not isinstance(old_pid, int)
                or old_pid <= 1
                or isinstance(user_id, bool)
                or not isinstance(user_id, int)
                or not isinstance(pair_list, list)
                or not pair_list
                or not all(isinstance(username, str) and username for username in pair_list)
                or isinstance(pair_index, bool)
                or not isinstance(pair_index, int)
                or not 0 <= pair_index < len(pair_list)
                or task.get('target_type') not in ('dm', 'gc')
                or isinstance(task.get('switch_minutes'), bool)
                or not isinstance(task.get('switch_minutes'), int)
                or task['switch_minutes'] < 5
                or not _is_finite_number(task.get('last_switch_time'))
                or isinstance(task.get('threads'), bool)
                or not isinstance(task.get('threads'), int)
                or not 1 <= task['threads'] <= 5
            ):
                task['status'] = 'stopped'
                logging.warning("[TASKS] Stopped a running task with invalid or missing fields")
                continue

            task["names_file"] = names_file
            if not _stop_persisted_message_process(task):
                mark_task_stopped_persistent(task["id"])
                continue
            data = users_data.get(user_id)
            if not isinstance(data, dict) or not isinstance(data.get('accounts'), list):
                mark_task_stopped_persistent(task['id'])
                continue
            curr_idx = pair_index
            curr_u = pair_list[curr_idx]
            curr_acc = None
            for acc in data['accounts']:
                if isinstance(acc, dict) and acc.get('ig_username') == curr_u:
                    curr_acc = acc
                    break
            if (
                not curr_acc
                or not isinstance(curr_acc.get('password'), str)
                or not isinstance(curr_acc.get('storage_state', {}), dict)
            ):
                mark_task_stopped_persistent(task['id'])
                continue
            curr_pass = curr_acc['password']
            curr_u = curr_u.strip().lower()
            state_file = os.path.join(PROJECT_DIR, "sessions", f"{user_id}_{curr_u}_state.json")
            if not os.path.exists(state_file):
                _write_json_atomic(state_file, curr_acc.get('storage_state', {}))
            if not os.path.exists(names_file):
                # Recreate if missing? But skip for now
                mark_task_stopped_persistent(task['id'])
                continue
            cmd = [
                sys.executable, os.path.join(PROJECT_DIR, "msg.py"),
                "--thread-url", task['target_thread_url'],
                "--names", _project_path(names_file),
                "--tabs", str(task['threads']),
                "--headless", "true",
                "--storage-state", _project_path(state_file)
            ]
            try:
                proc = _launch_message_process(cmd, curr_u, curr_pass)
                # Register runtime map
                running_processes[proc.pid] = proc
                new_pid = proc.pid
                task['process_started_at'] = time.time()
                task['pid'] = new_pid
                task['proc_list'] = [new_pid]
                task['display_pid'] = task.get('display_pid', new_pid)
                update_task_pid_persistent(task['id'], new_pid, task)
                mem_task = task.copy()
                mem_task['proc'] = proc
                mem_task['proc_list'] = [proc.pid]
                if user_id not in users_tasks:
                    users_tasks[user_id] = []
                users_tasks[user_id].append(mem_task)
                print(f"✅ Restored message attack {task['id']} for {task['target_display']} | New PID: {new_pid}")
            except Exception:
                log_exception_safely(
                    f"Failed to restore message task {task['id']}",
                    curr_pass,
                )
                mark_task_stopped_persistent(task['id'])
    save_persistent_tasks()
    print("✅ Task restoration complete!")

async def send_resume_notification(user_id: int, task: Dict):
    ttype = task['target_type']
    tdisplay = task['target_display']
    disp = f"dm -> @{tdisplay}" if ttype == 'dm' else tdisplay
    msg = f"🔄 Attack auto resumed! New PID: {task['pid']} ({disp})\n"
    pair_list = task['pair_list']
    curr_idx = task['pair_index']
    curr_u = pair_list[curr_idx]
    for u in pair_list:
        if u == curr_u:
            msg += f"using - {u}\n"
        else:
            msg += f"cooldown - {u}\n"
    await APP.bot.send_message(chat_id=user_id, text=msg)

def get_switch_update(task: Dict) -> str:
    pair_list = task['pair_list']
    curr_idx = task['pair_index']
    curr_u = pair_list[curr_idx]
    lines = []
    for u in pair_list:
        if u == curr_u:
            lines.append(f"using - {u}")
        else:
            lines.append(f"cooldown - {u}")
    return '\n'.join(lines)

def switch_task_sync(task: Dict):
    user_id = task['user_id']

    # Keep reference to old proc (don't terminate it yet)
    try:
        old_proc = task.get('proc')
        old_pid = task.get('pid')
    except Exception:
        old_proc = None
        old_pid = task.get('pid')

    # Advance index first so new account is chosen
    task['pair_index'] = (task['pair_index'] + 1) % len(task['pair_list'])
    next_u = task['pair_list'][task['pair_index']]
    data = users_data.get(user_id)
    if not data:
        logging.error(f"No users_data for user {user_id} during switch")
        return

    next_acc = next((a for a in data['accounts'] if a['ig_username'] == next_u), None)
    if not next_acc:
        logging.error(f"Can't find account {next_u} for switch")
        try:
            asyncio.run_coroutine_threadsafe(
                APP.bot.send_message(user_id, f"can't find thread Id - {next_u}"),
                LOOP
            )
        except Exception:
            pass
        return

    next_pass = next_acc['password']
    next_state_file = os.path.join(PROJECT_DIR, "sessions", f"{user_id}_{next_u}_state.json")
    if not os.path.exists(next_state_file):
        try:
            _write_json_atomic(next_state_file, next_acc.get('storage_state', {}))
        except (OSError, TypeError, ValueError):
            logging.exception("[PROCESS] Failed to write state file for account %s", next_u)
            return

    # Launch new process FIRST so overlap prevents downtime
    new_cmd = [
        sys.executable, os.path.join(PROJECT_DIR, "msg.py"),
        "--thread-url", task['target_thread_url'],
        "--names", _project_path(task['names_file']),
        "--tabs", str(task['threads']),
        "--headless", "true",
        "--storage-state", _project_path(next_state_file)
    ]
    try:
        new_proc = _launch_message_process(new_cmd, next_u, next_pass)
    except Exception:
        log_exception_safely("[PROCESS] Failed to start the switched message worker", next_pass)
        return

    # Append new to proc_list
    task['proc_list'].append(new_proc.pid)

    # Register new proc and update task/persistent info
    running_processes[new_proc.pid] = new_proc
    task['cmd'] = new_cmd
    task['pid'] = new_proc.pid
    task['proc'] = new_proc
    task['last_switch_time'] = time.time()
    task['process_started_at'] = task['last_switch_time']
    try:
        update_task_pid_persistent(task['id'], task['pid'], task)
    except Exception as e:
        logging.error(f"Failed to update persistent pid for task {task.get('id')}: {e}")

    # Give old proc a short cooldown window before killing it (avoid downtime)
    if old_proc and old_pid != new_proc.pid:
        # Allow overlap for a short cooldown before stopping the old worker.
        time.sleep(5)
        if _stop_message_process(old_proc):
            if old_pid in task['proc_list']:
                task['proc_list'].remove(old_pid)
            if old_pid in running_processes:
                running_processes.pop(old_pid, None)
        else:
            logging.error("[PROCESS] Old worker remains tracked after failed shutdown (pid=%s)", old_pid)

    # Send/update status message (edit if message id present)
    try:
        chat_id = task.get('status_chat_id', user_id)
        msg_id = task.get('status_msg_id')
        text = "Spamming...!\n" + get_switch_update(task)
        text += f"\nTo stop 🛑 type /stop {task['display_pid']} or /stop all to stop all processes."
        if msg_id:
            asyncio.run_coroutine_threadsafe(
                APP.bot.edit_message_text(chat_id=chat_id, message_id=msg_id, text=text),
                LOOP
            )
        else:
            asyncio.run_coroutine_threadsafe(
                APP.bot.send_message(chat_id=chat_id, text=text),
                LOOP
            )
    except Exception as e:
        logging.error(f"Failed to update status message: {e}")


def _notify_worker_exit(task: Dict, return_code: int | None) -> None:
    logging.error(
        "[PROCESS] Message worker exited (task=%s, pid=%s, exit_code=%s); see %s",
        task.get("id"),
        task.get("pid"),
        return_code,
        MESSAGE_PROCESS_LOG,
    )
    if APP is None or LOOP is None:
        return
    try:
        future = asyncio.run_coroutine_threadsafe(
            APP.bot.send_message(
                chat_id=task.get("status_chat_id", task.get("user_id")),
                text=f"⚠️ Message worker exited (code {return_code}). Check the server log.",
            ),
            LOOP,
        )
        future.add_done_callback(_log_worker_notice_failure)
    except Exception:
        logging.exception("[PROCESS] Could not schedule worker-exit notification")


def _log_worker_notice_failure(future) -> None:
    try:
        future.result()
    except Exception:
        logging.exception("[PROCESS] Could not deliver worker-exit notification")


def switch_monitor():
    while True:
        time.sleep(30)
        for user_id in list(users_tasks):
            if user_id not in users_tasks:
                continue
            for task in users_tasks[user_id]:
                proc = task.get("proc")
                if (
                    task.get("type") == "message_attack"
                    and task.get("status") == "running"
                    and isinstance(proc, subprocess.Popen)
                    and proc.poll() is not None
                ):
                    task["status"] = "completed"
                    for pid in task.get("proc_list", []):
                        running_processes.pop(pid, None)
                    mark_task_completed_persistent(task["id"])
                    _notify_worker_exit(task, proc.returncode)
                    continue
                if task.get('type') == 'message_attack' and task['status'] == 'running' and isinstance(proc, subprocess.Popen) and proc.poll() is None:
                    due_time = task['last_switch_time'] + task['switch_minutes'] * 60
                    if time.time() >= due_time:
                        if len(task['pair_list']) > 1:
                            switch_task_sync(task)

async def stop(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    user_id = update.effective_user.id
    if not is_authorized(user_id):
        await update.message.reply_text("⚠️ You are not authorised to use, dm owner to gain access! @spyther ⚠️")
        return
    if not context.args:
        await update.message.reply_text("❗ Usage: /stop <PID> or /stop all ❗")
        return
    arg = context.args[0]
    if user_id not in users_tasks or not users_tasks[user_id]:
        await update.message.reply_text("❌ No tasks running. ❌")
        return
    tasks = users_tasks[user_id]
    if arg == 'all':
        stopped_count = 0
        failed_count = 0
        for task in tasks[:]:
            if not await asyncio.to_thread(_stop_task_processes, task):
                failed_count += 1
                continue
            if task.get('type') == 'message_attack' and 'names_file' in task:
                names_file = _project_path(task['names_file'])
                if _is_within_project(names_file) and os.path.exists(names_file):
                    os.remove(names_file)
            logging.info(f"{time.strftime('%Y-%m-%d %H:%M:%S')} Task stop user={user_id} task={task['id']}")
            mark_task_stopped_persistent(task['id'])
            tasks.remove(task)
            stopped_count += 1
        await update.message.reply_text(
            f"🛑 Stopped {stopped_count} task(s); {failed_count} could not be stopped. 🛑"
        )
    elif arg.isdigit():
        pid_to_stop = int(arg)
        stopped_task = None

        # Match only this user's tasks; never signal an unowned PID from chat input.
        for task in tasks[:]:
            if task.get('display_pid') == pid_to_stop or pid_to_stop in task.get('proc_list', []):
                if not await asyncio.to_thread(_stop_task_processes, task):
                    await reply_error_safely(
                        update,
                        f"❌ Could not stop task {pid_to_stop}. Check the server logs.",
                    )
                    return
                mark_task_stopped_persistent(task['id'])
                names_file = _project_path(task['names_file']) if isinstance(task.get('names_file'), str) else ""
                if names_file and _is_within_project(names_file) and os.path.exists(names_file):
                    os.remove(names_file)
                stopped_task = task
                tasks.remove(task)
                await update.message.reply_text(f"🛑 Stopped task {pid_to_stop}!")
                break

        if not stopped_task:
            await update.message.reply_text("⚠️ Task not found. ⚠️")
    else:
        await update.message.reply_text("❗ Usage: /stop <PID> or /stop all ❗")
    users_tasks[user_id] = tasks

async def task_command(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    user_id = update.effective_user.id
    if not is_authorized(user_id):
        await update.message.reply_text("⚠️ You are not authorised to use, dm owner to gain access! @spyther ⚠️")
        return
    if user_id not in users_tasks or not users_tasks[user_id]:
        await update.message.reply_text("❌ No ongoing tasks. ❌")
        return
    tasks = users_tasks[user_id]
    active_tasks = []
    for t in tasks:
        if t['proc'].poll() is None:
            active_tasks.append(t)
        else:
            mark_task_completed_persistent(t['id'])
    users_tasks[user_id] = active_tasks
    if not active_tasks:
        await update.message.reply_text("❌ No active tasks. ❌")
        return
    msg = "📋 Ongoing tasks 📋\n"
    for task in active_tasks:
        tdisplay = task.get('target_display', 'Unknown')
        ttype = task.get('type', 'unknown')
        preview = tdisplay[:20] + '...' if len(tdisplay) > 20 else tdisplay
        display_pid = task.get('display_pid', task['pid'])
        msg += f"PID {display_pid} — {preview} ({ttype})\n"
    await update.message.reply_text(msg)

async def usg_command(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not is_authorized(update.effective_user.id):
        await update.message.reply_text("⚠️ You are not authorised to use, dm owner to gain access! @spyther ⚠️")
        return
    cpu = psutil.cpu_percent(interval=1)
    mem = psutil.virtual_memory()
    ram_used = mem.used / (1024 ** 3)
    ram_total = mem.total / (1024 ** 3)
    msg = f"🖥️ CPU Usage: {cpu:.1f}%\n💾 RAM: {ram_used:.1f}GB / {ram_total:.1f}GB ({mem.percent:.1f}%)"
    await update.message.reply_text(msg)

async def cancel_handler(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    user_id = update.effective_user.id
    if user_id in user_fetching:
        user_cancel_fetch.add(user_id)
        await update.message.reply_text("❌ Fetching cancelled! 🚫")
    else:
        await update.message.reply_text("No active fetching to cancel. 😊")

async def add_user(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    user_id = update.effective_user.id
    if not is_owner(user_id):
        await update.message.reply_text("⚠️ you are not an admin ⚠️")
        return
    if len(context.args) != 1:
        await update.message.reply_text("❗ Usage: /add <tg_id> ❗")
        return
    if not context.args[0].isdigit() or int(context.args[0]) <= 0:
        await update.message.reply_text("⚠️ Invalid tg_id. ⚠️")
        return
    tg_id = int(context.args[0])
    if any(u['id'] == tg_id for u in authorized_users):
        await update.message.reply_text("❗ User already added. ❗")
        return
    authorized_users.append({'id': tg_id, 'username': ''})
    save_authorized()
    await update.message.reply_text(f"➕ Added {tg_id} as authorized user. ➕")

async def remove_user(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    user_id = update.effective_user.id
    if not is_owner(user_id):
        await update.message.reply_text("⚠️ you are not an admin ⚠️")
        return
    if not context.args or not context.args[0].isdigit():
        await update.message.reply_text("❗ Usage: /remove <tg_id> ❗")
        return
    tg_id = int(context.args[0])
    global authorized_users
    authorized_users = [u for u in authorized_users if u['id'] != tg_id]
    save_authorized()
    await update.message.reply_text(f"➖ Removed {tg_id} from authorized users. ➖")

async def list_users(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    user_id = update.effective_user.id
    if not is_owner(user_id):
        await update.message.reply_text("⚠️ you are not an admin ⚠️")
        return
    if not authorized_users:
        await update.message.reply_text("❌ No authorized users. ❌")
        return
    msg = "📜 Authorized users: 📜\n"
    for i, u in enumerate(authorized_users, 1):
        if u['id'] == OWNER_TG_ID:
            msg += f"{i}.(tg id {u['id']}) owner\n"
        elif u['username']:
            msg += f"{i}.(tg id {u['id']}) @{u['username']}\n"
        else:
            msg += f"{i}.(tg id {u['id']})\n"
    await update.message.reply_text(msg)

def main_bot():
    from telegram.request import HTTPXRequest
    request = HTTPXRequest(connect_timeout=30, read_timeout=30, write_timeout=30)
    application = Application.builder().token(BOT_TOKEN).request(request).build()
    global APP, LOOP
    APP = application
    application.add_error_handler(telegram_error_handler)
    
    # Restore tasks
    restore_tasks_on_start()
    
    # Post init for notifications
    async def post_init(app):
        global LOOP
        LOOP = asyncio.get_running_loop()

        # Start the monitor only after the application's event loop is available.
        monitor_thread = threading.Thread(target=switch_monitor, daemon=True)
        monitor_thread.start()

        for user_id, tasks_list in list(users_tasks.items()):
            for task in tasks_list:
                if task.get('type') == 'message_attack' and task['status'] == 'running':
                    await send_resume_notification(user_id, task)
    
    application.post_init = post_init

    application.add_handler(CommandHandler("start", start))
    application.add_handler(CommandHandler("help", help_command))
    application.add_handler(CommandHandler("viewmyac", viewmyac))
    application.add_handler(CommandHandler("setig", setig))
    application.add_handler(CommandHandler("pair", pair_command))
    application.add_handler(CommandHandler("unpair", unpair_command))
    application.add_handler(CommandHandler("switch", switch_command))
    application.add_handler(CommandHandler("threads", threads_command))
    application.add_handler(CommandHandler("viewpref", viewpref))
    application.add_handler(CommandHandler("stop", stop))
    application.add_handler(CommandHandler("task", task_command))
    application.add_handler(CommandHandler("add", add_user))
    application.add_handler(CommandHandler("remove", remove_user))
    application.add_handler(CommandHandler("users", list_users))
    application.add_handler(CommandHandler("logout", logout_command))
    application.add_handler(CommandHandler("kill", cmd_kill))
    application.add_handler(CommandHandler("flush", flush))
    application.add_handler(CommandHandler("usg", usg_command))
    application.add_handler(CommandHandler("cancel", cancel_handler))

    conv_login = ConversationHandler(
        entry_points=[CommandHandler("login", login_start)],
        states={
            USERNAME: [MessageHandler(filters.TEXT & ~filters.COMMAND, get_username)],
            PASSWORD: [MessageHandler(filters.TEXT & ~filters.COMMAND, get_password)],
        },
        fallbacks=[],
    )
    application.add_handler(conv_login)

    conv_plogin = ConversationHandler(
        entry_points=[CommandHandler("plogin", plogin_start)],
        states={
            PLO_USERNAME: [MessageHandler(filters.TEXT & ~filters.COMMAND, plogin_get_username)],
            PLO_PASSWORD: [MessageHandler(filters.TEXT & ~filters.COMMAND, plogin_get_password)],
        },
        fallbacks=[],
    )
    application.add_handler(conv_plogin)

    conv_slogin = ConversationHandler(
        entry_points=[CommandHandler("slogin", slogin_start)],
        states={
            SLOG_SESSION: [MessageHandler(filters.TEXT & ~filters.COMMAND, slogin_get_session)],
            SLOG_USERNAME: [MessageHandler(filters.TEXT & ~filters.COMMAND, slogin_get_username)],
        },
        fallbacks=[],
    )
    application.add_handler(conv_slogin)
    
    psid_handler = ConversationHandler(
    entry_points=[CommandHandler("psid", psid_start)],
    states={
        PSID_SESSION: [MessageHandler(filters.TEXT & ~filters.COMMAND, psid_get_session)],
        PSID_USERNAME: [MessageHandler(filters.TEXT & ~filters.COMMAND, psid_get_username)],
    },
    fallbacks=[]
)

    application.add_handler(psid_handler)

    conv_attack = ConversationHandler(
        entry_points=[CommandHandler("attack", attack_start)],
        states={
            MODE: [MessageHandler(filters.TEXT & ~filters.COMMAND, get_mode)],
            SELECT_GC: [MessageHandler(filters.TEXT & ~filters.COMMAND, select_gc_handler)],
            TARGET: [MessageHandler(filters.TEXT & ~filters.COMMAND, get_target_handler)],
            MESSAGES: [
                MessageHandler(filters.Document.FileExtension("txt"), get_messages_file),
                MessageHandler(filters.TEXT & ~filters.COMMAND, get_messages),
            ],
        },
        fallbacks=[],
    )
    application.add_handler(conv_attack)

    conv_pattack = ConversationHandler(
        entry_points=[CommandHandler("pattack", pattack_start)],
        states={
            P_MODE: [MessageHandler(filters.TEXT & ~filters.COMMAND, p_get_mode)],
            P_TARGET_DISPLAY: [MessageHandler(filters.TEXT & ~filters.COMMAND, p_get_target_display)],
            P_THREAD_URL: [MessageHandler(filters.TEXT & ~filters.COMMAND, p_get_thread_url)],
            P_MESSAGES: [
                MessageHandler(filters.Document.FileExtension("txt"), p_get_messages_file),
                MessageHandler(filters.TEXT & ~filters.COMMAND, p_get_messages),
            ],
        },
        fallbacks=[],
    )
    application.add_handler(conv_pattack)

    application.add_handler(MessageHandler(filters.TEXT & ~filters.COMMAND, handle_text))

    print("🚀 Bot starting with message attack system!")
    application.run_polling()

if __name__ == "__main__":
    main_bot()