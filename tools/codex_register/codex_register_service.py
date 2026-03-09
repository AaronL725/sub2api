import argparse
import base64
import hashlib
import imaplib
import importlib
import json
import logging
import os
import random
import re
import secrets
import shutil
import subprocess
import sys
import time
import urllib.error
import urllib.parse
import urllib.request
from collections import deque
import concurrent.futures
from dataclasses import dataclass, field
from datetime import datetime, timezone
from email.header import decode_header
from email.utils import parsedate_to_datetime
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
import email as email_module
import html as html_module
import threading
import traceback
from typing import Any, Callable, Dict, List, Optional, Set, Tuple



def get_requests_module():
    return importlib.import_module("curl_cffi.requests")


# ---------------------------------------------------------------------------
# Logging
# ---------------------------------------------------------------------------
_log_lock = threading.Lock()


def _setup_logger() -> logging.Logger:
    logger = logging.getLogger("codex_register")
    logger.setLevel(logging.INFO)
    fmt = logging.Formatter("%(asctime)s [%(levelname)s] %(message)s")
    sh = logging.StreamHandler(sys.stdout)
    sh.setFormatter(fmt)
    logger.addHandler(sh)
    return logger


log = _setup_logger()


# ---------------------------------------------------------------------------
# Global state
# ---------------------------------------------------------------------------
enabled = True
last_run = None
last_success = None
last_error = ""
total_created = 0
total_updated = 0
total_skipped = 0
total_failed = 0
sleep_min_global = 0
sleep_max_global = 0
tokens_dir_global = None
last_token_email = ""
last_created_email = ""
last_created_account_id = ""
last_updated_email = ""
last_updated_account_id = ""
last_processed_records = 0
recent_logs: List[Dict[str, str]] = []
status_lock = threading.Lock()
JSONDict = Dict[str, Any]

# Sliding window for failure rate tracking
_recent_results: deque = deque(maxlen=20)
_results_lock = threading.Lock()
FAILURE_RATE_THRESHOLD = 0.8  # pause if 80%+ of recent attempts failed
MIN_WINDOW_SIZE = 5  # need at least 5 results before checking failure rate

DEFAULT_MODEL_MAPPING: Dict[str, str] = {
    "claude-haiku*": "gpt-5.3-codex-spark",
    "claude-sonnet*": "gpt-5.4",
    "claude-opus*": "gpt-5.4",
    "gpt-5": "gpt-5",
    "gpt-5.1": "gpt-5.1",
    "gpt-5.1-codex": "gpt-5.1-codex",
    "gpt-5.1-codex-max": "gpt-5.1-codex-max",
    "gpt-5.1-codex-mini": "gpt-5.1-codex-mini",
    "gpt-5.2": "gpt-5.2",
    "gpt-5.2-codex": "gpt-5.2-codex",
    "gpt-5.3-codex": "gpt-5.3-codex",
    "gpt-5.3-codex-spark": "gpt-5.3-codex-spark",
    "gpt-5.4": "gpt-5.4",
}


def append_log(level: str, message: str) -> None:
    with status_lock:
        recent_logs.append(
            {
                "time": datetime.utcnow().isoformat() + "Z",
                "level": level,
                "message": message,
            }
        )
        if len(recent_logs) > 100:
            del recent_logs[0 : len(recent_logs) - 100]


def ensure_dict(value: object) -> JSONDict:
    if isinstance(value, dict):
        return dict(value)
    if isinstance(value, str):
        try:
            parsed = json.loads(value)
            if isinstance(parsed, dict):
                return parsed
        except Exception:
            return {}
    return {}


def parse_group_ids() -> List[int]:
    raw = get_env("CODEX_GROUP_IDS", "")
    if not raw:
        return []
    group_ids: List[int] = []
    for item in raw.split(","):
        item = item.strip()
        if not item:
            continue
        try:
            value = int(item)
        except ValueError:
            continue
        if value > 0:
            group_ids.append(value)
    return group_ids


def build_model_mapping() -> Dict[str, str]:
    raw = get_env("CODEX_MODEL_MAPPING_JSON", "")
    if not raw:
        return dict(DEFAULT_MODEL_MAPPING)

    parsed = ensure_dict(raw)
    mapping: Dict[str, str] = {}
    for key, value in parsed.items():
        pattern = str(key).strip()
        target = str(value).strip()
        if pattern and target:
            mapping[pattern] = target

    if mapping:
        return mapping

    return dict(DEFAULT_MODEL_MAPPING)


def get_env(name: str, default=None, required: bool = False) -> str:
    value = os.getenv(name, default)
    if required and not value:
        raise RuntimeError(f"环境变量 {name} 未配置且为必需")
    return value or ""


MAILTM_BASE = "https://api.mail.tm"
AUTH_URL = "https://auth.openai.com/oauth/authorize"
TOKEN_URL = "https://auth.openai.com/oauth/token"
SENTINEL_URL = "https://sentinel.openai.com/backend-api/sentinel/req"
SIGNUP_URL = "https://auth.openai.com/api/accounts/authorize/continue"
SEND_OTP_URL = "https://auth.openai.com/api/accounts/passwordless/send-otp"
VERIFY_OTP_URL = "https://auth.openai.com/api/accounts/email-otp/validate"
CREATE_ACCOUNT_URL = "https://auth.openai.com/api/accounts/create_account"
WORKSPACE_SELECT_URL = "https://auth.openai.com/api/accounts/workspace/select"
CLIENT_ID = "app_EMoamEEZ73f0CkXaXp7hrann"
DEFAULT_REDIRECT_URI = "http://localhost:1455/auth/callback"
DEFAULT_SCOPE = "openid email profile offline_access"
MAX_RETRY_PER_ACCOUNT = 2
IMAP_POLL_TIMEOUT = 180
OTP_RESEND_INTERVAL = 25


# ---------------------------------------------------------------------------
# Sliding window failure tracking
# ---------------------------------------------------------------------------
def record_result(success: bool) -> None:
    with _results_lock:
        _recent_results.append(success)


def should_pause_for_failures() -> bool:
    with _results_lock:
        if len(_recent_results) < MIN_WINDOW_SIZE:
            return False
        fail_count = sum(1 for r in _recent_results if not r)
        return (fail_count / len(_recent_results)) >= FAILURE_RATE_THRESHOLD


# ---------------------------------------------------------------------------
# Random name / birthday
# ---------------------------------------------------------------------------
_GIVEN_NAMES = [
    "Liam", "Noah", "Oliver", "James", "Elijah", "William", "Henry", "Lucas",
    "Benjamin", "Theodore", "Jack", "Levi", "Alexander", "Mason", "Ethan",
    "Daniel", "Jacob", "Michael", "Logan", "Jackson", "Sebastian", "Aiden",
    "Owen", "Samuel", "Ryan", "Nathan", "Carter", "Luke", "Jayden", "Dylan",
    "Caleb", "Isaac", "Connor", "Adrian", "Hunter", "Eli", "Thomas", "Aaron",
    "Olivia", "Emma", "Charlotte", "Amelia", "Sophia", "Isabella", "Mia",
    "Evelyn", "Harper", "Luna", "Camila", "Sofia", "Scarlett", "Elizabeth",
    "Eleanor", "Emily", "Chloe", "Mila", "Avery", "Riley", "Aria", "Layla",
    "Nora", "Lily", "Hannah", "Hazel", "Zoey", "Stella", "Aurora", "Natalie",
]

_FAMILY_NAMES = [
    "Smith", "Johnson", "Williams", "Brown", "Jones", "Miller", "Davis",
    "Wilson", "Anderson", "Thomas", "Taylor", "Moore", "Jackson", "Martin",
    "Lee", "Thompson", "White", "Harris", "Clark", "Lewis", "Robinson",
    "Walker", "Young", "Allen", "King", "Wright", "Hill", "Scott", "Green",
    "Adams", "Baker", "Nelson", "Carter", "Mitchell", "Roberts", "Turner",
    "Phillips", "Campbell", "Parker", "Evans", "Edwards", "Collins", "Stewart",
]


def random_name() -> str:
    return f"{random.choice(_GIVEN_NAMES)} {random.choice(_FAMILY_NAMES)}"


def random_birthday() -> str:
    y = random.randint(1986, 2006)
    m = random.randint(1, 12)
    d = random.randint(1, 28)
    return f"{y}-{m:02d}-{d:02d}"


# ---------------------------------------------------------------------------
# Browser fingerprint diversity (TLS impersonation)
# ---------------------------------------------------------------------------
_BROWSER_PROFILES = [
    "chrome120", "chrome123", "chrome124", "chrome131",
    "chrome133a", "chrome136",
    "edge99", "edge101",
    "safari15_3", "safari15_5", "safari17_0",
]

_ACCEPT_LANGUAGES = [
    "en-US,en;q=0.9",
    "en-US,en;q=0.9,zh-CN;q=0.8",
    "en-GB,en;q=0.9,en-US;q=0.8",
    "en-US,en;q=0.8",
    "en,en-US;q=0.9",
    "en-US,en;q=0.9,de;q=0.7",
    "en-US,en;q=0.9,ja;q=0.7",
]


def _pick_fingerprint() -> Tuple[str, Dict[str, str]]:
    profile = random.choice(_BROWSER_PROFILES)
    lang = random.choice(_ACCEPT_LANGUAGES)
    headers = {
        "Accept-Language": lang,
        "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8",
        "Accept-Encoding": "gzip, deflate, br",
        "DNT": "1",
        "Sec-Fetch-Dest": "document",
        "Sec-Fetch-Mode": "navigate",
        "Sec-Fetch-Site": "none",
        "Sec-Fetch-User": "?1",
        "Upgrade-Insecure-Requests": "1",
    }
    return profile, headers


# ---------------------------------------------------------------------------
# Outlook IMAP email retrieval (XOAUTH2 + password fallback)
# ---------------------------------------------------------------------------
@dataclass
class MailAccount:
    email: str
    password: str
    client_id: str = ""
    refresh_token: str = ""

    @classmethod
    def parse(cls, line: str) -> "MailAccount":
        fields = [f.strip() for f in line.strip().split("----")]
        if len(fields) < 2:
            raise ValueError(f"Invalid format, need at least email----password: {line[:60]}")
        return cls(
            email=fields[0],
            password=fields[1],
            client_id=fields[2] if len(fields) > 2 and fields[2] else "",
            refresh_token=fields[3] if len(fields) > 3 and fields[3] else "",
        )


def load_accounts_file(path: str) -> List[MailAccount]:
    if not os.path.isfile(path):
        return []
    result = []
    with open(path, "r", encoding="utf-8") as f:
        for line in f:
            line = line.strip()
            if not line or line.startswith("#"):
                continue
            try:
                result.append(MailAccount.parse(line))
            except ValueError as e:
                log.warning(f"Skipping invalid account line: {e}")
    return result


_ms_token_cache: Dict[str, Tuple[str, float]] = {}
_ms_cache_lock = threading.Lock()


def refresh_ms_token(account: MailAccount, timeout: int = 15) -> str:
    if not account.client_id or not account.refresh_token:
        raise RuntimeError("Missing client_id or refresh_token for XOAUTH2")
    key = account.email.lower()
    with _ms_cache_lock:
        cached = _ms_token_cache.get(key)
        if cached and time.time() < cached[1]:
            return cached[0]
    body = urllib.parse.urlencode({
        "client_id": account.client_id,
        "refresh_token": account.refresh_token,
        "grant_type": "refresh_token",
        "redirect_uri": "https://login.live.com/oauth20_desktop.srf",
    }).encode()
    req = urllib.request.Request("https://login.live.com/oauth20_token.srf", data=body)
    try:
        with urllib.request.urlopen(req, timeout=timeout) as resp:
            data = json.loads(resp.read())
    except urllib.error.HTTPError as e:
        raise RuntimeError(f"MS OAuth refresh failed: {e.code}") from e
    token = data.get("access_token")
    if not token:
        raise RuntimeError("MS OAuth response missing access_token")
    ttl = int(data.get("expires_in", 3600))
    with _ms_cache_lock:
        _ms_token_cache[key] = (token, time.time() + ttl - 120)
    return token


def _build_xoauth2(email_addr: str, token: str) -> bytes:
    return f"user={email_addr}\x01auth=Bearer {token}\x01\x01".encode()


_RE_CODE = re.compile(r"(?<!\d)(\d{6})(?!\d)")
_imap_semaphore = threading.Semaphore(10)


class OutlookIMAP:
    def __init__(self, account: MailAccount, host: str = "outlook.office365.com", port: int = 993):
        self.account = account
        self.host = host
        self.port = port
        self._conn: Optional[imaplib.IMAP4_SSL] = None

    def connect(self) -> None:
        self._conn = imaplib.IMAP4_SSL(self.host, self.port, timeout=20)
        if self.account.client_id and self.account.refresh_token:
            try:
                token = refresh_ms_token(self.account)
                self._conn.authenticate("XOAUTH2",
                    lambda _: _build_xoauth2(self.account.email, token))
                return
            except Exception:
                pass
        self._conn.login(self.account.email, self.account.password)

    def _ensure(self) -> None:
        if self._conn:
            try:
                self._conn.noop()
                return
            except Exception:
                self.close()
        self.connect()

    def get_recent_mails(self, count: int = 20, only_unseen: bool = True) -> List[Dict[str, str]]:
        self._ensure()
        flag = "UNSEEN" if only_unseen else "ALL"
        self._conn.select("INBOX", readonly=True)
        _, data = self._conn.search(None, flag)
        if not data or not data[0]:
            return []
        ids = data[0].split()[-count:]
        result = []
        for mid in reversed(ids):
            _, payload = self._conn.fetch(mid, "(RFC822)")
            if not payload:
                continue
            raw = b""
            for part in payload:
                if isinstance(part, tuple) and len(part) > 1:
                    raw = part[1]
                    break
            if raw:
                result.append(self._parse(raw))
        return result

    @staticmethod
    def _parse(raw: bytes) -> Dict[str, str]:
        if raw.startswith(b"\xef\xbb\xbf"):
            raw = raw[3:]
        msg = email_module.message_from_bytes(raw)
        subject = OutlookIMAP._decode_header(msg.get("Subject", ""))
        sender = OutlookIMAP._decode_header(msg.get("From", ""))
        date = OutlookIMAP._decode_header(msg.get("Date", ""))
        to = OutlookIMAP._decode_header(msg.get("To", ""))
        delivered_to = OutlookIMAP._decode_header(msg.get("Delivered-To", ""))
        x_original_to = OutlookIMAP._decode_header(msg.get("X-Original-To", ""))
        body = OutlookIMAP._extract_body(msg)
        return {"subject": subject, "from": sender, "date": date, "body": body,
                "to": to, "delivered_to": delivered_to, "x_original_to": x_original_to}

    @staticmethod
    def _decode_header(val: Optional[str]) -> str:
        if not val:
            return ""
        parts = []
        for chunk, enc in decode_header(val):
            if isinstance(chunk, bytes):
                parts.append(chunk.decode(enc or "utf-8", errors="replace"))
            else:
                parts.append(chunk)
        return "".join(parts).strip()

    @staticmethod
    def _extract_body(msg: Any) -> str:
        texts = []
        parts = msg.walk() if msg.is_multipart() else [msg]
        for part in parts:
            ct = part.get_content_type()
            if ct not in ("text/plain", "text/html"):
                continue
            payload = part.get_payload(decode=True)
            if not payload:
                continue
            charset = part.get_content_charset() or "utf-8"
            try:
                t = payload.decode(charset, errors="replace")
            except LookupError:
                t = payload.decode("utf-8", errors="replace")
            if "<html" in t.lower():
                t = re.sub(r"<[^>]+>", " ", t)
            texts.append(t)
        return re.sub(r"\s+", " ", html_module.unescape(" ".join(texts))).strip()

    def close(self) -> None:
        if self._conn:
            try:
                self._conn.close()
            except Exception:
                pass
            try:
                self._conn.logout()
            except Exception:
                pass
            self._conn = None

    def __enter__(self) -> "OutlookIMAP":
        return self

    def __exit__(self, *a: Any) -> None:
        self.close()


class DomainIMAP:
    """Domain catch-all IMAP: single inbox receives mail for all sub-addresses."""

    def __init__(self, host: str, port: int, user: str, password: str):
        self.host = host
        self.port = port
        self.user = user
        self.password = password
        self._conn: Optional[imaplib.IMAP4_SSL] = None

    def connect(self) -> None:
        self._conn = imaplib.IMAP4_SSL(self.host, self.port, timeout=20)
        self._conn.login(self.user, self.password)

    def _ensure(self) -> None:
        if self._conn:
            try:
                self._conn.noop()
                return
            except Exception:
                self.close()
        self.connect()

    def get_recent_mails(self, count: int = 20, only_unseen: bool = True) -> List[Dict[str, str]]:
        self._ensure()
        flag = "UNSEEN" if only_unseen else "ALL"
        self._conn.select("INBOX", readonly=True)
        _, data = self._conn.search(None, flag)
        if not data or not data[0]:
            return []
        ids = data[0].split()[-count:]
        result = []
        for mid in reversed(ids):
            _, payload = self._conn.fetch(mid, "(RFC822)")
            if not payload:
                continue
            raw = b""
            for part in payload:
                if isinstance(part, tuple) and len(part) > 1:
                    raw = part[1]
                    break
            if raw:
                result.append(OutlookIMAP._parse(raw))
        return result

    def close(self) -> None:
        if self._conn:
            try:
                self._conn.close()
            except Exception:
                pass
            try:
                self._conn.logout()
            except Exception:
                pass
            self._conn = None

    def __enter__(self) -> "DomainIMAP":
        return self

    def __exit__(self, *a: Any) -> None:
        self.close()


class DomainMailHub:
    """Shared IMAP poller for domain catch-all: 1 connection serves N workers."""

    _instances: Dict[str, "DomainMailHub"] = {}
    _instances_lock = threading.Lock()

    @classmethod
    def get_or_create(cls, domain_mail: Dict[str, str]) -> "DomainMailHub":
        key = f"{domain_mail['host']}:{domain_mail.get('port', '993')}:{domain_mail['user']}"
        with cls._instances_lock:
            if key not in cls._instances or not cls._instances[key]._running:
                hub = cls(domain_mail)
                hub.start()
                cls._instances[key] = hub
            return cls._instances[key]

    def __init__(self, domain_mail: Dict[str, str]):
        self._config = domain_mail
        self._running = False
        self._lock = threading.Lock()
        self._waiters: Dict[str, List[Tuple[str, str, Optional[float]]]] = {}
        self._delivered: Dict[str, Set[str]] = {}
        self._thread: Optional[threading.Thread] = None
        self._ref_count = 0

    def start(self) -> None:
        if self._running:
            return
        self._running = True
        self._thread = threading.Thread(target=self._poll_loop, daemon=True)
        self._thread.start()

    def register(self, email: str) -> None:
        email_lower = email.lower()
        with self._lock:
            self._ref_count += 1
            if email_lower not in self._waiters:
                self._waiters[email_lower] = []
            if email_lower not in self._delivered:
                self._delivered[email_lower] = set()

    def unregister(self, email: str) -> None:
        with self._lock:
            self._ref_count -= 1
            if self._ref_count <= 0:
                self._ref_count = 0

    def wait_code(self, email: str, timeout: int, used_codes: Set[str],
                  otp_sent_at: float, resend_fn: Optional[Callable] = None) -> str:
        email_lower = email.lower()
        min_ts = (otp_sent_at - 60) if otp_sent_at else 0
        start = time.time()
        last_resend = 0.0
        while time.time() - start < timeout:
            with self._lock:
                queue = self._waiters.get(email_lower, [])
                while queue:
                    code, _source, mail_ts = queue.pop(0)
                    if code in used_codes:
                        continue
                    if min_ts > 0 and mail_ts and mail_ts < min_ts:
                        continue
                    used_codes.add(code)
                    elapsed = int(time.time() - start)
                    log.info(f"    OTP code: {code} ({elapsed}s, shared poll)")
                    return code
            elapsed_now = time.time() - start
            if resend_fn and elapsed_now > 20 and (elapsed_now - last_resend) > OTP_RESEND_INTERVAL:
                try:
                    resend_fn()
                    last_resend = elapsed_now
                    log.info("    Resent OTP")
                except Exception:
                    pass
            time.sleep(2)
        raise TimeoutError(f"OTP timeout ({timeout}s)")

    def _poll_loop(self) -> None:
        imap: Optional[DomainIMAP] = None
        fails = 0
        poll_idx = 0
        while self._running:
            try:
                with self._lock:
                    if self._ref_count <= 0:
                        time.sleep(1)
                        continue
                if imap is None:
                    imap = DomainIMAP(
                        host=self._config["host"],
                        port=int(self._config.get("port", "993")),
                        user=self._config["user"],
                        password=self._config["pass"],
                    )
                    imap.connect()
                    log.info("    Domain mail hub: IMAP connected")
                mails = imap.get_recent_mails(count=30, only_unseen=(poll_idx < 3))
                fails = 0
                poll_idx += 1
                for m in mails:
                    if not _is_oai_mail(m):
                        continue
                    mail_ts = _parse_email_date(m.get("date", ""))
                    subject = m.get("subject", "")
                    code = None
                    source = "subject"
                    subj_match = _RE_CODE.search(subject)
                    if subj_match:
                        code = subj_match.group(1)
                    else:
                        body = m.get("body", "")
                        precise = re.search(r'(?:code\s+is|验证码)\s*(\d{6})', body, re.IGNORECASE)
                        if precise:
                            code = precise.group(1)
                            source = "body"
                    if not code:
                        continue
                    recipients: Set[str] = set()
                    for fld in ("to", "delivered_to", "x_original_to"):
                        val = m.get(fld, "").lower()
                        if val:
                            recipients.update(re.findall(r'[\w.+-]+@[\w.-]+', val))
                    with self._lock:
                        for email_lower, queue in self._waiters.items():
                            if email_lower in recipients:
                                delivered = self._delivered.get(email_lower, set())
                                if code not in delivered:
                                    delivered.add(code)
                                    queue.append((code, source, mail_ts))
                time.sleep(3)
            except Exception as e:
                fails += 1
                log.warning(f"    Domain mail hub error ({fails}): {e}")
                if imap:
                    try:
                        imap.close()
                    except Exception:
                        pass
                    imap = None
                time.sleep(2)
        if imap:
            try:
                imap.close()
            except Exception:
                pass


def _is_oai_mail(mail: Dict[str, str]) -> bool:
    combined = f"{mail.get('from', '')} {mail.get('subject', '')} {mail.get('body', '')}".lower()
    return any(kw in combined for kw in ("openai", "chatgpt", "verification"))


def _parse_email_date(date_str: str) -> Optional[float]:
    if not date_str:
        return None
    try:
        return parsedate_to_datetime(date_str).timestamp()
    except Exception:
        return None


def poll_verification_code_imap(
    account: MailAccount,
    timeout: int = IMAP_POLL_TIMEOUT,
    used_codes: Optional[Set[str]] = None,
    resend_fn: Optional[Callable] = None,
    otp_sent_at: Optional[float] = None,
    domain_mail: Optional[Dict[str, str]] = None,
) -> str:
    """Poll Outlook/domain IMAP for OpenAI 6-digit OTP code."""
    is_domain = domain_mail is not None
    used = used_codes or set()
    email_lower = account.email.lower()
    min_ts = (otp_sent_at - 60) if otp_sent_at else 0
    intervals = [3, 4, 5, 6, 8, 10]
    idx = 0
    last_resend = 0.0
    start = time.time()
    imap: Any = None
    imap_fails = 0

    if is_domain:
        hub = DomainMailHub.get_or_create(domain_mail)
        hub.register(account.email)
        try:
            return hub.wait_code(account.email, timeout, used,
                                otp_sent_at=otp_sent_at or 0, resend_fn=resend_fn)
        finally:
            hub.unregister(account.email)

    def _connect():
        nonlocal imap
        if imap:
            try:
                imap.close()
            except Exception:
                pass
        _imap_semaphore.acquire()
        try:
            imap = OutlookIMAP(account)
            imap.connect()
        except Exception:
            _imap_semaphore.release()
            raise

    def _close():
        nonlocal imap
        if imap:
            try:
                imap.close()
            except Exception:
                pass
            imap = None
            _imap_semaphore.release()

    try:
        _connect()
        while time.time() - start < timeout:
            try:
                mails = imap.get_recent_mails(count=20, only_unseen=(idx < 2))
                imap_fails = 0
                for m in mails:
                    if not _is_oai_mail(m):
                        continue
                    if min_ts > 0:
                        mail_ts = _parse_email_date(m.get("date", ""))
                        if mail_ts and mail_ts < min_ts:
                            continue
                    subject = m.get("subject", "")
                    subj_match = _RE_CODE.search(subject)
                    if subj_match and subj_match.group(1) not in used:
                        code = subj_match.group(1)
                        used.add(code)
                        elapsed = int(time.time() - start)
                        log.info(f"    OTP code: {code} ({elapsed}s, subject)")
                        return code
                    if not subj_match:
                        body = m.get("body", "")
                        precise = re.search(r'(?:code\s+is|验证码)\s*(\d{6})', body, re.IGNORECASE)
                        if precise and precise.group(1) not in used:
                            code = precise.group(1)
                            used.add(code)
                            elapsed = int(time.time() - start)
                            log.info(f"    OTP code: {code} ({elapsed}s, body)")
                            return code
            except Exception as e:
                imap_fails += 1
                log.warning(f"    IMAP error ({imap_fails}): {e}")
                if imap_fails >= 2:
                    _close()
                    time.sleep(2)
                    try:
                        _connect()
                        imap_fails = 0
                    except Exception as e2:
                        log.warning(f"    IMAP reconnect failed: {e2}")
            elapsed_now = time.time() - start
            if resend_fn and elapsed_now > 20 and (elapsed_now - last_resend) > OTP_RESEND_INTERVAL:
                try:
                    resend_fn()
                    last_resend = elapsed_now
                    log.info("    Resent OTP")
                except Exception:
                    pass
            wait = intervals[min(idx, len(intervals) - 1)]
            idx += 1
            time.sleep(wait)
        raise TimeoutError(f"OTP timeout ({timeout}s)")
    finally:
        _close()


def _mailtm_headers(*, token: str = "", use_json: bool = False) -> Dict[str, Any]:
    headers = {"Accept": "application/json"}
    if use_json:
        headers["Content-Type"] = "application/json"
    if token:
        headers["Authorization"] = f"Bearer {token}"
    return headers


def _mailtm_domains(proxies: Any = None) -> List[str]:
    requests = get_requests_module()
    resp = requests.get(
        f"{MAILTM_BASE}/domains",
        headers=_mailtm_headers(),
        proxies=proxies,
        impersonate="chrome",
        timeout=15,
    )
    if resp.status_code != 200:
        raise RuntimeError(f"获取 Mail.tm 域名失败，状态码: {resp.status_code}")

    data = resp.json()
    if isinstance(data, list):
        items = data
    elif isinstance(data, dict):
        items = data.get("hydra:member") or data.get("items") or []
    else:
        items = []

    domains: List[str] = []
    for item in items:
        if not isinstance(item, dict):
            continue
        domain = str(item.get("domain") or "").strip()
        is_active = item.get("isActive", True)
        is_private = item.get("isPrivate", False)
        if domain and is_active and not is_private:
            domains.append(domain)

    return domains


def get_email_and_token(proxies: Any = None) -> tuple[str, str]:
    requests = get_requests_module()
    try:
        domains = _mailtm_domains(proxies)
        if not domains:
            print("[Error] Mail.tm 没有可用域名")
            return "", ""
        domain = random.choice(domains)

        for _ in range(5):
            local = f"oc{secrets.token_hex(5)}"
            email = f"{local}@{domain}"
            password = secrets.token_urlsafe(18)

            create_resp = requests.post(
                f"{MAILTM_BASE}/accounts",
                headers=_mailtm_headers(use_json=True),
                json={"address": email, "password": password},
                proxies=proxies,
                impersonate="chrome",
                timeout=15,
            )
            if create_resp.status_code not in (200, 201):
                continue

            token_resp = requests.post(
                f"{MAILTM_BASE}/token",
                headers=_mailtm_headers(use_json=True),
                json={"address": email, "password": password},
                proxies=proxies,
                impersonate="chrome",
                timeout=15,
            )
            if token_resp.status_code == 200:
                token = str(token_resp.json().get("token") or "").strip()
                if token:
                    return email, token

        print("[Error] Mail.tm 邮箱创建成功但获取 Token 失败")
        return "", ""
    except Exception as exc:
        print(f"[Error] 请求 Mail.tm API 出错: {exc}")
        return "", ""


def get_oai_code(token: str, email: str, proxies: Any = None) -> str:
    requests = get_requests_module()
    url_list = f"{MAILTM_BASE}/messages"
    regex = r"(?<!\d)(\d{6})(?!\d)"
    seen_ids: set[str] = set()

    print(f"[*] 正在等待邮箱 {email} 的验证码...", end="", flush=True)
    for _ in range(40):
        print(".", end="", flush=True)
        try:
            resp = requests.get(
                url_list,
                headers=_mailtm_headers(token=token),
                proxies=proxies,
                impersonate="chrome",
                timeout=15,
            )
            if resp.status_code != 200:
                time.sleep(3)
                continue

            data = resp.json()
            if isinstance(data, list):
                messages = data
            elif isinstance(data, dict):
                messages = data.get("hydra:member") or data.get("messages") or []
            else:
                messages = []

            for msg in messages:
                if not isinstance(msg, dict):
                    continue
                msg_id = str(msg.get("id") or "").strip()
                if not msg_id or msg_id in seen_ids:
                    continue
                seen_ids.add(msg_id)

                read_resp = requests.get(
                    f"{MAILTM_BASE}/messages/{msg_id}",
                    headers=_mailtm_headers(token=token),
                    proxies=proxies,
                    impersonate="chrome",
                    timeout=15,
                )
                if read_resp.status_code != 200:
                    continue

                mail_data = read_resp.json()
                sender = str(((mail_data.get("from") or {}).get("address") or "")).lower()
                subject = str(mail_data.get("subject") or "")
                intro = str(mail_data.get("intro") or "")
                text = str(mail_data.get("text") or "")
                html = mail_data.get("html") or ""
                if isinstance(html, list):
                    html = "\n".join(str(x) for x in html)
                content = "\n".join([subject, intro, text, str(html)])

                if "openai" not in sender and "openai" not in content.lower():
                    continue

                match = re.search(regex, content)
                if match:
                    print(" 抓到啦! 验证码:", match.group(1))
                    return match.group(1)
        except Exception:
            pass

        time.sleep(3)

    print(" 超时，未收到验证码")
    return ""


def _sanitize_filename_component(value: str, fallback: str = "unknown") -> str:
    sanitized = re.sub(r"[^A-Za-z0-9._-]+", "_", (value or "").strip())
    sanitized = sanitized.strip("._-")
    if not sanitized:
        return fallback
    return sanitized[:128]


def _b64url_no_pad(raw: bytes) -> str:
    return base64.urlsafe_b64encode(raw).decode("ascii").rstrip("=")


def _sha256_b64url_no_pad(value: str) -> str:
    return _b64url_no_pad(hashlib.sha256(value.encode("ascii")).digest())


def _parse_callback_url(callback_url: str) -> Dict[str, Any]:
    candidate = callback_url.strip()
    if not candidate:
        return {"code": "", "state": "", "error": "", "error_description": ""}
    if "://" not in candidate:
        if candidate.startswith("?"):
            candidate = f"http://localhost{candidate}"
        elif any(ch in candidate for ch in "/?#") or ":" in candidate:
            candidate = f"http://{candidate}"
        elif "=" in candidate:
            candidate = f"http://localhost/?{candidate}"
    parsed = urllib.parse.urlparse(candidate)
    query = urllib.parse.parse_qs(parsed.query, keep_blank_values=True)
    fragment = urllib.parse.parse_qs(parsed.fragment, keep_blank_values=True)
    for key, values in fragment.items():
        if key not in query or not query[key] or not (query[key][0] or "").strip():
            query[key] = values

    def get1(key: str) -> str:
        vals = query.get(key, [""])
        return (vals[0] or "").strip()

    code = get1("code")
    state = get1("state")
    error = get1("error")
    error_description = get1("error_description")
    if code and not state and "#" in code:
        code, state = code.split("#", 1)
    if not error and error_description:
        error, error_description = error_description, ""
    return {"code": code, "state": state, "error": error, "error_description": error_description}


def _jwt_claims_no_verify(id_token: str) -> Dict[str, Any]:
    if not id_token or id_token.count(".") < 2:
        return {}
    payload_b64 = id_token.split(".")[1]
    pad = "=" * ((4 - (len(payload_b64) % 4)) % 4)
    try:
        payload = base64.urlsafe_b64decode((payload_b64 + pad).encode("ascii"))
        return json.loads(payload.decode("utf-8"))
    except Exception:
        return {}


def _decode_jwt_segment(segment: str) -> Dict[str, Any]:
    raw = (segment or "").strip()
    if not raw:
        return {}
    pad = "=" * ((4 - (len(raw) % 4)) % 4)
    try:
        decoded = base64.urlsafe_b64decode((raw + pad).encode("ascii"))
        return json.loads(decoded.decode("utf-8"))
    except Exception:
        return {}


def _to_int(value: Any) -> int:
    try:
        return int(value)
    except (TypeError, ValueError):
        return 0


def _post_form(url: str, data: Dict[str, str], timeout: int = 30) -> Dict[str, Any]:
    body = urllib.parse.urlencode(data).encode("utf-8")
    req = urllib.request.Request(
        url, data=body, method="POST",
        headers={"Content-Type": "application/x-www-form-urlencoded", "Accept": "application/json"},
    )
    try:
        with urllib.request.urlopen(req, timeout=timeout) as resp:
            raw_resp = resp.read()
            if resp.status != 200:
                raise RuntimeError(f"token exchange failed: {resp.status}: {raw_resp.decode('utf-8', 'replace')}")
            return json.loads(raw_resp.decode("utf-8"))
    except urllib.error.HTTPError as exc:
        raw_resp = exc.read()
        raise RuntimeError(f"token exchange failed: {exc.code}: {raw_resp.decode('utf-8', 'replace')}") from exc


@dataclass(frozen=True)
class OAuthStart:
    auth_url: str
    state: str
    code_verifier: str
    redirect_uri: str


def generate_oauth_url(*, redirect_uri: str = DEFAULT_REDIRECT_URI, scope: str = DEFAULT_SCOPE) -> OAuthStart:
    state = secrets.token_urlsafe(16)
    code_verifier = secrets.token_urlsafe(48)
    code_challenge = _sha256_b64url_no_pad(code_verifier)
    params = {
        "client_id": CLIENT_ID,
        "response_type": "code",
        "redirect_uri": redirect_uri,
        "scope": scope,
        "state": state,
        "code_challenge": code_challenge,
        "code_challenge_method": "S256",
        "prompt": "login",
        "id_token_add_organizations": "true",
        "codex_cli_simplified_flow": "true",
    }
    auth_url = f"{AUTH_URL}?{urllib.parse.urlencode(params)}"
    return OAuthStart(auth_url=auth_url, state=state, code_verifier=code_verifier, redirect_uri=redirect_uri)


def submit_callback_url(*, callback_url: str, expected_state: str, code_verifier: str, redirect_uri: str = DEFAULT_REDIRECT_URI) -> str:
    callback = _parse_callback_url(callback_url)
    if callback["error"]:
        desc = callback["error_description"]
        raise RuntimeError(f"oauth error: {callback['error']}: {desc}".strip())
    if not callback["code"]:
        raise ValueError("callback url missing ?code=")
    if not callback["state"]:
        raise ValueError("callback url missing ?state=")
    if callback["state"] != expected_state:
        raise ValueError("state mismatch")
    token_resp = _post_form(
        TOKEN_URL,
        {"grant_type": "authorization_code", "client_id": CLIENT_ID,
         "code": callback["code"], "redirect_uri": redirect_uri, "code_verifier": code_verifier},
    )
    access_token = (token_resp.get("access_token") or "").strip()
    refresh_token = (token_resp.get("refresh_token") or "").strip()
    id_token = (token_resp.get("id_token") or "").strip()
    expires_in = _to_int(token_resp.get("expires_in"))
    claims = _jwt_claims_no_verify(id_token)
    email = str(claims.get("email") or "").strip()
    auth_claims = claims.get("https://api.openai.com/auth") or {}
    account_id = str(auth_claims.get("chatgpt_account_id") or "").strip()
    now = int(time.time())
    expired_rfc3339 = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime(now + max(expires_in, 0)))
    now_rfc3339 = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime(now))
    return json.dumps({
        "id_token": id_token, "access_token": access_token, "refresh_token": refresh_token,
        "account_id": account_id, "last_refresh": now_rfc3339, "email": email,
        "type": "codex", "expired": expired_rfc3339,
    }, ensure_ascii=False, separators=(",", ":"))


# ---------------------------------------------------------------------------
# APISession — curl_cffi based HTTP session with browser fingerprinting
# ---------------------------------------------------------------------------
@dataclass
class APIResponse:
    status: int
    text: str
    headers: Dict[str, str]

    def json(self) -> Dict[str, Any]:
        return json.loads(self.text)

    def ok(self) -> bool:
        return 200 <= self.status < 300


class APISession:
    def __init__(self, proxy: str = ""):
        requests = get_requests_module()
        profile, fp_headers = _pick_fingerprint()
        proxies = {"http": proxy, "https": proxy} if proxy else None
        self._session = requests.Session(proxies=proxies, impersonate=profile)
        self._session.headers.update(fp_headers)
        self._profile = profile
        log.info(f"    Browser fingerprint: {profile}")

    def get(self, url: str, **kwargs: Any) -> APIResponse:
        resp = self._session.get(url, timeout=30, **kwargs)
        return APIResponse(resp.status_code, resp.text, dict(resp.headers))

    def post_json(self, url: str, data: Dict[str, Any], headers: Optional[Dict[str, str]] = None) -> APIResponse:
        hdrs: Dict[str, str] = {"Content-Type": "application/json", "Accept": "application/json"}
        if headers:
            hdrs.update(headers)
        resp = self._session.post(url, data=json.dumps(data), headers=hdrs, timeout=30)
        return APIResponse(resp.status_code, resp.text, dict(resp.headers))

    def post_form(self, url: str, data: Dict[str, str]) -> APIResponse:
        hdrs = {"Content-Type": "application/x-www-form-urlencoded", "Accept": "application/json"}
        resp = self._session.post(url, data=urllib.parse.urlencode(data), headers=hdrs, timeout=30)
        return APIResponse(resp.status_code, resp.text, dict(resp.headers))

    def get_cookie(self, name: str) -> Optional[str]:
        return self._session.cookies.get(name)

    def follow_redirects(self, url: str, max_hops: int = 12) -> Optional[str]:
        for _ in range(max_hops):
            resp = self._session.get(url, allow_redirects=False, timeout=30)
            location = resp.headers.get("Location")
            if not location:
                return None
            if "localhost" in location and "/auth/callback" in location:
                return location
            url = location
        return None

    def close(self) -> None:
        self._session.close()

    def __enter__(self) -> "APISession":
        return self

    def __exit__(self, *a: Any) -> None:
        self.close()


# ---------------------------------------------------------------------------
# Core registration flow (pure API, no browser)
# ---------------------------------------------------------------------------
def register_account(
    email_addr: str,
    proxy: str = "",
    used_codes: Optional[Set[str]] = None,
    get_otp_fn: Optional[Callable[..., str]] = None,
    mail_account: Optional[MailAccount] = None,
    domain_mail: Optional[Dict[str, str]] = None,
) -> Dict[str, Any]:
    """Register or login an OpenAI account via pure API.

    Args:
        email_addr: Email to register with.
        proxy: HTTP proxy URL.
        used_codes: Set of already-used OTP codes.
        get_otp_fn: Callable(email, proxies) -> code for Mail.tm mode.
        mail_account: MailAccount for Outlook IMAP OTP retrieval.
        domain_mail: Domain catch-all IMAP config dict.
    """
    codes = used_codes or set()

    def _sleep(lo: float, hi: float) -> None:
        time.sleep(random.uniform(lo, hi))

    with APISession(proxy) as http:
        # 1. Initiate OAuth
        oauth = generate_oauth_url()
        log.info("  [1] Initiating OAuth...")
        resp = http.get(oauth.auth_url)
        log.info(f"      Status: {resp.status}")
        device_id = http.get_cookie("oai-did") or ""
        if device_id:
            log.info(f"      Device ID: {device_id[:16]}...")
        _sleep(0.8, 2.0)

        # 2. Get sentinel anti-bot token
        log.info("  [2] Getting sentinel token...")
        sentinel_resp = http.post_json(
            SENTINEL_URL,
            {"p": "", "id": device_id, "flow": "authorize_continue"},
            headers={
                "Origin": "https://sentinel.openai.com",
                "Referer": "https://sentinel.openai.com/backend-api/sentinel/frame.html",
            },
        )
        if not sentinel_resp.ok():
            raise RuntimeError(f"Sentinel failed: {sentinel_resp.status} {sentinel_resp.text[:200]}")
        sentinel_token = sentinel_resp.json()["token"]
        sentinel_header = json.dumps({
            "p": "", "t": "", "c": sentinel_token,
            "id": device_id, "flow": "authorize_continue",
        })
        log.info("      OK")
        _sleep(0.5, 1.5)

        # 3. Submit email (signup flow)
        otp_sent_at = time.time()
        log.info(f"  [3] Submitting email: {email_addr}")
        signup_resp = http.post_json(
            SIGNUP_URL,
            {"username": {"value": email_addr, "kind": "email"}, "screen_hint": "signup"},
            headers={
                "Referer": "https://auth.openai.com/create-account",
                "openai-sentinel-token": sentinel_header,
            },
        )
        if not signup_resp.ok():
            raise RuntimeError(f"Submit email failed: {signup_resp.status} {signup_resp.text[:300]}")
        log.info("      OK")

        # Detect if account already exists (OTP auto-sent)
        try:
            step3_data = signup_resp.json()
            page_type = step3_data.get("page", {}).get("type", "")
        except Exception:
            page_type = ""
        is_existing = page_type == "email_otp_verification"
        log.info(f"      Page type: {page_type or 'new_account'}")
        _sleep(0.5, 1.5)

        # 4. Send OTP (only for new accounts; existing accounts get it automatically)
        if is_existing:
            log.info("  [4] OTP already sent (existing account)")
        else:
            otp_sent_at = time.time()
            log.info("  [4] Sending OTP...")
            otp_resp = http.post_json(
                SEND_OTP_URL, {},
                headers={"Referer": "https://auth.openai.com/create-account/password"},
            )
            if not otp_resp.ok():
                raise RuntimeError(f"Send OTP failed: {otp_resp.status} {otp_resp.text[:300]}")
            log.info(f"      OTP sent to {email_addr}")

        # 5. Get OTP code
        def _resend_otp() -> bool:
            r = http.post_json(SEND_OTP_URL, {},
                               headers={"Referer": "https://auth.openai.com/email-verification"})
            return r.ok()

        if mail_account or domain_mail:
            # Outlook IMAP or domain catch-all
            imap_account = mail_account or MailAccount(email=email_addr, password="")
            code = poll_verification_code_imap(
                imap_account, used_codes=codes, resend_fn=_resend_otp,
                otp_sent_at=otp_sent_at, domain_mail=domain_mail,
            )
        elif get_otp_fn:
            # Mail.tm polling
            code = get_otp_fn(email_addr)
            if not code:
                raise RuntimeError("Failed to get OTP from Mail.tm")
        else:
            raise RuntimeError("No OTP retrieval method available")
        _sleep(0.3, 1.0)

        # 6. Verify OTP
        log.info(f"  [6] Verifying OTP: {code}")
        verify_resp = http.post_json(
            VERIFY_OTP_URL, {"code": code},
            headers={"Referer": "https://auth.openai.com/email-verification"},
        )
        if not verify_resp.ok():
            raise RuntimeError(f"OTP verify failed: {verify_resp.status} {verify_resp.text[:300]}")
        log.info("      OK")
        _sleep(0.5, 1.5)

        # 7. Create account (skip for existing)
        name = ""
        if is_existing:
            log.info("  [7] Skipped (account exists)")
        else:
            name = random_name()
            birthday = random_birthday()
            log.info(f"  [7] Creating account: {name}, {birthday}")
            create_resp = http.post_json(
                CREATE_ACCOUNT_URL,
                {"name": name, "birthdate": birthday},
                headers={"Referer": "https://auth.openai.com/about-you"},
            )
            if not create_resp.ok():
                raise RuntimeError(f"Create account failed: {create_resp.status} {create_resp.text[:300]}")
            log.info("      OK")
            _sleep(0.5, 1.5)

        # 8. Select workspace
        auth_cookie = http.get_cookie("oai-client-auth-session")
        if not auth_cookie:
            raise RuntimeError("Missing oai-client-auth-session cookie")
        try:
            cookie_b64 = auth_cookie.split(".")[0]
            padding = "=" * ((4 - len(cookie_b64) % 4) % 4)
            cookie_data = json.loads(base64.b64decode(cookie_b64 + padding))
            workspaces = cookie_data.get("workspaces", [])
            workspace_id = workspaces[0]["id"] if workspaces else None
        except Exception as e:
            raise RuntimeError(f"Parse workspace failed: {e}")
        if not workspace_id:
            raise RuntimeError("No workspace_id found")

        log.info(f"  [8] Selecting workspace: {workspace_id[:20]}...")
        select_resp = http.post_json(
            WORKSPACE_SELECT_URL,
            {"workspace_id": workspace_id},
            headers={"Referer": "https://auth.openai.com/sign-in-with-chatgpt/codex/consent"},
        )
        if not select_resp.ok():
            raise RuntimeError(f"Workspace select failed: {select_resp.status}")
        continue_url = select_resp.json().get("continue_url")
        if not continue_url:
            raise RuntimeError("Missing continue_url")

        # 9. Follow redirects to get token
        log.info("  [9] Following redirects for token...")
        callback_url = http.follow_redirects(continue_url)
        if not callback_url:
            raise RuntimeError("Redirect chain failed, no callback URL")

        parsed = urllib.parse.urlparse(callback_url)
        query = urllib.parse.parse_qs(parsed.query)
        auth_code = query.get("code", [""])[0]
        returned_state = query.get("state", [""])[0]
        if not auth_code:
            raise RuntimeError("Callback URL missing code")
        if returned_state != oauth.state:
            raise RuntimeError("State mismatch")

        token_resp = http.post_form(TOKEN_URL, {
            "grant_type": "authorization_code",
            "client_id": CLIENT_ID,
            "code": auth_code,
            "redirect_uri": oauth.redirect_uri,
            "code_verifier": oauth.code_verifier,
        })
        if not token_resp.ok():
            raise RuntimeError(f"Token exchange failed: {token_resp.status} {token_resp.text[:300]}")
        token_data = token_resp.json()

        claims = _jwt_claims_no_verify(token_data.get("id_token", ""))
        auth_claims = claims.get("https://api.openai.com/auth", {})
        now = int(time.time())
        result = {
            "email": email_addr,
            "type": "codex",
            "name": name or claims.get("name", ""),
            "access_token": token_data.get("access_token", ""),
            "refresh_token": token_data.get("refresh_token", ""),
            "id_token": token_data.get("id_token", ""),
            "account_id": auth_claims.get("chatgpt_account_id", ""),
            "expired": time.strftime("%Y-%m-%dT%H:%M:%SZ",
                                     time.gmtime(now + int(token_data.get("expires_in", 0)))),
            "last_refresh": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime(now)),
        }
        log.info("  Registration successful!")
        return result


# ---------------------------------------------------------------------------
# Legacy run() — kept for backward compatibility with subprocess invocation
# ---------------------------------------------------------------------------
def run(proxy: Optional[str]) -> Optional[str]:
    requests = get_requests_module()
    proxies: Any = None
    if proxy:
        proxies = {"http": proxy, "https": proxy}

    # Network check
    try:
        session = requests.Session(proxies=proxies, impersonate="chrome")
        trace = session.get("https://cloudflare.com/cdn-cgi/trace", timeout=10).text
        loc_match = re.search(r"^loc=(.+)$", trace, re.MULTILINE)
        loc = loc_match.group(1) if loc_match else None
        log.info(f"IP location: {loc}")
        session.close()
        if loc == "CN":
            raise RuntimeError("Location not supported - check proxy")
    except Exception as exc:
        log.error(f"Network check failed: {exc}")
        return None

    email, dev_token = get_email_and_token(proxies)
    if not email or not dev_token:
        return None
    log.info(f"Mail.tm email acquired: {email}")

    def _get_otp(email_addr: str) -> str:
        return get_oai_code(dev_token, email_addr, proxies)

    try:
        result = register_account(email, proxy=proxy or "", get_otp_fn=_get_otp)
        return json.dumps(result, ensure_ascii=False, separators=(",", ":"))
    except Exception as exc:
        log.error(f"Registration failed: {exc}")
        return None


# ---------------------------------------------------------------------------
# Single registration task with retry (thread-safe)
# ---------------------------------------------------------------------------
def _do_one_registration(
    idx: int,
    total: int,
    proxy: str,
    stats: Dict[str, int],
    lock: threading.Lock,
    tokens_dir: Path,
    mail_account: Optional[MailAccount] = None,
    domain_mail: Optional[Dict[str, str]] = None,
    delay: float = 0,
) -> None:
    if delay > 0:
        time.sleep(delay)

    proxies: Any = {"http": proxy, "https": proxy} if proxy else None

    # Determine email source
    if mail_account:
        email_addr = mail_account.email
        log.info(f"\n{'─'*50}")
        log.info(f"[{idx}/{total}] {email_addr} (Outlook IMAP)")
        log.info(f"{'─'*50}")
    else:
        email_addr = None  # Will be generated by Mail.tm

    used = set()
    start_t = time.time()

    for attempt in range(1, MAX_RETRY_PER_ACCOUNT + 1):
        if attempt > 1:
            log.info(f"  Retry #{attempt}...")
            time.sleep(random.uniform(2, 5))
        try:
            if mail_account:
                result = register_account(
                    email_addr, proxy=proxy, used_codes=used,
                    mail_account=mail_account, domain_mail=domain_mail,
                )
            else:
                # Mail.tm mode: get a new disposable email
                email, dev_token = get_email_and_token(proxies)
                if not email or not dev_token:
                    raise RuntimeError("Failed to get Mail.tm email")
                email_addr = email

                if idx == 1 or not hasattr(_do_one_registration, "_logged_email"):
                    log.info(f"\n{'─'*50}")
                    log.info(f"[{idx}/{total}] {email_addr} (Mail.tm)")
                    log.info(f"{'─'*50}")
                    _do_one_registration._logged_email = True

                def _get_otp(addr: str) -> str:
                    return get_oai_code(dev_token, addr, proxies)

                result = register_account(email_addr, proxy=proxy, used_codes=used, get_otp_fn=_get_otp)

            elapsed = round(time.time() - start_t, 1)
            result["elapsed_seconds"] = elapsed

            tokens_dir.mkdir(parents=True, exist_ok=True)
            fpath = tokens_dir / f"{_sanitize_filename_component(email_addr or 'unknown')}_{int(time.time())}.json"
            with fpath.open("w", encoding="utf-8") as f:
                json.dump(result, f, indent=2, ensure_ascii=False)

            with lock:
                stats["ok"] += 1
            record_result(True)
            log.info(f"  Saved: {fpath} ({elapsed}s)")
            return

        except Exception as e:
            log.warning(f"  Attempt {attempt} failed: {type(e).__name__}: {str(e)[:150]}")

    with lock:
        stats["fail"] += 1
    record_result(False)


def run_auto_register_cli(*, proxy: Optional[str], once: bool, sleep_min: int, sleep_max: int,
                          tokens_dir: Path, workers: int = 1,
                          outlook_accounts: Optional[List[MailAccount]] = None,
                          domain_mail: Optional[Dict[str, str]] = None) -> None:
    sleep_min = max(1, sleep_min)
    sleep_max = max(sleep_min, sleep_max)
    workers = max(1, workers)
    count = 0
    log.info("Codex Auto-Registrar started")
    log.info(f"  Workers: {workers}, Proxy: {proxy or 'none'}")
    while True:
        if should_pause_for_failures():
            log.warning("High failure rate detected, pausing 60s...")
            time.sleep(60)
            continue

        count += 1
        log.info(f"\n[{datetime.now().strftime('%H:%M:%S')}] === Batch #{count} ===")

        if outlook_accounts:
            # IMAP mode: register each account
            tasks = outlook_accounts
            total = len(tasks)
            stats: Dict[str, int] = {"ok": 0, "fail": 0}
            lock = threading.Lock()

            if workers > 1 and total > 1:
                pool = concurrent.futures.ThreadPoolExecutor(max_workers=min(workers, total))
                try:
                    futures = []
                    for i, acct in enumerate(tasks, 1):
                        delay = random.uniform(0.5, 3.0) * (i - 1) if i > 1 else 0
                        futures.append(pool.submit(
                            _do_one_registration, i, total, proxy or "", stats, lock,
                            tokens_dir, mail_account=acct, domain_mail=domain_mail, delay=delay,
                        ))
                    concurrent.futures.wait(futures)
                finally:
                    pool.shutdown(wait=True)
            else:
                for i, acct in enumerate(tasks, 1):
                    _do_one_registration(i, total, proxy or "", stats, lock,
                                         tokens_dir, mail_account=acct, domain_mail=domain_mail)
            log.info(f"Batch #{count} complete: {stats['ok']} ok, {stats['fail']} fail")
        else:
            # Mail.tm mode: single registration per cycle
            stats = {"ok": 0, "fail": 0}
            lock = threading.Lock()
            _do_one_registration(1, 1, proxy or "", stats, lock, tokens_dir)
            if stats["ok"]:
                log.info(f"Batch #{count} complete: success")
            else:
                log.info(f"Batch #{count} complete: failed")

        if once:
            break
        wait_time = random.randint(sleep_min, sleep_max)
        log.info(f"Sleeping {wait_time}s...")
        time.sleep(wait_time)


def create_db_connection():
    psycopg2 = importlib.import_module("psycopg2")

    host = get_env("POSTGRES_HOST", "postgres")
    port = int(get_env("POSTGRES_PORT", "5432"))
    connect_timeout = int(get_env("POSTGRES_CONNECT_TIMEOUT", "5"))
    user = get_env("POSTGRES_USER", required=True)
    password = get_env("POSTGRES_PASSWORD", required=True)
    dbname = get_env("POSTGRES_DB", required=True)

    conn = psycopg2.connect(
        host=host,
        port=port,
        user=user,
        password=password,
        dbname=dbname,
        connect_timeout=connect_timeout,
    )
    conn.autocommit = True
    return conn


def pg_json(value):
    Json = importlib.import_module("psycopg2.extras").Json

    return Json(value)


def normalize_extra_for_compare(extra: JSONDict) -> JSONDict:
    normalized = ensure_dict(extra)
    normalized.pop("codex_auto_register_updated_at", None)
    return normalized


def should_update_account(
    current_credentials: JSONDict,
    next_credentials: JSONDict,
    current_extra: JSONDict,
    next_extra: JSONDict,
) -> bool:
    return (
        current_credentials != next_credentials
        or normalize_extra_for_compare(current_extra) != normalize_extra_for_compare(next_extra)
    )


def archive_processed_file(source: Path, processed_dir: Path) -> Path:
    if not source.exists():
        raise FileNotFoundError(f"source token file not found: {source}")
    processed_dir.mkdir(parents=True, exist_ok=True)
    target = processed_dir / source.name
    while target.exists():
        target = processed_dir / f"{int(time.time() * 1000)}-{source.name}"
    shutil.move(str(source), str(target))
    return target


def compute_group_binding_changes(current_group_ids: Set[int], next_group_ids: Set[int]) -> Tuple[Set[int], Set[int]]:
    return next_group_ids - current_group_ids, current_group_ids - next_group_ids


def run_codex_once(tokens_dir: Path) -> List[Tuple[Path, List[JSONDict]]]:
    service_file = Path(__file__).resolve()
    tokens_dir.mkdir(parents=True, exist_ok=True)

    proxy = get_env("CODEX_PROXY", "")
    cmd = [sys.executable, str(service_file), "--register-only", "--once", "--tokens-dir", str(tokens_dir)]
    if proxy:
        cmd.extend(["--proxy", proxy])

    print("[codex-register] 启动注册脚本:", " ".join(cmd), flush=True)

    result = subprocess.run(
        cmd,
        cwd=str(service_file.parent),
        capture_output=True,
        text=True,
    )

    print("[codex-register] stdout:\n" + (result.stdout or ""), flush=True)
    if result.stderr:
        print("[codex-register] stderr:\n" + result.stderr, flush=True)

    if result.returncode != 0:
        print(f"[codex-register] 注册脚本退出码非 0: {result.returncode}", flush=True)
        append_log("error", f"script_exit_nonzero:{result.returncode}")
        return []

    json_files = sorted(tokens_dir.glob("*.json"), key=lambda p: p.stat().st_mtime, reverse=True)
    if not json_files:
        print("[codex-register] 未找到新的 token JSON 文件", flush=True)
        append_log("warn", "no_token_json_found")
        return []

    batches: List[Tuple[Path, List[JSONDict]]] = []
    for json_file in json_files:
        try:
            data = json.loads(json_file.read_text(encoding="utf-8"))
        except Exception as exc:  # noqa: BLE001
            print(f"[codex-register] 解析 token JSON 失败: {exc}", flush=True)
            append_log("error", f"token_json_parse_failed:{json_file.name}")
            continue

        token_infos: List[JSONDict] = []
        if isinstance(data, list):
            token_infos.extend(item for item in data if isinstance(item, dict))
        elif isinstance(data, dict):
            token_infos.append(data)
        print(f"[codex-register] 读取 token 文件: {json_file}", flush=True)
        batches.append((json_file, token_infos))

    return batches


def get_existing_account(cur, email: str, account_id: str):
    conditions = []
    params = []
    if email:
        conditions.append("credentials ->> 'email' = %s")
        params.append(email)
    if account_id:
        conditions.append("credentials ->> 'account_id' = %s")
        params.append(account_id)
    if not conditions:
        return None
    cur.execute(
        "SELECT id, name, credentials, extra FROM accounts WHERE platform = 'openai' AND type = 'oauth' "
        f"AND ({' OR '.join(conditions)}) ORDER BY id LIMIT 1",
        tuple(params),
    )
    return cur.fetchone()


def bind_groups(cur, account_id: int, group_ids: List[int]) -> None:
    if not group_ids:
        return

    desired_priority = {group_id: index for index, group_id in enumerate(group_ids, start=1)}
    desired_ids = set(desired_priority.keys())

    cur.execute("SELECT group_id, priority FROM account_groups WHERE account_id = %s", (account_id,))
    current_rows = cur.fetchall()
    current_priority = {int(row[0]): int(row[1]) for row in current_rows}
    current_ids = set(current_priority.keys())

    to_add, to_remove = compute_group_binding_changes(current_ids, desired_ids)

    for group_id in to_remove:
        cur.execute("DELETE FROM account_groups WHERE account_id = %s AND group_id = %s", (account_id, group_id))

    for group_id in to_add:
        cur.execute(
            "INSERT INTO account_groups (account_id, group_id, priority, created_at) VALUES (%s, %s, %s, NOW()) "
            "ON CONFLICT (account_id, group_id) DO UPDATE SET priority = EXCLUDED.priority",
            (account_id, group_id, desired_priority[group_id]),
        )

    retained_ids = desired_ids.intersection(current_ids)
    for group_id in retained_ids:
        next_priority = desired_priority[group_id]
        if current_priority[group_id] != next_priority:
            cur.execute(
                "UPDATE account_groups SET priority = %s WHERE account_id = %s AND group_id = %s",
                (next_priority, account_id, group_id),
            )


def build_credentials(existing: JSONDict, token_info: JSONDict) -> JSONDict:
    credentials = dict(existing)
    credentials["access_token"] = token_info.get("access_token") or credentials.get("access_token") or ""
    credentials["refresh_token"] = token_info.get("refresh_token") or credentials.get("refresh_token") or ""
    credentials["id_token"] = token_info.get("id_token") or credentials.get("id_token") or ""
    if token_info.get("email"):
        credentials["email"] = token_info.get("email")
    if token_info.get("account_id"):
        credentials["account_id"] = token_info.get("account_id")
        credentials["chatgpt_account_id"] = token_info.get("account_id")
    if token_info.get("expired") is not None:
        credentials["expires_at"] = token_info.get("expired")
    credentials["source"] = "codex-auto-register"
    credentials["model_mapping"] = build_model_mapping()
    if token_info.get("auth_file"):
        credentials["codex_auth_file"] = token_info.get("auth_file")
    return credentials


def build_extra(existing: JSONDict, token_info: JSONDict) -> JSONDict:
    extra = dict(existing)
    extra["codex_auto_register"] = True
    extra["codex_auto_register_model_mapping"] = build_model_mapping()
    if token_info.get("auth_file"):
        extra["codex_auth_file"] = token_info.get("auth_file")
    return extra


def upsert_account(cur, token_info: JSONDict) -> str:
    email = token_info.get("email") or ""
    account_id = token_info.get("account_id") or ""
    if not email and not account_id:
        print("[codex-register] token 中缺少 email/account_id，跳过", flush=True)
        append_log("warn", "skip_missing_email_and_account_id")
        return "skipped"

    existing = get_existing_account(cur, email, account_id)
    group_ids = parse_group_ids()
    if existing is not None:
        existing_id, _existing_name, existing_credentials, existing_extra = existing
        credentials = build_credentials(ensure_dict(existing_credentials), token_info)
        extra = build_extra(ensure_dict(existing_extra), token_info)
        current_credentials = ensure_dict(existing_credentials)
        current_extra = ensure_dict(existing_extra)
        if not should_update_account(current_credentials, credentials, current_extra, extra):
            bind_groups(cur, existing_id, group_ids)
            print(f"[codex-register] 账号无需更新，跳过: {email or account_id}", flush=True)
            append_log("info", f"skip_unchanged:{email or account_id}")
            return "skipped"

        extra["codex_auto_register_updated_at"] = datetime.utcnow().isoformat() + "Z"
        cur.execute(
            "UPDATE accounts SET credentials = %s, extra = %s, status = 'active', schedulable = true, updated_at = NOW() WHERE id = %s",
            (pg_json(credentials), pg_json(extra), existing_id),
        )
        bind_groups(cur, existing_id, group_ids)
        print(f"[codex-register] 已更新账号: {email or account_id}", flush=True)
        append_log("info", f"updated:{email or account_id}")
        return "updated"

    identifier = email or account_id
    name = f"codex-{identifier}"
    credentials = build_credentials({}, token_info)
    extra = build_extra({}, token_info)
    extra["codex_auto_register_updated_at"] = datetime.utcnow().isoformat() + "Z"

    cur.execute(
        "INSERT INTO accounts (name, platform, type, credentials, extra, concurrency, priority, rate_multiplier, status, schedulable, auto_pause_on_expired) "
        "VALUES (%s, 'openai', 'oauth', %s, %s, 3, 50, 1.0, 'active', true, true) RETURNING id",
        (name, pg_json(credentials), pg_json(extra)),
    )
    created_id = cur.fetchone()[0]
    bind_groups(cur, created_id, group_ids)
    print(f"[codex-register] 已插入新账号: {identifier}", flush=True)
    append_log("info", f"created:{identifier}")
    return "created"


def run_one_cycle(tokens_dir: Path) -> None:
    global last_run, last_success, last_error, total_created, total_updated, total_skipped
    global last_token_email, last_created_email, last_created_account_id, last_updated_email, last_updated_account_id
    global last_processed_records
    with status_lock:
        last_run = datetime.utcnow()
    try:
        conn = create_db_connection()
        cur = conn.cursor()
        print("[codex-register] 数据库连接成功", flush=True)
    except Exception as exc:  # noqa: BLE001
        last_error = traceback.format_exc()
        append_log("error", f"db_connect_failed:{exc}")
        print(f"[codex-register] 数据库连接失败，将在 10 秒后重试: {last_error}", flush=True)
        time.sleep(10)
        return

    try:
        batches = run_codex_once(tokens_dir)
        with status_lock:
            last_processed_records = sum(len(items) for _, items in batches)
        if batches:
            processed_dir = tokens_dir / "processed"
            for source_file, token_infos in batches:
                file_success = True
                for token_info in token_infos:
                    try:
                        identifier = token_info.get("email") or token_info.get("account_id") or token_info.get("name") or ""
                        if identifier:
                            with status_lock:
                                last_token_email = identifier
                        action = upsert_account(cur, token_info)
                        if action == "created":
                            with status_lock:
                                total_created += 1
                                last_created_email = token_info.get("email") or ""
                                last_created_account_id = token_info.get("account_id") or ""
                        elif action == "updated":
                            with status_lock:
                                total_updated += 1
                                last_updated_email = token_info.get("email") or ""
                                last_updated_account_id = token_info.get("account_id") or ""
                        else:
                            with status_lock:
                                total_skipped += 1
                    except Exception as exc:  # noqa: BLE001
                        file_success = False
                        append_log("error", f"token_process_failed:{source_file.name}:{exc}")
                        print(f"[codex-register] 处理 token 失败（保留重试）: {source_file} {exc}", flush=True)
                        break

                if file_success:
                    try:
                        archived = archive_processed_file(source_file, processed_dir)
                        append_log("info", f"archived:{archived.name}")
                    except Exception as exc:  # noqa: BLE001
                        append_log("error", f"archive_failed:{source_file.name}:{exc}")
                        print(f"[codex-register] 归档 token 文件失败（保留重试）: {source_file} {exc}", flush=True)
            with status_lock:
                last_success = datetime.utcnow()
                last_error = ""
            append_log("info", f"cycle_completed:{last_processed_records}")
        else:
            append_log("info", "cycle_completed:0")
    except Exception:  # noqa: BLE001
        last_error = traceback.format_exc()
        append_log("error", "process_error")
        print(f"[codex-register] 处理流程异常: {last_error}", flush=True)
    finally:
        try:
            cur.close()
        except Exception:  # noqa: BLE001
            pass
        try:
            conn.close()
        except Exception:  # noqa: BLE001
            pass


def worker_loop(tokens_dir: Path, sleep_min: int, sleep_max: int) -> None:
    while True:
        with status_lock:
            worker_enabled = enabled
        if not worker_enabled:
            time.sleep(5)
            continue
        if should_pause_for_failures():
            log.warning("High failure rate — pausing worker for 60s")
            time.sleep(60)
            continue
        run_one_cycle(tokens_dir)
        sleep_seconds = random.randint(sleep_min, sleep_max)
        log.info(f"Worker sleeping {sleep_seconds}s")
        time.sleep(sleep_seconds)


def get_status_payload() -> JSONDict:
    proxy = get_env("CODEX_PROXY", "")
    with status_lock:
        return {
            "enabled": enabled,
            "sleep_min": sleep_min_global,
            "sleep_max": sleep_max_global,
            "total_created": total_created,
            "total_updated": total_updated,
            "total_skipped": total_skipped,
            "total_failed": total_failed,
            "last_run": last_run.isoformat() + "Z" if last_run else None,
            "last_success": last_success.isoformat() + "Z" if last_success else None,
            "last_error": last_error,
            "proxy": bool(proxy),
            "last_token_email": last_token_email or None,
            "last_created_email": last_created_email or None,
            "last_created_account_id": last_created_account_id or None,
            "last_updated_email": last_updated_email or None,
            "last_updated_account_id": last_updated_account_id or None,
            "last_processed_records": last_processed_records,
        }


class CodexRequestHandler(BaseHTTPRequestHandler):
    def _cors_headers(self) -> None:
        self.send_header("Access-Control-Allow-Origin", "*")
        self.send_header("Access-Control-Allow-Methods", "GET, POST, OPTIONS")
        self.send_header("Access-Control-Allow-Headers", "Content-Type")

    def do_OPTIONS(self) -> None:  # noqa: N802
        self.send_response(204)
        self._cors_headers()
        self.end_headers()

    def do_GET(self) -> None:  # noqa: N802
        if self.path == "/status":
            body = json.dumps(get_status_payload()).encode("utf-8")
            self.send_response(200)
            self._cors_headers()
            self.send_header("Content-Type", "application/json")
            self.end_headers()
            self.wfile.write(body)
            return
        if self.path == "/logs":
            with status_lock:
                logs = list(recent_logs)
            body = json.dumps({"logs": logs}).encode("utf-8")
            self.send_response(200)
            self._cors_headers()
            self.send_header("Content-Type", "application/json")
            self.end_headers()
            self.wfile.write(body)
            return
        if self.path == "/health":
            body = json.dumps({"ok": True}).encode("utf-8")
            self.send_response(200)
            self._cors_headers()
            self.send_header("Content-Type", "application/json")
            self.end_headers()
            self.wfile.write(body)
            return

        self.send_response(404)
        self._cors_headers()
        self.send_header("Content-Type", "application/json")
        self.end_headers()
        self.wfile.write(b'{"error":"not_found"}')

    def do_POST(self) -> None:  # noqa: N802
        global enabled, tokens_dir_global
        if self.path == "/enable":
            with status_lock:
                enabled = True
            body = json.dumps(get_status_payload()).encode("utf-8")
            self.send_response(200)
            self._cors_headers()
            self.send_header("Content-Type", "application/json")
            self.end_headers()
            self.wfile.write(body)
            return
        if self.path == "/disable":
            with status_lock:
                enabled = False
            body = json.dumps(get_status_payload()).encode("utf-8")
            self.send_response(200)
            self._cors_headers()
            self.send_header("Content-Type", "application/json")
            self.end_headers()
            self.wfile.write(body)
            return
        if self.path == "/run-once":
            with status_lock:
                run_once_tokens_dir = tokens_dir_global
            if run_once_tokens_dir is not None:
                run_one_cycle(run_once_tokens_dir)
            body = json.dumps(get_status_payload()).encode("utf-8")
            self.send_response(200)
            self._cors_headers()
            self.send_header("Content-Type", "application/json")
            self.end_headers()
            self.wfile.write(body)
            return

        self.send_response(404)
        self._cors_headers()
        self.send_header("Content-Type", "application/json")
        self.end_headers()
        self.wfile.write(b'{"error":"not_found"}')


def main() -> None:
    parser = argparse.ArgumentParser(description="Codex register service")
    parser.add_argument("--register-only", action="store_true", help="run the embedded OpenAI register flow only")
    parser.add_argument("--proxy", default=None, help="proxy URL, e.g. http://127.0.0.1:7890")
    parser.add_argument("--once", action="store_true", help="run one cycle then exit")
    parser.add_argument("--sleep-min", type=int, default=5, help="minimum sleep seconds between cycles")
    parser.add_argument("--sleep-max", type=int, default=30, help="maximum sleep seconds between cycles")
    parser.add_argument("--tokens-dir", default="", help="token output directory")
    parser.add_argument("--workers", type=int, default=1, help="concurrent registration workers")
    parser.add_argument("--outlook-accounts", default="", help="path to outlook accounts file (email:password per line)")
    args = parser.parse_args()

    if args.register_only:
        tokens_dir = Path(args.tokens_dir).expanduser() if args.tokens_dir else Path(__file__).resolve().parent / "tokens"
        outlook_accounts = None
        if args.outlook_accounts:
            outlook_accounts = load_accounts_file(args.outlook_accounts)
        run_auto_register_cli(
            proxy=args.proxy,
            once=args.once,
            sleep_min=args.sleep_min,
            sleep_max=args.sleep_max,
            tokens_dir=tokens_dir,
            workers=args.workers,
            outlook_accounts=outlook_accounts,
        )
        return

    global sleep_min_global, sleep_max_global, tokens_dir_global
    sleep_min = int(get_env("CODEX_SLEEP_MIN", "5"))
    sleep_max = int(get_env("CODEX_SLEEP_MAX", "30"))
    if sleep_min < 1:
        sleep_min = 1
    if sleep_max < sleep_min:
        sleep_max = sleep_min

    with status_lock:
        sleep_min_global = sleep_min
        sleep_max_global = sleep_max

    tokens_dir = Path(__file__).resolve().parent / "tokens"
    with status_lock:
        tokens_dir_global = tokens_dir

    worker = threading.Thread(target=worker_loop, args=(tokens_dir, sleep_min, sleep_max), daemon=True)
    worker.start()

    port = int(get_env("CODEX_HTTP_PORT", "5000"))
    server = ThreadingHTTPServer(("0.0.0.0", port), CodexRequestHandler)
    print(f"[codex-register] HTTP 服务启动于 0.0.0.0:{port}", flush=True)
    server.serve_forever()


if __name__ == "__main__":
    main()
