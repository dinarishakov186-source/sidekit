#!/usr/bin/env python3
"""
SideKit - local server + GUI for installing .ipa files on your own iOS
device without the App Store.

Everything here uses only the Python standard library for the server/GUI
layer itself, so it can run before any extra dependency is installed. It
shells out to two well-known open-source tools for the actual work:

  - ipatool         (github.com/majd/ipatool)      Apple ID login + App
                                                     Store search/download.
  - pymobiledevice3  (pypi.org/project/pymobiledevice3)  talks to the
                                                     device over USB.
  - zsign            (github.com/zhlynn/zsign)      re-signs .ipa files
                                                     that did NOT come from
                                                     the App Store.

On first run, SideKit offers to fetch/install whatever is missing by
itself (no Terminal needed): pymobiledevice3 via pip, ipatool/zsign as
prebuilt binaries from their GitHub releases.
"""

# Must come before anything else: makes `str | None`-style type hints safe
# to parse on the older Python 3.9 that Apple still ships with the Command
# Line Tools on many Macs (without this, the whole file fails to even
# import there, which is exactly why the app was closing instantly).
from __future__ import annotations

import ctypes
import difflib
import json
import locale
import os
import platform
import re
import shutil
import signal
import struct
import subprocess
import sys
import tarfile
import tempfile
import threading
import time
import traceback
import urllib.error
import urllib.request
import webbrowser
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path

def _resources_dir() -> Path:
    """Папка программы: там лежат ipatool, zsign, значок и родное окно.
    Обновлённый движок работает из отдельной папки обновлений, и искать
    соседей рядом с собой ему нельзя - их там нет. Настоящий адрес приходит
    в переменной SIDEKIT_HOME, а если её нет - берём привычные места."""
    told = os.environ.get("SIDEKIT_HOME")
    if told and Path(told).is_dir():
        return Path(told)
    here = Path(__file__).resolve().parent
    if (here / "bin").is_dir() or (here / "index.html").exists():
        return here
    for known in (Path("/Applications/SideKit.app/Contents/Resources"),
                  Path(os.environ.get("LOCALAPPDATA", "")) / "SideKit"):
        if (known / "index.html").exists():
            return known
    return here


RESOURCES_DIR = _resources_dir()
BIN_DIR = RESOURCES_DIR / "bin"
DOWNLOADS_DIR = Path.home() / "Downloads" / "SideKit"
INDEX_HTML = RESOURCES_DIR / "index.html"
USER_AGENT = "SideKit-app (+https://github.com)"
# Windows has no ~/Library; every platform difference below hangs off these
# two flags rather than scattering checks through the code.
IS_MAC = sys.platform == "darwin"
IS_WINDOWS = os.name == "nt"

LOCK_DIR = (Path(os.environ.get("APPDATA", Path.home())) / "SideKit" if IS_WINDOWS
            else Path.home() / "Library" / "Application Support" / "SideKit")

# Every external tool SideKit runs (ipatool, pymobiledevice3) is a console
# program. On Windows that means a black window for each call - a flicker for
# short ones, a window that sits there for the whole length of a download.
# This flag starts them with no console attached at all.
NO_CONSOLE = {"creationflags": subprocess.CREATE_NO_WINDOW} if IS_WINDOWS else {}

# pythonw.exe (которым запускается программа на Windows, чтобы не было консоли)
# не имеет stdout - подпроцессы через него возвращают пустоту, и сбор App Store
# ID молча не работал. Для дочерних процессов нужен обычный python.exe.
PYTHON_EXE = sys.executable
if IS_WINDOWS and PYTHON_EXE.lower().endswith("pythonw.exe"):
    _console_python = Path(PYTHON_EXE).with_name("python.exe")
    if _console_python.exists():
        PYTHON_EXE = str(_console_python)
LOCK_FILE = LOCK_DIR / "server.lock"

# Bump this any time server.py changes in a way that matters. It's how a
# new launch knows an already-running background server is stale (from an
# older download) rather than a legitimate already-running copy of itself,
# so it doesn't keep re-attaching to old, already-fixed-elsewhere code
# forever. Closing the browser tab does NOT stop the Python process behind
# it, so without this check a months-old process could quietly keep
# serving every future double-click of a newly downloaded SideKit.app.
SERVER_VERSION = "2026-08-07.65-report-bg"


# ---------------------------------------------------------------------------
# single-instance guard - if SideKit gets opened twice (e.g. double-clicked
# again while it's already running), the second launch should just open a
# browser tab pointing at the FIRST instance instead of starting a second
# server. Two servers each trying to `pip install` at the same time is
# exactly what makes setup look like it's hanging forever (pip serializes
# on a lock file, so the second install just waits on the first one).
# ---------------------------------------------------------------------------

def find_existing_instance_url() -> str | None:
    try:
        if not LOCK_FILE.exists():
            return None
        data = json.loads(LOCK_FILE.read_text(encoding="utf-8"))
        port = data.get("port")
        if not port or data.get("version") != SERVER_VERSION:
            return None
        req = urllib.request.Request(f"http://127.0.0.1:{port}/api/status")
        with urllib.request.urlopen(req, timeout=1.5) as r:
            if r.status == 200:
                return f"http://127.0.0.1:{port}/"
    except Exception:
        pass
    return None


def shut_down_stale_instance() -> None:
    """Best-effort: if an older-version SideKit server is still running in
    the background, ask it to exit so it stops serving stale code and
    doesn't sit around contending for pip/download locks."""
    try:
        if not LOCK_FILE.exists():
            return
        data = json.loads(LOCK_FILE.read_text(encoding="utf-8"))
        port = data.get("port")
        if not port:
            return
        req = urllib.request.Request(f"http://127.0.0.1:{port}/api/shutdown", method="POST")
        urllib.request.urlopen(req, timeout=1.5)
    except Exception:
        pass


def write_lock(port: int) -> None:
    try:
        LOCK_DIR.mkdir(parents=True, exist_ok=True)
        LOCK_FILE.write_text(json.dumps({"port": port, "pid": os.getpid(), "version": SERVER_VERSION}), encoding="utf-8")
    except Exception:
        pass


def remove_lock() -> None:
    """Deletes the lock only if it still describes THIS process. An older
    instance shutting down a moment after a newer one has started would
    otherwise erase the newcomer's entry, leaving a running server that
    nothing can find - so the next launch starts a second one alongside it."""
    try:
        data = json.loads(LOCK_FILE.read_text(encoding="utf-8"))
        if data.get("pid") != os.getpid():
            return
    except Exception:
        return
    try:
        LOCK_FILE.unlink(missing_ok=True)
    except Exception:
        pass


# ---------------------------------------------------------------------------
# tool discovery
# ---------------------------------------------------------------------------

def _macho_arch(path: Path) -> str | None:
    """Reads a Mach-O binary's CPU type directly from its header, so a
    bundled binary built for the wrong Mac architecture (e.g. an arm64
    binary shipped for an Intel Mac) never gets silently invoked - it would
    just fail with 'Bad CPU type in executable' at run time otherwise."""
    try:
        with open(path, "rb") as f:
            magic = f.read(4)
            if magic == b"\xcf\xfa\xed\xfe":
                cputype = struct.unpack("<i", f.read(4))[0]
            elif magic == b"\xfe\xed\xfa\xcf":
                cputype = struct.unpack(">i", f.read(4))[0]
            else:
                return None
        if cputype == 0x0100000C:
            return "arm64"
        if cputype == 0x01000007:
            return "x86_64"
        return None
    except Exception:
        return None


def find_tool(name: str) -> str | None:
    if IS_WINDOWS and not name.endswith(".exe"):
        name += ".exe"
    bundled = BIN_DIR / name
    if bundled.exists() and os.access(bundled, os.X_OK):
        arch = None if IS_WINDOWS else _macho_arch(bundled)
        if arch is None or arch == machine_arch():
            return str(bundled)
        # wrong-architecture binary bundled in the app - ignore it, let the
        # caller fall back to PATH / a fresh download for the right arch.
    return shutil.which(name)


def has_pymobiledevice3() -> bool:
    try:
        # Import something deep enough to actually exercise the compiled
        # dependencies (cryptography's Rust extension in particular) - a
        # bare `import pymobiledevice3` can succeed even when the install
        # is broken (e.g. wrong-architecture wheel), since the failure
        # only happens once lockdown.py is actually loaded.
        result = subprocess.run(
            [PYTHON_EXE, "-c", "import pymobiledevice3.lockdown"],
            capture_output=True,
            timeout=20, **NO_CONSOLE)
        return result.returncode == 0
    except Exception:
        return False


def get_status() -> dict:
    return {
        "pymobiledevice3": has_pymobiledevice3(),
        "ipatool": find_tool("ipatool") is not None,
        "zsign": find_tool("zsign") is not None,
    }


# ---------------------------------------------------------------------------
# subprocess helpers
# ---------------------------------------------------------------------------

def run(cmd: list[str], timeout: int | None = 300) -> tuple[int, str, str]:
    try:
        result = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout, **NO_CONSOLE)
        return result.returncode, result.stdout, result.stderr
    except subprocess.TimeoutExpired:
        return 1, "", "timed out"
    except Exception as e:
        return 1, "", str(e)


def pmd3(*args: str, timeout: int | None = 120) -> tuple[int, str, str]:
    # -W ignore: the system Python 3.9 that ships with Apple's Command Line
    # Tools is built against LibreSSL, and urllib3 (a pymobiledevice3
    # dependency) prints a NotOpenSSLWarning about it on every single
    # invocation. It's harmless noise, not a real error, but it was
    # polluting the error text shown to the user (e.g. "no device
    # connected" would get buried under this warning). Suppressing all
    # Python warnings for this subprocess is the clean fix.
    return run([PYTHON_EXE, "-W", "ignore", "-m", "pymobiledevice3", *args], timeout=timeout)


# ---------------------------------------------------------------------------
# first-run setup (pip install pymobiledevice3, download ipatool/zsign)
# ---------------------------------------------------------------------------

def python_candidates() -> list:
    """Все питоны, какие есть на этом Маке, от самого подходящего к запасным.
    На старых системах /usr/bin/python3 - это Python 3.8 из инструментов Xcode:
    он запускается, но библиотека для iPhone под него уже не выпускается, да и
    pip там настолько старый, что не умеет читать современные пакеты."""
    if IS_WINDOWS:
        return [PYTHON_EXE]
    found = []
    versions = sorted(Path("/Library/Frameworks/Python.framework/Versions").glob("3.*"),
                      key=lambda x: [int(n) for n in x.name.split(".") if n.isdigit()],
                      reverse=True)
    for folder in versions:
        exe = folder / "bin" / "python3"
        if exe.exists():
            found.append(str(exe))
    for extra in ("/opt/homebrew/bin/python3", "/usr/local/bin/python3",
                  sys.executable, "/usr/bin/python3"):
        if extra and extra not in found and Path(extra).exists():
            found.append(extra)
    return found


def interpreter_version(exe: str) -> tuple:
    try:
        out = subprocess.run([exe, "-c", "import sys; print('%d.%d' % sys.version_info[:2])"],
                             capture_output=True, text=True, timeout=20, **NO_CONSOLE).stdout.strip()
        return tuple(int(x) for x in out.split("."))
    except Exception:
        return (0, 0)


def interpreter_has_library(exe: str) -> bool:
    try:
        return subprocess.run([exe, "-c", "import pymobiledevice3"],
                              capture_output=True, timeout=40, **NO_CONSOLE).returncode == 0
    except Exception:
        return False


def python_with_library() -> str | None:
    """Питон, у которого библиотека для iPhone уже стоит."""
    for exe in python_candidates():
        if interpreter_has_library(exe):
            return exe
    return None


def switch_python_if_needed() -> None:
    """Программу запускает короткий скрипт внутри приложения, и он может
    выбрать не тот питон - например Python 3.8 из инструментов Xcode. Если
    у него нет библиотеки, а у соседнего есть, перезапускаемся на соседнем."""
    if IS_WINDOWS or os.environ.get("SIDEKIT_PYSWITCH") == "1":
        return
    if has_pymobiledevice3():
        return
    better = python_with_library()
    if not better or Path(better).resolve() == Path(sys.executable).resolve():
        return
    os.environ["SIDEKIT_PYSWITCH"] = "1"
    try:
        os.execv(better, [better, os.path.abspath(__file__)] + sys.argv[1:])
    except Exception:
        pass


def python_for_install() -> str:
    """Куда ставить библиотеку: нужен Python 3.9 и новее."""
    for exe in python_candidates():
        if interpreter_version(exe) >= (3, 9):
            return exe
    return sys.executable


def pip_install_pymobiledevice3(log: list) -> bool:
    log.append("Устанавливаю pymobiledevice3...")
    # --force-reinstall --no-cache-dir matters here: if a previous install
    # left behind a wheel compiled for the wrong CPU architecture (e.g.
    # installed once under Rosetta, run another time natively), a plain
    # --upgrade can think the "same version" is already satisfied and skip
    # reinstalling it, leaving the broken files in place.
    target = python_for_install()
    if Path(target).resolve() != Path(sys.executable).resolve():
        log.append("Ставлю в подходящий Python: " + target)

    # Старый pip не умеет читать современные пакеты и падает на pyproject.toml -
    # именно это происходит на Python 3.8 из инструментов Xcode.
    log.append("Обновляю сам pip...")
    run([target, "-m", "pip", "install", "--user", "--upgrade",
         "pip", "setuptools", "wheel"], timeout=300)

    cmd = [
        target, "-m", "pip", "install", "--user",
        "--upgrade", "--force-reinstall", "--no-cache-dir", "pymobiledevice3",
    ]
    rc, out, err = run(cmd, timeout=600)
    if rc != 0 and "externally-managed-environment" in err:
        log.append("Повторяю установку с --break-system-packages...")
        rc, out, err = run(cmd + ["--break-system-packages"], timeout=300)
    if rc == 0:
        log.append("pymobiledevice3 установлен.")
        if Path(target).resolve() != Path(sys.executable).resolve():
            log.append("Перезапускаю программу на этом Python...")
            restart_with_python(target)
        return True
    log.append(f"Не удалось установить pymobiledevice3: {err.strip()[-800:]}")
    return False


def machine_arch() -> str:
    """Returns 'arm64' or 'x86_64' for the actual CPU, not the interpreter's
    architecture. platform.machine() is unreliable here: if Python itself is
    an Intel build running under Rosetta on an Apple Silicon Mac, it reports
    'x86_64' even though the machine can (and should) use the arm64 build."""
    if IS_WINDOWS:
        return "arm64" if platform.machine().lower() in ("arm64", "aarch64") else "x86_64"
    try:
        result = subprocess.run(
            ["sysctl", "-n", "hw.optional.arm64"], capture_output=True, text=True, timeout=5, **NO_CONSOLE)
        if result.stdout.strip() == "1":
            return "arm64"
        if result.stdout.strip() == "0":
            return "x86_64"
    except Exception:
        pass
    return "arm64" if platform.machine() == "arm64" else "x86_64"


_MACHO_MAGICS = {
    b"\xfe\xed\xfa\xce",  # Mach-O 32-bit
    b"\xce\xfa\xed\xfe",
    b"\xfe\xed\xfa\xcf",  # Mach-O 64-bit
    b"\xcf\xfa\xed\xfe",
    b"\xca\xfe\xba\xbe",  # fat/universal binary
    b"\xbe\xba\xfe\xca",
}


def _is_macho_binary(path: Path) -> bool:
    try:
        with open(path, "rb") as f:
            return f.read(4) in _MACHO_MAGICS
    except Exception:
        return False


def _extract_binary_from_tar(archive_path: Path, tmp: Path, preferred_name: str, log: list) -> Path | None:
    """Finds the actual tool binary inside a downloaded release tarball.
    Tar metadata (names, exec bits) isn't always trustworthy across
    projects/CI pipelines, so the reliable check is the file's own bytes:
    a real macOS executable starts with a Mach-O magic number no matter
    what it's called or how it's nested. Falls back to exact-name / largest
    file only if nothing looks like a real binary (and logs what it saw, so
    a repeat failure is diagnosable instead of a dead end)."""
    with tarfile.open(archive_path) as t:
        t.extractall(tmp)

    all_files = [p for p in tmp.rglob("*") if p.is_file()]
    listing = ", ".join(f"{p.relative_to(tmp)} ({p.stat().st_size}b)" for p in all_files[:12])
    log.append(f"  внутри архива {len(all_files)} файл(ов): {listing or '(пусто)'}")

    macho = [p for p in all_files if _is_macho_binary(p)]
    if macho:
        return max(macho, key=lambda p: p.stat().st_size)

    exact = [p for p in all_files if p.name == preferred_name]
    if exact:
        return exact[0]

    if all_files:
        return max(all_files, key=lambda p: p.stat().st_size)

    return None


def _adhoc_codesign(path: Path) -> None:
    """Ad-hoc code-signs a bundled binary (ipatool/zsign). Without ANY code
    signature, macOS can't verify "this is the same trusted binary" between
    separate process launches, so Keychain access grants ("Always Allow")
    never persist for it - every operation re-triggers the permission
    dialog no matter what's clicked. An ad-hoc signature (no paid Apple
    Developer certificate needed) still gives the binary a stable identity
    hash that macOS CAN track, which is what actually lets "Always Allow"
    stick. Best-effort: if codesign isn't available or fails, we just
    carry on with the unsigned binary as before.
    """
    if not IS_MAC:
        return
    try:
        subprocess.run(
            ["codesign", "--force", "-s", "-", str(path)],
            capture_output=True, timeout=30, **NO_CONSOLE)
    except Exception:
        pass


def fetch_github_binary(repo: str, matcher, binary_name: str, log: list) -> bool:
    log.append(f"Скачиваю {binary_name} с GitHub ({repo})...")
    try:
        req = urllib.request.Request(
            f"https://api.github.com/repos/{repo}/releases/latest",
            headers={"User-Agent": USER_AGENT},
        )
        with urllib.request.urlopen(req, timeout=30) as r:
            data = json.load(r)
        assets = data.get("assets", [])
        asset = next((a for a in assets if matcher(a["name"])), None)
        if asset is None:
            available = ", ".join(a["name"] for a in assets) or "(список пуст)"
            log.append(f"{binary_name}: не нашёл подходящую сборку под этот Mac в последнем релизе. Доступны: {available}")
            return False
        with tempfile.TemporaryDirectory() as tmp_str:
            tmp = Path(tmp_str)
            archive_path = tmp / asset["name"]
            urllib.request.urlretrieve(asset["browser_download_url"], archive_path)
            found = _extract_binary_from_tar(archive_path, tmp, binary_name, log)
            if found is None:
                log.append(f"{binary_name}: не нашёл исполняемый файл внутри архива.")
                return False
            BIN_DIR.mkdir(parents=True, exist_ok=True)
            dest = BIN_DIR / binary_name
            shutil.copy2(found, dest)
            dest.chmod(0o755)
            _adhoc_codesign(dest)
            log.append(f"{binary_name}: готово ({dest}).")
            return True
    except Exception as e:
        log.append(f"{binary_name}: ошибка - {e}")
        return False


def install_ipatool(log: list) -> bool:
    arch = "arm64" if machine_arch() == "arm64" else "amd64"
    system = "windows" if IS_WINDOWS else "macos"
    log.append(f"  система: {system}, архитектура: {arch}")
    return fetch_github_binary(
        "majd/ipatool", lambda n: n.endswith(f"{system}-{arch}.tar.gz"),
        "ipatool.exe" if IS_WINDOWS else "ipatool", log,
    )


def install_zsign(log: list) -> bool:
    if IS_MAC and machine_arch() != "arm64":
        log.append("zsign под Intel-Маки в свежих выпусках не публикуют. "
                   "Для скачивания и установки приложений через Apple ID он не нужен - пропускаю.")
        return True

    if IS_WINDOWS:
        log.append("zsign под Windows не публикуют — пропускаю "
                   "(он нужен только для переподписи не-AppStore .ipa).")
        return False
    arch = machine_arch()
    log.append(f"  определил архитектуру Mac как: {arch}")
    ok = fetch_github_binary("zhlynn/zsign", lambda n: n == f"zsign-macos-{arch}.tar.gz", "zsign", log)
    if not ok:
        log.append(
            "zsign не критичен для скачивания приложений через Apple ID - можно пропустить "
            "(его проект пока не всегда публикует сборку под Intel Mac для каждой версии)."
        )
    return ok


_setup_jobs: dict = {}
_setup_lock = threading.Lock()

SETUP_STEPS = {
    "pymobiledevice3": lambda log: pip_install_pymobiledevice3(log),
    "ipatool": lambda log: install_ipatool(log),
    "zsign": lambda log: install_zsign(log),
}


def start_setup_step(name: str) -> dict:
    """Запускает доустановку в фоне. Раньше окно ждало ответа на один запрос, а
    установка библиотеки идёт минутами - и окно обрывало запрос по своему
    таймауту («The request timed out»), хотя установка ещё шла."""
    worker = SETUP_STEPS.get(name)
    if worker is None:
        return {"ok": False, "error": "Неизвестный шаг: " + str(name)}
    with _setup_lock:
        job = _setup_jobs.get(name)
        if job and job.get("running"):
            return {"ok": True, "started": True, "already": True}
        job = {"running": True, "done": False, "ok": None, "log": []}
        _setup_jobs[name] = job

    def run_step():
        try:
            result = worker(job["log"])
        except Exception as e:
            job["log"].append("Сбой: " + str(e))
            result = False
        job["ok"] = bool(result)
        job["running"] = False
        job["done"] = True

    threading.Thread(target=run_step, daemon=True).start()
    return {"ok": True, "started": True}


def setup_step_state(name: str) -> dict:
    job = _setup_jobs.get(name)
    if not job:
        return {"running": False, "done": False, "log": []}
    return {"running": job["running"], "done": job["done"],
            "ok": job["ok"], "log": list(job["log"])}


def run_setup() -> dict:
    log: list[str] = []
    status = get_status()
    if not status["pymobiledevice3"]:
        pip_install_pymobiledevice3(log)
    if not status["ipatool"]:
        install_ipatool(log)
    if not status["zsign"]:
        install_zsign(log)
    return {"log": log, "status": get_status()}


# ---------------------------------------------------------------------------
# ipatool-backed actions
# ---------------------------------------------------------------------------

PASSPHRASE_FILE = LOCK_DIR / "ipatool.passphrase"


def ipatool_keychain_args() -> list:
    """On macOS: nothing. ipatool stores its session in the system Keychain
    there, and --keychain-passphrase applies only to its FILE-based keyring -
    passing it would add an unlock step without replacing anything.

    On Windows there IS no system keychain for ipatool to use, so it falls
    back to that file keyring - and refuses to save anything without a
    passphrase ("keychain passphrase is required when not running in
    interactive mode"). SideKit keeps one for it: generated once, stored in
    the user's own app-data folder, never shown to anyone. Nobody has to
    remember it - it exists purely because ipatool insists on having one."""
    if not IS_WINDOWS:
        return []
    try:
        if PASSPHRASE_FILE.exists():
            secret = PASSPHRASE_FILE.read_text(encoding="utf-8").strip()
        else:
            import secrets
            secret = secrets.token_urlsafe(24)
            LOCK_DIR.mkdir(parents=True, exist_ok=True)
            PASSPHRASE_FILE.write_text(secret, encoding="utf-8")
            try:
                os.chmod(PASSPHRASE_FILE, 0o600)
            except Exception:
                pass
        if secret:
            return ["--keychain-passphrase", secret]
    except Exception:
        pass
    return []


# ---------------------------------------------------------------------------
# macOS Keychain access for ipatool's saved Apple ID session
#
# ipatool keeps its session in one login-keychain entry and, when it creates
# that entry itself, locks it to "the exact binary that wrote it" (path +
# code signature). The moment SideKit moves - a rebuild, a copy to
# /Applications - that identity no longer matches, and macOS falls back to
# asking for the keychain password on EVERY access. Worse, when the answer
# doesn't satisfy it, ipatool doesn't report a permission problem at all:
# the lookup just comes back empty and it says the account "could not be
# found in the keyring", so downloads fail at 0% while the app still thinks
# it's logged in.
#
# The fix is to own the entry instead of letting ipatool create it: an
# entry created with `-A` is readable without any prompt, and ipatool then
# UPDATES it rather than creating a new one - and updating never changes
# the access rules. So the prompt is gone for good, including after the app
# is moved or rebuilt.
# ---------------------------------------------------------------------------

KEYCHAIN_SERVICE = "ipatool-auth.service"
KEYCHAIN_ACCOUNT = "account"


def prepare_keychain_slot() -> None:
    """Clears out ipatool's keychain entry right before a login, so ipatool
    creates a fresh one itself.

    An earlier version pre-created an empty entry with `-A` (readable with no
    password) hoping ipatool would just fill it in. It doesn't: the session
    never got written, the entry stayed empty, and every download then died
    with "failed to unmarshal json: unexpected end of JSON input" - a signed-
    in-looking app that could not download a thing. Letting ipatool own its
    own entry is what actually works; the password prompts this was meant to
    avoid only appeared because the entry had been created by a copy of
    ipatool living at a different path."""
    if not IS_MAC:
        # Windows keeps ipatool's session in the Credential Manager, which it
        # manages itself - there is nothing to clear out here.
        return
    run(["security", "delete-generic-password", "-s", KEYCHAIN_SERVICE], timeout=15)


def keychain_has_session() -> bool:
    """Whether a session was really stored. `security` can read the entry
    without a prompt only when ipatool marked it accessible, so an
    unreadable-but-present entry counts as stored too - what matters here is
    that it is not empty."""
    if not IS_MAC:
        # No equivalent check on Windows; ipatool's own "auth info" is the
        # authority there, and it is consulted separately.
        return True
    try:
        result = subprocess.run(
            ["security", "find-generic-password", "-s", KEYCHAIN_SERVICE,
             "-a", KEYCHAIN_ACCOUNT, "-w"],
            capture_output=True, text=True, timeout=8, **NO_CONSOLE)
    except Exception:
        return True   # could not check - don't cry wolf
    if result.returncode != 0:
        return True   # entry exists but isn't readable from here: fine
    return bool(result.stdout.strip())


# macOS guards Desktop / Downloads / Documents / iCloud Drive per app. SideKit
# gets no automatic pass there, and the failure is silent and cryptic: the
# file simply refuses to open with "Operation not permitted", buried in a
# Python traceback. Since ~/Desktop is exactly where .ipa files naturally
# live, this needs to be caught early and explained in one sentence.
TCC_HINT = (
    "macOS не разрешает SideKit доступ к этой папке.\n\n"
    "Открой Системные настройки → Конфиденциальность и безопасность → "
    "Полный доступ к диску, нажми «+», выбери /Applications/SideKit.app "
    "и включи переключатель. Потом перезапусти SideKit.\n\n"
    "Либо просто держи .ipa в другой папке — например в Загрузках "
    "внутри папки SideKit."
)


def check_readable(path: str) -> str | None:
    """None if the file can actually be read, otherwise a ready-to-show
    explanation. Checked up front because the same block hits mid-install
    otherwise, after the progress bar has already started moving."""
    try:
        with open(path, "rb") as f:
            f.read(1)
        return None
    except PermissionError:
        return f"Не удалось прочитать файл:\n{path}\n\n{TCC_HINT}"
    except FileNotFoundError:
        return f"Файл не найден:\n{path}"
    except Exception as e:
        return f"Не удалось открыть файл:\n{path}\n\n{e}"


def check_writable_dir(directory: Path) -> str | None:
    """Same idea for the download destination: better to say why now than to
    let ipatool die at 0% with a permissions error nobody can read."""
    probe = directory / ".sidekit-write-test"
    try:
        directory.mkdir(parents=True, exist_ok=True)
        probe.write_bytes(b"")
        probe.unlink(missing_ok=True)
        return None
    except PermissionError:
        return f"Не удалось записать в папку:\n{directory}\n\n{TCC_HINT}"
    except Exception as e:
        return f"Не удалось записать в папку:\n{directory}\n\n{e}"


def _looks_like_lost_session(text: str) -> bool:
    low = (text or "").lower()
    return "keyring" in low or "failed to get account" in low


LOGIN_STATE_FILE = LOCK_DIR / "login_state.json"


def _write_login_state(email: str) -> None:
    try:
        LOCK_DIR.mkdir(parents=True, exist_ok=True)
        LOGIN_STATE_FILE.write_text(json.dumps({"logged_in": True, "email": email}), encoding="utf-8")
    except Exception:
        pass


def _clear_login_state() -> None:
    try:
        LOGIN_STATE_FILE.unlink(missing_ok=True)
    except Exception:
        pass


_auth_status_cache = {"time": 0.0, "value": None}


def _read_login_state() -> dict:
    try:
        if LOGIN_STATE_FILE.exists():
            data = json.loads(LOGIN_STATE_FILE.read_text(encoding="utf-8"))
            if data.get("logged_in"):
                return {"logged_in": True, "email": data.get("email", "")}
    except Exception:
        pass
    return {"logged_in": False}


def ipatool_auth_status() -> dict:
    """Asks ipatool itself who is signed in - it owns the session, so it is
    the only source that can't drift out of sync with reality.

    This used to be answered from a local file instead, because `auth info`
    reads the keychain and that used to pop a macOS password dialog on every
    single launch. Now that SideKit owns the keychain entry and keeps it
    freely readable (see prepare_keychain_slot), asking costs milliseconds
    and no dialog. The local file is kept only as an answer for the case
    where ipatool CAN'T be asked.

    Nothing here erases the saved login on a mere timeout: a check that
    can't complete means "unknown", not "signed out". Treating those as the
    same thing is what silently logged the account out mid-session while the
    saved session was in fact perfectly fine."""
    now = time.time()
    cached = _auth_status_cache["value"]
    if cached and now - _auth_status_cache["time"] < 30:
        return cached

    tool = find_tool("ipatool")
    status = None
    if tool:
        try:
            result = subprocess.run(
                [tool, "auth", "info", "--non-interactive", "--format", "json"]
                + ipatool_keychain_args(),
                capture_output=True, text=True, timeout=10, **NO_CONSOLE)
            # ipatool reports failures on stderr, so reading stdout alone
            # leaves "not signed in" looking like "couldn't tell" - and the
            # fallback to the local record then claims an account is signed
            # in when its session is long gone.
            for line in reversed(((result.stdout or "") + (result.stderr or "")).strip().splitlines()):
                line = line.strip()
                if line.startswith("{"):
                    data = json.loads(line)
                    status = (
                        {"logged_in": True, "email": data.get("email", "")}
                        if data.get("success") else {"logged_in": False}
                    )
                    break
        except Exception:
            status = None  # includes the timeout case: simply unknown

    if status is None:
        status = _read_login_state()
    elif status["logged_in"]:
        _write_login_state(status.get("email", ""))
    else:
        _clear_login_state()

    _auth_status_cache.update({"time": now, "value": status})
    return status


def _invalidate_auth_status() -> None:
    _auth_status_cache.update({"time": 0.0, "value": None})


def ipatool_logout() -> dict:
    """Signs out on this Mac by dropping the saved session, so another Apple
    ID can be used - swapping between two family phones is the normal case.

    Deliberately does NOT call `ipatool auth revoke`: that asks Apple to
    invalidate the token account-wide, which would also sign the account out
    somewhere else. Removing the local copy is what "выйти" should mean."""
    if IS_MAC:
        run(["security", "delete-generic-password", "-s", KEYCHAIN_SERVICE], timeout=15)
    else:
        # ipatool owns the stored credential on Windows, so ask it to drop it.
        tool = find_tool("ipatool")
        if tool:
            run([tool, "auth", "revoke", "--non-interactive", "--format", "json"]
                + ipatool_keychain_args(), timeout=30)
    _clear_login_state()
    _invalidate_auth_status()
    return {"ok": True}


# Почтовые домены, с которых обычно и заводят Apple ID. Нужны, чтобы поймать
# опечатку в один символ: gmial.com, iclod.com, yandx.ru.
COMMON_MAIL_DOMAINS = [
    "icloud.com", "me.com", "mac.com", "gmail.com", "googlemail.com",
    "yandex.ru", "ya.ru", "mail.ru", "bk.ru", "inbox.ru", "list.ru",
    "outlook.com", "hotmail.com", "live.com", "rambler.ru", "yahoo.com",
]


def known_apple_ids() -> set:
    """Apple ID, которые в этой программе уже встречались: прошлый вход и
    аккаунты, которыми куплены приложения на телефоне. Apple принципиально не
    отвечает, существует ли аккаунт (защита от перебора), поэтому сверять
    введённое можно только с тем, что известно нам самим."""
    found = set()
    state = _read_login_state()
    if state.get("email"):
        found.add(state["email"].strip().lower())
    # Раньше сюда добавлялись владельцы из базы известных приложений. База
    # едет в установщике с моего телефона, поэтому на чужом компьютере первый
    # же вход упирался в «раньше вход был как din1337@icloud.com». Сверять
    # можно только с тем, чем входили на ЭТОМ компьютере.
    return found


def suspicious_login(email: str) -> str:
    """Возвращает предупреждение, если логин похож на опечатку. Пустая строка -
    возражений нет."""
    email = email.strip().lower()
    domain = email.split("@")[-1]

    known = known_apple_ids()
    if known and email not in known:
        close = difflib.get_close_matches(email, list(known), n=1, cutoff=0.75)
        if close:
            return ("Похоже на опечатку: раньше вход был как " + close[0]
                    + ", а сейчас введено " + email + ".")
        return ("Этим Apple ID здесь ещё не пользовались. Раньше вход был как "
                + sorted(known)[0] + ".")

    if domain not in COMMON_MAIL_DOMAINS:
        close = difflib.get_close_matches(domain, COMMON_MAIL_DOMAINS, n=1, cutoff=0.8)
        if close:
            return "Похоже на опечатку в почте: " + domain + " вместо " + close[0] + "?"
    return ""


def ipatool_login(email: str, password: str, auth_code: str | None, force: bool = False) -> dict:
    tool = find_tool("ipatool")
    if not tool:
        return {"ok": False, "error": "ipatool не установлен"}
    # Apple на неверный пароль и на «нужен код» отвечает ОДНОЙ И ТОЙ ЖЕ
    # фразой ("2FA code is required") - различить их по ответу невозможно.
    # Поэтому явную чепуху вместо почты отсекаем сами, не спрашивая Apple:
    # иначе программа предлагает ввести код, которого никто не присылал.
    if not re.match(r"^[^@\s]+@[^@\s]+\.[A-Za-z]{2,}$", email.strip()):
        return {
            "ok": False,
            "bad_credentials": True,
            "error": "Это не похоже на Apple ID. Нужна почта целиком, например ivan@icloud.com.",
        }

    # Apple на неверный пароль отвечает тем же, что на «нужен код», поэтому
    # сомнительный логин отсекаем здесь - до того, как программа предложит
    # ввести код, которого никто не пришлёт.
    if not auth_code and not force:
        doubt = suspicious_login(email)
        if doubt:
            return {"ok": False, "confirm_login": True, "error": doubt}

    prepare_keychain_slot()

    def build_cmd(binary: str) -> list:
        line = [binary, "auth", "login", "-e", email, "-p", password,
                "--non-interactive", "--format", "json"] + ipatool_keychain_args()
        if auth_code:
            line += ["--auth-code", auth_code]
        return line

    cmd = build_cmd(tool)
    # A longer timeout here on purpose: on the first ever run, macOS pops a
    # "ipatool wants to access your keychain" permission dialog while this
    # is running, and the command genuinely blocks until the user answers
    # it. 60s isn't unreasonable for "go find that dialog and click it".
    rc, out, err = run(cmd, timeout=90)

    # Apple иногда отвечает 404 на самом последнем шаге - когда отправляешь
    # код. Свежий ipatool сам выбирает, на какой сервер Apple идти, и порой
    # выбирает не тот. Пробуем ещё раз, а потом - запасной ipatool постарше,
    # который ходит по постоянному адресу.
    def looks_like_apple_404(text: str) -> bool:
        low = text.lower()
        return "404" in low and ("unexpected response" in low or "not found" in low)

    if looks_like_apple_404((out or "") + (err or "")):
        remember_error("вход в Apple ID", "Apple ответила 404, пробую ещё раз")
        time.sleep(1.5)
        rc, out, err = run(build_cmd(tool), timeout=90)   # бывает разовым
    if looks_like_apple_404((out or "") + (err or "")):
        spare = ensure_legacy_ipatool()                   # при нужде докачает
        if spare:
            time.sleep(1)
            rc, out, err = run(build_cmd(str(spare)), timeout=120)

    # Read BOTH streams. ipatool prints its result as JSON, but sends failures
    # (including "2FA code is required") to stderr - looking only at stdout is
    # why the app used to answer a code request with a plain error message and
    # never show the field to type the code into.
    combined = ((out or "") + "\n" + (err or "")).strip()
    success = None
    error_text = ""
    for line in reversed(combined.splitlines()):
        line = line.strip()
        if not line.startswith("{"):
            continue
        try:
            parsed = json.loads(line)
        except Exception:
            continue
        success = parsed.get("success")
        error_text = str(parsed.get("error", ""))
        break

    lowered = (combined + " " + error_text).lower()

    # Неверный пароль Apple отдаёт вместе с упоминанием проверочного кода,
    # и программа честно показывала экран "введи код" — вводить туда было
    # нечего, потому что кода Apple не присылала. Ошибку логина проверяем
    # первой: не пускаем дальше, пока пароль не верный.
    bad_credentials = any(marker in lowered for marker in (
        "password was incorrect", "invalid credentials", "incorrect password",
        "account information was entered incorrectly", "invalid email",
        "unable to authenticate", "authentication failed", "invalid password",
        "wrong password", "-20101", "bad login", "invalid account",
    ))
    if bad_credentials:
        _clear_login_state()
        _invalidate_auth_status()
        return {
            "ok": False,
            "bad_credentials": True,
            "error": "Неверный Apple ID или пароль. Проверь почту и пароль и попробуй ещё раз.",
            "raw": combined,
        }

    wants_code = any(marker in lowered for marker in (
        "2fa", "auth-code", "auth code", "verification code", "code is required",
    ))
    if wants_code and not auth_code:
        # Apple has just sent the code to the user's devices; the app's only
        # job now is to ask for it.
        return {"ok": False, "need2fa": True, "raw": combined}
    if wants_code and auth_code:
        # Сюда же попадает случай «пароль неверный»: Apple отвечает так же,
        # как на неверный код, поэтому в тексте названы обе причины.
        return {"ok": False, "need2fa": True, "wrong_code": True,
                "error": ("Не подошло. Если код точно свежий — значит неверный "
                          "Apple ID или пароль: нажми «Ввести другой Apple ID» "
                          "и проверь их."),
                "raw": combined}

    ok = success if success is not None else (rc == 0)
    if ok and not keychain_has_session():
        # ipatool said yes but stored nothing. Reporting success here is what
        # produced the worst failure mode of all: an app that looks signed in
        # and fails every single download afterwards.
        _clear_login_state()
        _invalidate_auth_status()
        return {
            "ok": False,
            "error": (
                "Apple вход принял, но сессия не сохранилась в Связке ключей, "
                "поэтому скачивание работать не будет.\n\n"
                "Попробуй войти ещё раз. Если повторится — перезапусти SideKit "
                "и войди заново."
            ),
            "raw": out + err,
        }
    if ok:
        _write_login_state(email)
        _invalidate_auth_status()
        return {"ok": True, "raw": combined}

    remember_error("вход в Apple ID", combined)

    # Failed: hand back a sentence, not ipatool's JSON. "something went wrong"
    # is what Apple returns for a rejected code as well as for bad
    # credentials, so the message has to cover both without guessing.
    _invalidate_auth_status()
    human = error_text or _extract_error_text(combined)
    if "something went wrong" in human.lower():
        human = (
            "Apple не приняла вход. Проверь Apple ID и пароль — "
            "и если вводил код, запроси новый: старый мог устареть."
        )
    return {"ok": False, "error": human, "raw": combined,
            "at_code_step": bool(auth_code)}


def ipatool_search(term: str, limit: int) -> dict:
    tool = find_tool("ipatool")
    if not tool:
        return {"ok": False, "error": "ipatool не установлен"}
    cmd = [tool, "search", term, "--limit", str(limit), "--non-interactive", "--format", "json"] + ipatool_keychain_args()
    rc, out, err = run(cmd, timeout=60)
    results = []
    try:
        parsed = json.loads(out)
        results = parsed.get("apps", parsed) if isinstance(parsed, dict) else parsed
    except Exception:
        pass
    return {"ok": rc == 0, "results": results, "raw": out + err}


def _clean_python_traceback(raw: str) -> str | None:
    """The real message out of a pymobiledevice3 crash dump. Its tracebacks
    are drawn as a boxed table, so the useful line ("AppInstallError: ...")
    is buried under dozens of lines of framed source code - showing that raw
    in the interface tells the user nothing."""
    for line in reversed((raw or "").splitlines()):
        line = line.strip().strip("│").strip()
        if re.match(r"^[A-Za-z_]+(Error|Exception)\b.*:", line):
            return line
    return None


def _extract_error_text(raw: str) -> str:
    """Pulls a clean, human-readable error line out of subprocess output
    instead of dumping raw text. This matters more now that some jobs run
    WITHOUT --non-interactive (to get a real progress percentage), so
    stdout also contains progress-bar redraw noise (carriage returns,
    block-drawing characters) that can bury the actual error message."""
    for line in reversed(raw.splitlines()):
        line = line.strip()
        if line.lower().startswith("error:") or line.lower().startswith("error "):
            return line
    cleaned = [
        l.strip() for l in re.split(r"[\r\n]", raw)
        if l.strip() and "%" not in l and "|" not in l and "█" not in l
    ]
    text = "\n".join(cleaned).strip()
    return text[-800:] if text else "неизвестная ошибка"


_download_lock = threading.Lock()
_download_state = {
    "running": False, "bundle_id": None, "percent": 0,
    "downloaded": None, "total": None, "status": "idle",
    "path": None, "error": None, "raw": "", "paused": False,
}


def _apply_progress_line(line: str) -> None:
    m = re.search(r"(\d{1,3})\s*%", line)
    if not m:
        return
    percent = min(100, max(0, int(m.group(1))))
    # ipatool writes the pair as "(192/805 MB, 9.0 MB/s)" - the FIRST number
    # usually carries no unit of its own, it borrows the second one. Making
    # that unit optional is what stops the size readout from being wrong
    # (it used to only match the rare lines that did spell both units out,
    # so the UI could sit on a stale "723 kB / 805 MB" for a whole download).
    m2 = re.search(
        r"\(([\d.]+)\s*([KMGTkmgt]?i?B)?\s*/\s*([\d.]+)\s*([KMGTkmgt]?i?B)", line
    )
    with _download_lock:
        if not _download_state["running"]:
            return
        _download_state["percent"] = percent
        if m2:
            unit = m2.group(2) or m2.group(4)
            _download_state["downloaded"] = f"{m2.group(1)} {unit}"
            _download_state["total"] = f"{m2.group(3)} {m2.group(4)}"


# A phone knows things the App Store no longer admits to. Every installed
# app carries its own iTunesMetadata, including the numeric App Store item
# id it was installed from - which still works for downloading even after
# the app has been pulled from the store, as long as the Apple ID holds a
# license for it. That is the whole trick behind the fallback below.
_ITEM_ID_SCRIPT = r'''
import asyncio, inspect, json, plistlib, sys
from pymobiledevice3.lockdown import create_using_usbmux
from pymobiledevice3.services.installation_proxy import InstallationProxyService

async def main():
    bundle_id = sys.argv[1]
    udid = sys.argv[2] or None
    lockdown = create_using_usbmux(serial=udid) if udid else create_using_usbmux()
    if inspect.iscoroutine(lockdown):
        lockdown = await lockdown
    proxy = InstallationProxyService(lockdown)
    result = proxy.lookup(options={
        "ReturnAttributes": ["CFBundleIdentifier", "iTunesMetadata"],
        "BundleIDs": [bundle_id],
    })
    if inspect.iscoroutine(result):
        result = await result
    metadata = (result.get(bundle_id) or {}).get("iTunesMetadata")
    if not metadata:
        print(json.dumps({"ok": False}))
        return
    parsed = plistlib.loads(bytes(metadata))
    print(json.dumps({"ok": True, "item_id": parsed.get("itemId"),
                      "name": parsed.get("itemName", "")}))

asyncio.run(main())
'''


def device_app_item_id(bundle_id: str, udid: str | None) -> int | None:
    """The App Store item id of an app as recorded on the connected device,
    or None if it isn't installed there / has no store metadata (e.g. it was
    sideloaded rather than installed from the App Store)."""
    rc, out, err = run(
        [PYTHON_EXE, "-W", "ignore", "-c", _ITEM_ID_SCRIPT, bundle_id, udid or ""],
        timeout=90,
    )
    for line in (out or "").splitlines():
        line = line.strip()
        if not line.startswith("{"):
            continue
        try:
            data = json.loads(line)
            if data.get("ok") and data.get("item_id"):
                return int(data["item_id"])
        except Exception:
            pass
    return None


# ---------------------------------------------------------------------------
# apps that vanished from the phone
#
# iOS removes apps on its own - offloading them for space, or dropping them
# outright once they're pulled from the App Store. What stays behind is the
# home-screen icon, so the phone still knows the app WAS there while
# installation_proxy no longer lists it. That difference is the list of
# "vanished" apps.
#
# Bringing one back needs its numeric App Store id, and there are three
# places to find it, in descending order of reliability:
#
#   1. SideKit's own record of apps it has seen installed on this phone
#      (exact, and works even for apps deleted from the store afterwards);
#   2. the App Store catalogue, by bundle id (works for anything still on
#      sale - the common case for apps iOS merely offloaded);
#   3. the user, typing the id in by hand (last resort for apps that are
#      both gone from the phone and gone from the store).
#
# Point 1 is why the record is kept at all: it is the insurance policy that
# makes a future disappearance recoverable with one click.
# ---------------------------------------------------------------------------

KNOWN_APPS_FILE = LOCK_DIR / "known_apps.json"
RESTORE_DIR = LOCK_DIR / "restore"

# Home-screen entries that aren't apps: folders and web clips are identified
# by a bare 32-character hex string rather than a bundle id.
HEX_ID = re.compile(r"[0-9A-F]{32}")


def load_known_apps() -> dict:
    try:
        return json.loads(KNOWN_APPS_FILE.read_text(encoding="utf-8"))
    except Exception:
        return {}


def save_known_apps(data: dict) -> None:
    try:
        LOCK_DIR.mkdir(parents=True, exist_ok=True)
        KNOWN_APPS_FILE.write_text(json.dumps(data, ensure_ascii=False), encoding="utf-8")
    except Exception:
        pass


_METADATA_SCRIPT = r'''
import asyncio, inspect, json, plistlib, sys
from pymobiledevice3.lockdown import create_using_usbmux
from pymobiledevice3.services.installation_proxy import InstallationProxyService

async def main():
    udid = sys.argv[1] or None
    bundle_ids = json.loads(sys.stdin.read())
    lockdown = create_using_usbmux(serial=udid) if udid else create_using_usbmux()
    if inspect.iscoroutine(lockdown):
        lockdown = await lockdown
    proxy = InstallationProxyService(lockdown)
    result = proxy.lookup(options={
        "ReturnAttributes": ["CFBundleIdentifier", "iTunesMetadata"],
        "BundleIDs": bundle_ids,
    })
    if inspect.iscoroutine(result):
        result = await result
    out = {}
    for bundle_id, info in (result or {}).items():
        metadata = (info or {}).get("iTunesMetadata")
        if not metadata:
            continue
        try:
            parsed = plistlib.loads(bytes(metadata))
        except Exception:
            continue
        if parsed.get("itemId"):
            out[bundle_id] = {
                "item_id": int(parsed["itemId"]),
                "name": parsed.get("itemName", ""),
                "version": parsed.get("bundleShortVersionString", ""),
            }
    print(json.dumps(out, ensure_ascii=False))

asyncio.run(main())
'''

_VANISHED_SCRIPT = r'''
import asyncio, inspect, json, sys
from pymobiledevice3.lockdown import create_using_usbmux
from pymobiledevice3.services.installation_proxy import InstallationProxyService
from pymobiledevice3.services.springboard import SpringBoardServicesService

def walk(node, found):
    if isinstance(node, dict):
        bundle_id = node.get("bundleIdentifier") or node.get("displayIdentifier")
        if bundle_id:
            found.append(bundle_id)
        for value in node.values():
            walk(value, found)
    elif isinstance(node, list):
        for value in node:
            walk(value, found)

async def main():
    udid = sys.argv[1] or None
    lockdown = create_using_usbmux(serial=udid) if udid else create_using_usbmux()
    if inspect.iscoroutine(lockdown):
        lockdown = await lockdown

    proxy = InstallationProxyService(lockdown)
    apps = proxy.get_apps(application_type="Any", calculate_sizes=False)
    if inspect.iscoroutine(apps):
        apps = await apps

    springboard = SpringBoardServicesService(lockdown)
    state = springboard.get_icon_state()
    if inspect.iscoroutine(state):
        state = await state
    icons = []
    walk(state, icons)

    print(json.dumps({"installed": list(apps.keys()), "icons": icons}))

asyncio.run(main())
'''


def _run_device_script(script: str, udid: str | None, stdin_payload: str | None = None,
                       timeout: int = 180):
    """Runs one of the pymobiledevice3 helper scripts and returns its parsed
    JSON output, or None. The device libraries are async and noisy on
    shutdown, so they live in a subprocess rather than in this server."""
    try:
        result = subprocess.run(
            [PYTHON_EXE, "-W", "ignore", "-c", script, udid or ""],
            input=stdin_payload, text=True, capture_output=True, timeout=timeout, **NO_CONSOLE)
    except Exception:
        return None
    for line in (result.stdout or "").splitlines():
        line = line.strip()
        if line.startswith("{"):
            try:
                return json.loads(line)
            except Exception:
                continue
    return None


# Not every app on an iPhone came from the App Store. Anything installed
# from an .ipa - re-signed banking apps and the like - has no App Store id at
# all, so Apple will never hand it back no matter what is typed in. The only
# way home for those is the .ipa file itself, and the ones this user has are
# already sitting in their download folders. So: index those files by bundle
# id, and a vanished app that matches one can be reinstalled straight from
# disk.
IPA_SEARCH_DIRS = [
    Path.home() / "Downloads",
    Path.home() / "Desktop",
    Path.home() / "Documents",
]

_local_ipa_cache = {"time": 0.0, "index": {}, "blocked": False}


def _read_ipa_identity(path: Path) -> dict | None:
    import plistlib
    import zipfile
    metadata = {}
    try:
        with zipfile.ZipFile(path) as archive:
            names = archive.namelist()
            name = next(
                (n for n in names
                 if re.fullmatch(r"Payload/[^/]+\.app/Info\.plist", n)), None
            )
            if not name:
                return None
            info = plistlib.loads(archive.read(name))
            # An .ipa that came from the App Store carries its store id and
            # the account that bought it. Both matter: the id makes the app
            # recoverable from Apple on any phone, and the buying account
            # decides where the file will actually run (FairPlay ties it to
            # that Apple ID).
            if "iTunesMetadata.plist" in names:
                try:
                    metadata = plistlib.loads(archive.read("iTunesMetadata.plist"))
                except Exception:
                    metadata = {}
    except Exception:
        return None
    bundle_id = info.get("CFBundleIdentifier")
    if not bundle_id:
        return None
    account = (metadata.get("com.apple.iTunesStore.downloadInfo") or {}).get("accountInfo") or {}
    return {
        "bundle_id": bundle_id,
        "name": (info.get("CFBundleDisplayName") or info.get("CFBundleName")
                 or metadata.get("itemName") or bundle_id),
        "version": info.get("CFBundleShortVersionString", ""),
        "path": str(path),
        "item_id": int(metadata["itemId"]) if metadata.get("itemId") else None,
        "bought_by": account.get("AppleID"),
    }


def index_local_ipas(force: bool = False) -> dict:
    """Everything SideKit can find on disk, keyed by bundle id. Cached for a
    minute: opening every .ipa means reading a zip header out of files that
    are hundreds of megabytes each.

    Also reports whether macOS blocked the search outright - a scan that
    finds nothing because it isn't allowed to look must not be presented as
    "you have no files"."""
    now = time.time()
    if not force and now - _local_ipa_cache["time"] < 60:
        return _local_ipa_cache

    index: dict = {}
    blocked = False
    for directory in IPA_SEARCH_DIRS:
        # Explicit listing first: Path.glob() swallows permission errors and
        # just yields nothing, which reads exactly like "no files here" -
        # the difference that matters is whether macOS refused to let us look.
        try:
            subdirs = [d for d in os.listdir(directory)]
        except PermissionError:
            blocked = True
            continue
        except Exception:
            continue
        try:
            candidates = list(directory.glob("*.ipa"))
            for sub in subdirs:
                child = directory / sub
                if not child.is_dir():
                    continue
                try:
                    os.listdir(child)
                except PermissionError:
                    blocked = True
                    continue
                except Exception:
                    continue
                candidates += list(child.glob("*.ipa"))
        except Exception:
            continue
        for path in candidates:
            identity = _read_ipa_identity(path)
            if identity is None:
                # Unreadable because macOS says so, rather than because the
                # file is broken - worth telling the user about.
                try:
                    with open(path, "rb") as f:
                        f.read(1)
                except PermissionError:
                    blocked = True
                except Exception:
                    pass
                continue
            existing = index.get(identity["bundle_id"])
            if not existing or identity["version"] > existing["version"]:
                index[identity["bundle_id"]] = identity

    # Every store id found in a file is worth keeping: it makes that app
    # recoverable from Apple later, on this phone or any other, even if the
    # file itself is deleted or turns out to be tied to someone else's
    # Apple ID.
    learned = {b: i for b, i in index.items() if i.get("item_id")}
    if learned:
        known = load_known_apps()
        changed = False
        for bundle_id, identity in learned.items():
            entry = known.get(bundle_id, {})
            if entry.get("item_id") != identity["item_id"]:
                entry["item_id"] = identity["item_id"]
                entry.setdefault("name", identity["name"])
                entry.setdefault("source", "local-ipa")
                known[bundle_id] = entry
                changed = True
        if changed:
            save_known_apps(known)

    _local_ipa_cache.update({"time": now, "index": index, "blocked": blocked})
    return _local_ipa_cache


# Same as _METADATA_SCRIPT, but it decides for itself what to look at: every
# user-installed app on the phone. That matters because the record has to be
# taken the moment a phone is plugged in, before the user goes anywhere in
# the interface - an app whose id was never recorded while it was installed
# is unrecoverable once it disappears.
_ALL_METADATA_SCRIPT = r'''
import asyncio, inspect, json, plistlib, sys
from pymobiledevice3.lockdown import create_using_usbmux
from pymobiledevice3.services.installation_proxy import InstallationProxyService

async def main():
    udid = sys.argv[1] or None
    lockdown = create_using_usbmux(serial=udid) if udid else create_using_usbmux()
    if inspect.iscoroutine(lockdown):
        lockdown = await lockdown
    proxy = InstallationProxyService(lockdown)
    apps = proxy.get_apps(application_type="User", calculate_sizes=False)
    if inspect.iscoroutine(apps):
        apps = await apps
    bundle_ids = list(apps.keys())
    result = proxy.lookup(options={
        "ReturnAttributes": ["CFBundleIdentifier", "iTunesMetadata"],
        "BundleIDs": bundle_ids,
    })
    if inspect.iscoroutine(result):
        result = await result
    out = {}
    for bundle_id, info in (result or {}).items():
        metadata = (info or {}).get("iTunesMetadata")
        if not metadata:
            continue
        try:
            parsed = plistlib.loads(bytes(metadata))
        except Exception:
            continue
        if parsed.get("itemId"):
            out[bundle_id] = {
                "item_id": int(parsed["itemId"]),
                "name": parsed.get("itemName", ""),
                "version": parsed.get("bundleShortVersionString", ""),
            }
    print(json.dumps(out, ensure_ascii=False))

asyncio.run(main())
'''

_remember_lock = threading.Lock()
_remember_running = False


def remember_installed_apps(bundle_ids: list | None, udid: str | None) -> None:
    """Records the App Store id of everything installed right now, in the
    background. This is the insurance policy: once an app disappears, its id
    can no longer be read from the phone, and for apps also pulled from the
    store there is nowhere else to get it.

    Pass None for bundle_ids to have it sweep every user app on the phone."""
    global _remember_running
    with _remember_lock:
        if _remember_running:
            return
        _remember_running = True

    def job():
        global _remember_running
        try:
            if bundle_ids is None:
                found = _run_device_script(_ALL_METADATA_SCRIPT, udid, timeout=240) or {}
            else:
                found = _run_device_script(
                    _METADATA_SCRIPT, udid, json.dumps(bundle_ids), timeout=180
                ) or {}
            if found:
                known = load_known_apps()
                for bundle_id, info in found.items():
                    entry = known.get(bundle_id, {})
                    entry.update(info)
                    entry["last_seen"] = time.strftime("%Y-%m-%d")
                    # Which phones this app has been seen on. That is what
                    # later separates "this phone's own history" from apps
                    # belonging to someone else's device.
                    if udid:
                        seen = entry.get("seen_on") or []
                        if udid not in seen:
                            seen.append(udid)
                        entry["seen_on"] = seen
                    known[bundle_id] = entry
                save_known_apps(known)
        except Exception:
            pass
        finally:
            with _remember_lock:
                _remember_running = False

    threading.Thread(target=job, daemon=True).start()


def catalogue_lookup(bundle_id: str) -> dict | None:
    """The app's entry in the public App Store catalogue, or None if it has
    been pulled from sale. Tries the Russian storefront first - most of this
    phone's apps are Russian - then the US one."""
    for country in ("ru", "us"):
        try:
            req = urllib.request.Request(
                f"https://itunes.apple.com/lookup?bundleId={bundle_id}&country={country}",
                headers={"User-Agent": USER_AGENT},
            )
            with urllib.request.urlopen(req, timeout=10) as response:
                data = json.load(response)
            if data.get("resultCount"):
                entry = data["results"][0]
                return {"item_id": int(entry["trackId"]), "name": entry.get("trackName", "")}
        except Exception:
            continue
    return None


def list_vanished_apps(udid: str | None, include_others: bool = False) -> dict:
    """Apps that are gone from this phone but can be put back: ones whose
    home-screen icon is still there, plus ones SideKit has seen installed on
    THIS phone before. Apps known only from other phones are counted but shown
    only on request - they are usually installable only by the account that
    owns them, so they belong behind a click rather than in the main list."""
    data = _run_device_script(_VANISHED_SCRIPT, udid, timeout=180)
    if not data:
        return {"ok": False, "error": "Не удалось прочитать список приложений с iPhone.", "apps": []}

    installed = set(data.get("installed", []))
    icons = list(dict.fromkeys(data.get("icons", [])))
    vanished = [
        b for b in icons
        if b not in installed
        and not b.startswith("com.apple.")
        and not HEX_ID.fullmatch(b)
    ]

    # Index files FIRST: any store id found inside one is written into the
    # known-apps record, and reading that record before the scan would miss
    # exactly those ids for a whole refresh.
    local = index_local_ipas()
    local_index = local["index"]

    known = load_known_apps()
    # Catalogue lookups are one HTTP request each and independent, so run a
    # handful at a time instead of a minute of strict single file.
    unknown = [b for b in vanished if b not in known or not known[b].get("item_id")]
    if unknown:
        from concurrent.futures import ThreadPoolExecutor
        with ThreadPoolExecutor(max_workers=8) as pool:
            for bundle_id, found in zip(unknown, pool.map(catalogue_lookup, unknown)):
                if found:
                    entry = known.get(bundle_id, {})
                    entry.update(found)
                    entry["source"] = "catalogue"
                    known[bundle_id] = entry
        save_known_apps(known)

    # Apps whose icon was deleted along with the app leave no trace on the
    # phone at all - nothing to compare against. But SideKit may still know
    # their store id from another phone or from a file on disk, and that is
    # enough to put them back. They belong in a separate group: they didn't
    # vanish from THIS phone, they're simply available for it.
    candidates = [
        bundle_id for bundle_id, entry in known.items()
        if entry.get("item_id")
        and bundle_id not in installed
        and bundle_id not in vanished
    ]

    # What belongs in this list is THIS phone's own history - apps SideKit has
    # seen installed here before and that are gone now. Everything else in the
    # memory came from other phones in the family and is just noise.
    #
    # An Apple licence can't be used to tell those apart: nearly all of these
    # apps are free, and Apple hands a licence to any account that asks, so
    # every app checks out as "available" no matter whose it was.
    library = [b for b in candidates if udid and udid in (known[b].get("seen_on") or [])]
    others = [b for b in candidates if b not in library]

    apps = []
    for bundle_id in vanished + library + (others if include_others else []):
        entry = known.get(bundle_id, {})
        local_file = local_index.get(bundle_id)
        apps.append({
            "bundle_id": bundle_id,
            "name": entry.get("name") or (local_file or {}).get("name") or bundle_id,
            "item_id": entry.get("item_id"),
            "version": entry.get("version", ""),
            "known_from": entry.get("source", "device" if entry.get("last_seen") else None),
            "local_ipa": local_file,
            "group": ("vanished" if bundle_id in vanished
                      else "library" if bundle_id in library else "other"),
        })
    # Recoverable first: App Store id, then a file on disk, then the rest.
    apps.sort(key=lambda a: (a["item_id"] is None and not a["local_ipa"],
                             a["item_id"] is None, a["name"].lower()))
    return {"ok": True, "apps": apps, "files_blocked": local["blocked"],
            "local_files": len(local_index),
            "vanished_count": len(vanished), "library_count": len(library),
            "others_count": len(others)}


# ---------------------------------------------------------------------------
# one-click restore: download the .ipa, install it, clean up
# ---------------------------------------------------------------------------

_restore_lock = threading.Lock()
_restore_state = {
    "running": False, "bundle_id": None, "name": None,
    "stage": "idle", "percent": 0, "error": None,
}


def get_restore_progress() -> dict:
    with _restore_lock:
        state = dict(_restore_state)
    # While downloading/installing, the real percentage lives in the job
    # states those steps already maintain.
    if state["stage"] == "download":
        download = get_download_progress()
        state["percent"] = download.get("percent", 0)
        state["paused"] = download.get("paused", False)
        state["downloaded"] = download.get("downloaded")
        state["total"] = download.get("total")
    elif state["stage"] == "install":
        state["percent"] = get_install_progress().get("percent", 0)
    return state


def _set_restore(**changes) -> None:
    with _restore_lock:
        _restore_state.update(changes)


_DISK_SPACE_SCRIPT = r'''
import asyncio, inspect, json, sys
from pymobiledevice3.lockdown import create_using_usbmux

async def main():
    udid = sys.argv[1] or None
    lockdown = create_using_usbmux(serial=udid) if udid else create_using_usbmux()
    if inspect.iscoroutine(lockdown):
        lockdown = await lockdown
    info = lockdown.get_value(domain="com.apple.disk_usage")
    if inspect.iscoroutine(info):
        info = await info
    print(json.dumps({
        "free": int(info.get("AmountDataAvailable") or 0),
        "total": int(info.get("TotalDataCapacity") or 0),
        "name": lockdown.short_info.get("DeviceName", "iPhone"),
    }))

asyncio.run(main())
'''

# iOS copies the .ipa onto the phone and then unpacks it, so it needs room
# for both at once - well over the file's own size. When it runs out, the
# error it returns is "PackageExtractionFailed: Could not extract archive",
# which says nothing about storage and sends people hunting for the wrong
# problem entirely.
SPACE_MULTIPLIER = 2.2


def check_free_space(ipa_path: Path, udid: str | None) -> str | None:
    try:
        size = ipa_path.stat().st_size
    except Exception:
        return None
    info = _run_device_script(_DISK_SPACE_SCRIPT, udid, timeout=60)
    if not info or not info.get("free"):
        return None

    needed = int(size * SPACE_MULTIPLIER)
    if info["free"] >= needed:
        return None

    gb = lambda value: f"{value / 1024 ** 3:.1f} ГБ".replace(".", ",")
    return (
        f"На телефоне «{info.get('name', 'iPhone')}» не хватает места.\n\n"
        f"Свободно: {gb(info['free'])}, а для установки нужно примерно "
        f"{gb(needed)} — iOS сначала копирует приложение на телефон, "
        f"а потом распаковывает, и на это время ей нужно место под обе копии.\n\n"
        "Освободи место на телефоне и нажми «Вернуть» ещё раз."
    )


def check_ios_compatibility(ipa_path: Path, udid: str | None) -> str | None:
    """None if the app can run on that phone, otherwise the reason. iOS
    refuses an app built for a newer system, and the refusal arrives as a
    stalled install rather than a clear message - so it is worth knowing
    before a single byte is pushed over the cable."""
    import plistlib
    import zipfile
    try:
        with zipfile.ZipFile(ipa_path) as archive:
            name = next(
                (n for n in archive.namelist()
                 if re.fullmatch(r"Payload/[^/]+\.app/Info\.plist", n)), None
            )
            if not name:
                return None
            needed = plistlib.loads(archive.read(name)).get("MinimumOSVersion")
    except Exception:
        return None
    if not needed:
        return None

    devices = list_devices().get("devices", [])
    device = next((d for d in devices if not udid or d.get("udid") == udid), None)
    have = (device or {}).get("ios")
    if not have or have == "?":
        return None

    def as_tuple(version: str) -> tuple:
        return tuple(int(part) for part in re.findall(r"\d+", version)[:3])

    try:
        if as_tuple(needed) > as_tuple(have):
            return (
                f"Приложению нужна iOS {needed}, а на телефоне "
                f"«{device.get('name', 'iPhone')}» стоит iOS {have}.\n\n"
                "Обнови iOS на телефоне — иначе установка просто зависнет."
            )
    except Exception:
        return None
    return None


def _run_restore_job(tool: str, bundle_id: str, item_id: int, name: str,
                     udid: str | None = None) -> None:
    # Downloaded into SideKit's own folder on purpose: macOS blocks this
    # process from reading ~/Desktop and ~/Downloads without an explicit
    # grant, and a restore must not depend on the user having given one.
    RESTORE_DIR.mkdir(parents=True, exist_ok=True)
    out_path = RESTORE_DIR / f"{bundle_id}.ipa"

    _set_restore(stage="download", percent=0)
    with _download_lock:
        _download_state.update({
            "running": True, "bundle_id": bundle_id, "percent": 0,
            "downloaded": None, "total": None, "status": "running",
            "path": str(out_path), "error": None, "raw": "",
        })
    try:
        rc, raw = _stream_ipatool_download(
            [tool, "download", "-i", str(item_id), "-o", str(out_path),
             "--format", "json", "--purchase"] + ipatool_keychain_args()
        )
    except Exception as e:
        with _download_lock:
            _download_state.update({"running": False, "status": "error", "error": str(e)})
        _set_restore(running=False, stage="error", error=f"Не удалось скачать: {e}")
        return

    if _download_cancelled:
        out_path.unlink(missing_ok=True)
        with _download_lock:
            _download_state.update({"running": False, "status": "cancelled", "paused": False})
        _set_restore(running=False, stage="cancelled", error=None)
        return

    ok = _download_succeeded(rc, raw, out_path)
    with _download_lock:
        _download_state.update({
            "running": False, "status": "done" if ok else "error",
            "error": None if ok else _extract_error_text(raw), "raw": raw,
        })
    if not ok:
        message = _extract_error_text(raw)
        if "license" in message.lower():
            message = (
                "У этого Apple ID нет лицензии на приложение — оно ни разу не "
                "скачивалось под этим аккаунтом, поэтому Apple его не отдаёт."
            )
        _set_restore(running=False, stage="error", error=message)
        out_path.unlink(missing_ok=True)
        return

    # Both checks happen with the file already downloaded but before a byte
    # goes over the cable, and the file is KEPT when they fail: the download
    # was fine, so making the user wait through it again to retry would be
    # punishing them for the phone's state.
    problem = check_ios_compatibility(out_path, udid) or check_free_space(out_path, udid)
    if problem:
        _set_restore(running=False, stage="error",
                     error=problem + f"\n\nСкачанный файл сохранён: {out_path}")
        return

    _set_restore(stage="install", percent=0)
    # _run_install_job is normally started via install_ipa(), which is what
    # marks the job as running - and the progress parser ignores lines while
    # it isn't. Calling the worker directly means setting that up here.
    with _install_lock:
        _install_state.update({
            "running": True, "percent": 0, "status": "running", "error": None, "raw": "",
        })
    # The udid matters: with two phones plugged in, an install with no target
    # lands on whichever one the library picks first - which is how an app
    # can be "installed" onto the wrong device, or onto none at all.
    _run_install_job(str(out_path), udid)
    install = get_install_progress()

    if install.get("status") == "done":
        out_path.unlink(missing_ok=True)
        _set_restore(running=False, stage="done", percent=100, error=None)
    elif install.get("status") == "cancelled":
        out_path.unlink(missing_ok=True)
        _set_restore(running=False, stage="cancelled", error=None)
    else:
        # Keep the file after a failed install - it took minutes to fetch and
        # the next attempt can use it straight from disk.
        error = install.get("error") or "Установка не удалась"
        if "extract" in error.lower() or "PackageExtractionFailed" in error:
            error = (
                "iPhone не смог распаковать приложение.\n\n"
                "Почти всегда это нехватка места на телефоне: iOS нужно место "
                "и под сам файл, и под распакованное приложение. Освободи "
                "несколько гигабайт и попробуй снова."
            )
        _set_restore(running=False, stage="error",
                     error=error + f"\n\nСкачанный файл сохранён: {out_path}")


def restore_app(bundle_id: str, item_id: int | None, name: str | None,
                udid: str | None = None) -> dict:
    tool = find_tool("ipatool")
    if not tool:
        return {"ok": False, "error": "ipatool не установлен"}

    known = load_known_apps()
    if not item_id:
        item_id = (known.get(bundle_id) or {}).get("item_id")
    if not item_id:
        found = catalogue_lookup(bundle_id)
        if found:
            item_id = found["item_id"]
            entry = known.get(bundle_id, {})
            entry.update(found)
            entry["source"] = "catalogue"
            known[bundle_id] = entry
            save_known_apps(known)
    if not item_id:
        return {
            "ok": False, "need_item_id": True,
            "error": (
                "Не удалось определить App Store ID: приложения нет ни в каталоге "
                "App Store, ни в памяти SideKit. Впиши ID вручную — его можно найти "
                "в интернете по названию приложения (в адресе страницы App Store "
                "число после «id»)."
            ),
        }

    # An id typed in by hand is worth remembering too - next time it just works.
    entry = known.get(bundle_id, {})
    entry["item_id"] = int(item_id)
    if name:
        entry.setdefault("name", name)
    entry.setdefault("source", "manual")
    known[bundle_id] = entry
    save_known_apps(known)

    with _restore_lock:
        if _restore_state["running"]:
            return {"ok": False, "error": "Уже идёт восстановление — дождись завершения."}
        _restore_state.update({
            "running": True, "bundle_id": bundle_id, "name": name or bundle_id,
            "stage": "starting", "percent": 0, "error": None,
        })
    threading.Thread(
        target=_run_restore_job,
        args=(tool, bundle_id, int(item_id), name or bundle_id, udid),
        daemon=True,
    ).start()
    return {"ok": True, "started": True, "item_id": int(item_id)}


# The running download, so it can be paused or called off. A download is a
# child process writing to a file: SIGSTOP/SIGCONT freeze and thaw it exactly
# where it stands, and killing it plus deleting the half-written file is a
# clean cancel.
_download_proc = None
_download_cancelled = False


def _freeze_process(proc, resume: bool) -> None:
    """Замораживает и размораживает скачивание. SIGSTOP/SIGCONT существуют
    только в Unix - на Windows обращение к ним просто падало, и кнопки паузы
    и отмены не делали ничего. Там то же самое умеет ntdll."""
    if IS_WINDOWS:
        PROCESS_ALL_ACCESS = 0x1F0FFF
        handle = ctypes.windll.kernel32.OpenProcess(PROCESS_ALL_ACCESS, False, proc.pid)
        if not handle:
            raise OSError("не получилось обратиться к процессу загрузки")
        try:
            call = (ctypes.windll.ntdll.NtResumeProcess if resume
                    else ctypes.windll.ntdll.NtSuspendProcess)
            status = call(handle)
            if status != 0:
                raise OSError("ntdll ответил " + hex(status & 0xFFFFFFFF))
        finally:
            ctypes.windll.kernel32.CloseHandle(handle)
        return
    proc.send_signal(signal.SIGCONT if resume else signal.SIGSTOP)


def _kill_process(proc) -> None:
    """Завершает скачивание вместе с тем, что оно успело породить."""
    if IS_WINDOWS:
        try:
            subprocess.run(["taskkill", "/PID", str(proc.pid), "/T", "/F"],
                           capture_output=True, timeout=15, **NO_CONSOLE)
            return
        except Exception:
            pass
    try:
        proc.terminate()
    except Exception:
        pass


def control_download(action: str) -> dict:
    global _download_cancelled
    proc = _download_proc
    if proc is None or proc.poll() is not None:
        return {"ok": False, "error": "Сейчас ничего не скачивается."}
    try:
        if action == "pause":
            _freeze_process(proc, resume=False)
            _set_download(paused=True)
        elif action == "resume":
            _freeze_process(proc, resume=True)
            _set_download(paused=False)
        elif action == "cancel":
            _download_cancelled = True
            # Замороженный процесс не отреагирует на просьбу завершиться,
            # пока его не разбудят.
            try:
                _freeze_process(proc, resume=True)
            except Exception:
                pass
            _kill_process(proc)
            _set_download(paused=False)
        else:
            return {"ok": False, "error": "Неизвестное действие"}
    except Exception as e:
        return {"ok": False, "error": str(e)}
    return {"ok": True}


def _set_download(**changes) -> None:
    with _download_lock:
        _download_state.update(changes)


def _stream_ipatool_download(cmd: list) -> tuple[int, str]:
    """Runs one ipatool download, feeding its progress bar into
    _download_state as it goes. Returns (exit code, full output)."""
    global _download_proc, _download_cancelled
    chunks: list = []
    _download_cancelled = False
    proc = subprocess.Popen(
        cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True, bufsize=1, **NO_CONSOLE)
    _download_proc = proc
    try:
        buf = ""
        while True:
            piece = proc.stdout.read(256)
            if not piece:
                break
            chunks.append(piece)
            buf += piece
            parts = re.split(r"[\r\n]", buf)
            buf = parts[-1]
            for part in parts[:-1]:
                _apply_progress_line(part)
            _apply_progress_line(buf)
        return proc.wait(timeout=30), "".join(chunks)
    finally:
        _download_proc = None


def _download_succeeded(rc: int, raw: str, out_path: Path) -> bool:
    # ipatool's own JSON "success" field is more trustworthy than the exit
    # code; fall back to the exit code when there's no JSON to read.
    for line in reversed(raw.strip().splitlines()):
        line = line.strip()
        if line.startswith("{"):
            try:
                success = json.loads(line).get("success")
                if success is not None:
                    return bool(success) and out_path.exists()
            except Exception:
                pass
            break
    return rc == 0 and out_path.exists()


def _run_download_job(tool: str, bundle_id: str, purchase: bool, out_path: Path,
                      udid: str | None = None) -> None:
    # Deliberately NOT passing --non-interactive: that flag is what makes
    # ipatool skip creating its own progress bar. Download doesn't need a
    # terminal for anything else (no password/2FA prompt happens here,
    # that's only in `auth login`), so this is the only way to get a real
    # 0-100% number straight from ipatool's own byte counter instead of
    # faking a progress bar client-side.
    common = ["-o", str(out_path), "--format", "json"] + ipatool_keychain_args()
    if purchase:
        common += ["--purchase"]

    try:
        rc, raw = _stream_ipatool_download([tool, "download", "-b", bundle_id] + common)
    except Exception as e:
        with _download_lock:
            _download_state.update({"running": False, "status": "error", "error": str(e)})
        return

    # A cancelled download exits non-zero with a half-written file - that is
    # the user's own doing, not a failure to report as one.
    if _download_cancelled:
        out_path.unlink(missing_ok=True)
        with _download_lock:
            _download_state.update({
                "running": False, "status": "cancelled", "paused": False,
                "error": None, "path": None,
            })
        return

    ok = _download_succeeded(rc, raw, out_path)

    # "app not found" means the App Store catalogue has no entry for this
    # bundle id - which is what happens to apps that were pulled from the
    # store (Avito, Tinkoff and friends). Looking the app up BY BUNDLE ID is
    # what fails; downloading by numeric id still works if the account has a
    # license, and the connected iPhone can tell us that id.
    if not ok and "app not found" in raw.lower():
        item_id = device_app_item_id(bundle_id, udid)
        if item_id:
            with _download_lock:
                _download_state.update({"percent": 0, "downloaded": None, "total": None})
            try:
                rc, retry_raw = _stream_ipatool_download(
                    [tool, "download", "-i", str(item_id)] + common
                )
                raw = raw + "\n" + retry_raw
                ok = _download_succeeded(rc, retry_raw, out_path)
            except Exception as e:
                raw = raw + f"\nповтор по App Store ID {item_id} не удался: {e}"
        else:
            raw += (
                "\nЭтого приложения нет в каталоге App Store, и найти его "
                "App Store ID на подключённом iPhone тоже не вышло."
            )

    error_text = None
    if not ok:
        error_text = _extract_error_text(raw)
        low = error_text.lower()
        if _looks_like_lost_session(error_text):
            # ipatool can no longer read its saved Apple ID session. SideKit
            # tracks login separately (a local file, so that checking it
            # doesn't trigger a Keychain prompt), and that record is now
            # lying - clear it so the app asks for a login instead of
            # failing every download at 0% while claiming to be signed in.
            _clear_login_state()
            _invalidate_auth_status()
            error_text = (
                "Сессия Apple ID потеряна — ipatool больше не видит сохранённый вход.\n"
                "Войди в Apple ID заново, после этого выгрузка заработает."
            )
        elif "app not found" in low:
            error_text = (
                "Этого приложения больше нет в каталоге App Store — его оттуда удалили.\n"
                "SideKit попробовал обойти это, взяв App Store ID прямо с подключённого "
                "iPhone, но не получилось: либо приложение на телефоне не установлено, "
                "либо оно попало туда не из App Store."
            )
        elif "license" in low:
            error_text += (
                "\n\nУ этого Apple ID нет лицензии на приложение — оно ни разу не "
                "скачивалось под этим аккаунтом, а раз его убрали из App Store, "
                "получить лицензию заново уже нельзя."
            )
        elif "not available" in low or "unavailable" in low or "region" in low:
            error_text += (
                "\n\nПохоже, это приложение недоступно в App Store для аккаунта "
                "или региона, с которого выполнен вход."
            )

    with _download_lock:
        _download_state.update({
            "running": False,
            "status": "done" if ok else "error",
            "percent": 100 if ok else _download_state.get("percent", 0),
            "path": str(out_path) if ok else None,
            "error": error_text,
            "raw": raw,
        })


def ipatool_download(bundle_id: str, purchase: bool, dest_path: str | None) -> dict:
    """Starts the download as a background job instead of blocking, so the
    frontend can poll /api/download-progress for a real percentage instead
    of staring at an indeterminate spinner."""
    tool = find_tool("ipatool")
    if not tool:
        return {"ok": False, "error": "ipatool не установлен"}
    with _download_lock:
        if _download_state["running"]:
            return {"ok": False, "error": "Уже что-то выгружается — дождись завершения."}
        out_path = Path(dest_path) if dest_path else (DOWNLOADS_DIR / f"{bundle_id}.ipa")
        problem = check_writable_dir(out_path.parent)
        if problem:
            return {"ok": False, "error": problem}
        _download_state.update({
            "running": True, "bundle_id": bundle_id, "percent": 0,
            "downloaded": None, "total": None, "status": "running",
            "path": str(out_path), "error": None, "raw": "",
        })
    threading.Thread(target=_run_download_job, args=(tool, bundle_id, purchase, out_path), daemon=True).start()
    return {"ok": True, "started": True}


def get_download_progress() -> dict:
    with _download_lock:
        return dict(_download_state)


def list_downloaded_ipas() -> list:
    if not DOWNLOADS_DIR.exists():
        return []
    return sorted(str(p) for p in DOWNLOADS_DIR.glob("*.ipa"))


# ---------------------------------------------------------------------------
# pymobiledevice3-backed actions
# ---------------------------------------------------------------------------

def list_devices() -> dict:
    # --usb restricts this to devices physically plugged in right now.
    # Without it, usbmuxd also reports devices it remembers over Wi-Fi
    # sync (even ones that used to be connected and are just on the same
    # network now), which is not what "what's plugged in" should mean here.
    rc_simple, out_simple, err_simple = pmd3("usbmux", "list", "--simple", "--usb", timeout=15)
    udids: list[str] = []
    try:
        udids = json.loads(out_simple)
    except Exception:
        pass
    udids = list(dict.fromkeys(udids))  # de-dupe, keep order

    if not udids:
        # Nothing physically detected at the USB level - a real "not
        # connected / bad cable" situation, not a trust problem.
        return {"ok": rc_simple == 0, "devices": [], "raw": out_simple + err_simple}

    # Step 2: try to get friendly details (name/model/iOS version), which
    # DOES require the pairing/trust dialog to have been accepted. If this
    # fails, we still know from step 1 that something is plugged in, so we
    # show it with a "needs trust" flag instead of hiding it entirely.
    rc_full, out_full, err_full = pmd3("usbmux", "list", "--usb", timeout=30)
    devices = []
    seen_udids = set()
    try:
        raw = json.loads(out_full)
        for d in raw:
            udid = d.get("UniqueDeviceID") or d.get("SerialNumber") or ""
            if udid in seen_udids:
                continue  # same device reported more than once - skip
            seen_udids.add(udid)
            devices.append({
                "udid": udid,
                "name": d.get("DeviceName", "?"),
                "product": d.get("ProductType", "?"),
                "ios": d.get("ProductVersion", "?"),
                "needs_trust": False,
            })
        for udid in udids:
            if udid not in seen_udids:
                devices.append({
                    "udid": udid, "name": "iPhone/iPad (не подтверждено доверие)",
                    "product": "?", "ios": "?", "needs_trust": True,
                })
    except Exception:
        # Full lookup failed entirely (typically: trust not yet accepted on
        # ANY of the connected devices) - fall back to showing bare UDIDs
        # so the user at least sees "something is connected".
        for udid in udids:
            devices.append({
                "udid": udid, "name": "iPhone/iPad (не подтверждено доверие)",
                "product": "?", "ios": "?", "needs_trust": True,
            })

    return {"ok": True, "devices": devices, "raw": out_full + err_full}


_install_lock = threading.Lock()
_install_state = {"running": False, "percent": 0, "status": "idle", "error": None, "raw": ""}


def _apply_install_progress_line(line: str) -> None:
    # pymobiledevice3 logs lines like "42% Complete" while installing
    # (from installation_proxy's own completion watcher) - same idea as
    # ipatool's download progress bar, just a different tool/format.
    m = re.search(r"(\d{1,3})\s*%", line)
    if not m:
        return
    percent = min(100, max(0, int(m.group(1))))
    with _install_lock:
        if not _install_state["running"]:
            return
        _install_state["percent"] = max(_install_state["percent"], percent)


# How long an install may sit at the same percentage before it is declared
# stuck. A real install streams the whole .ipa across USB and then reports
# steady progress; several minutes of complete silence means it is waiting on
# something that will never arrive (a locked phone, a device that went away),
# and hanging there forever is worse than saying so.
INSTALL_STALL_SECONDS = 240

_install_proc = None
_install_cancelled = False


def cancel_install() -> dict:
    global _install_cancelled
    proc = _install_proc
    if proc is None or proc.poll() is not None:
        return {"ok": False, "error": "Сейчас ничего не устанавливается."}
    _install_cancelled = True
    try:
        proc.terminate()
    except Exception as e:
        return {"ok": False, "error": str(e)}
    return {"ok": True}


def _run_install_job(ipa_path: str, udid: str | None) -> None:
    global _install_proc, _install_cancelled
    args = [PYTHON_EXE, "-W", "ignore", "-m", "pymobiledevice3", "apps", "install", ipa_path]
    if udid:
        args += ["--udid", udid]
    chunks = []
    _install_cancelled = False
    stalled = {"flag": False}
    try:
        proc = subprocess.Popen(
            args, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True, bufsize=1, **NO_CONSOLE)
        _install_proc = proc

        def watchdog():
            last_seen = (-1, time.time())
            while proc.poll() is None:
                time.sleep(5)
                with _install_lock:
                    percent = _install_state.get("percent", 0)
                if percent != last_seen[0]:
                    last_seen = (percent, time.time())
                elif time.time() - last_seen[1] > INSTALL_STALL_SECONDS:
                    stalled["flag"] = True
                    try:
                        proc.terminate()
                    except Exception:
                        pass
                    return

        threading.Thread(target=watchdog, daemon=True).start()

        buf = ""
        while True:
            piece = proc.stdout.read(256)
            if not piece:
                break
            chunks.append(piece)
            buf += piece
            parts = re.split(r"[\r\n]", buf)
            buf = parts[-1]
            for part in parts[:-1]:
                _apply_install_progress_line(part)
            _apply_install_progress_line(buf)
        rc = proc.wait(timeout=30)
    except Exception as e:
        with _install_lock:
            _install_state.update({"running": False, "status": "error", "error": str(e)})
        return
    finally:
        _install_proc = None

    raw = "".join(chunks)
    ok = rc == 0 and not stalled["flag"] and not _install_cancelled

    if _install_cancelled:
        error = None
        status = "cancelled"
    elif stalled["flag"]:
        status = "error"
        error = (
            "Установка встала и не двигалась несколько минут.\n\n"
            "Обычно это значит, что iPhone заблокирован или отключился. "
            "Разблокируй телефон, держи его подключённым и попробуй ещё раз."
        )
    else:
        status = "done" if ok else "error"
        error = None if ok else (_clean_python_traceback(raw) or _extract_error_text(raw))

    with _install_lock:
        _install_state.update({
            "running": False,
            "status": status,
            "percent": 100 if ok else _install_state.get("percent", 0),
            "error": error,
            "raw": raw,
        })


def install_ipa(ipa_path: str, udid: str | None) -> dict:
    """Starts install as a background job (same pattern as the export
    download) so the frontend can show a real progress bar instead of an
    indeterminate spinner."""
    problem = (check_readable(ipa_path)
               or check_ios_compatibility(Path(ipa_path), udid)
               or check_free_space(Path(ipa_path), udid))
    if problem:
        return {"ok": False, "error": problem}
    with _install_lock:
        if _install_state["running"]:
            return {"ok": False, "error": "Уже что-то устанавливается — дождись завершения."}
        _install_state.update({"running": True, "percent": 0, "status": "running", "error": None, "raw": ""})
    threading.Thread(target=_run_install_job, args=(ipa_path, udid), daemon=True).start()
    return {"ok": True, "started": True}


def get_install_progress() -> dict:
    with _install_lock:
        return dict(_install_state)


def uninstall_app(bundle_id: str, udid: str | None) -> dict:
    args = ["apps", "uninstall", bundle_id]
    if udid:
        args += ["--udid", udid]
    rc, out, err = pmd3(*args, timeout=60)
    return {"ok": rc == 0, "raw": out + err}


def list_apps(udid: str | None, include_system: bool) -> dict:
    args = ["apps", "list", "--type", "Any" if include_system else "User"]
    if udid:
        args += ["--udid", udid]
    rc, out, err = pmd3(*args, timeout=60)
    apps = []
    try:
        raw = json.loads(out)
        for bundle_id, info in raw.items():
            apps.append({
                "bundle_id": bundle_id,
                "name": info.get("CFBundleDisplayName") or info.get("CFBundleName") or bundle_id,
                "version": info.get("CFBundleShortVersionString", ""),
                "system": info.get("ApplicationType") != "User",
            })
        apps.sort(key=lambda a: a["name"].lower())
    except Exception:
        pass
    return {"ok": rc == 0, "apps": apps, "raw": out + err}


# ---------------------------------------------------------------------------
# app icons
#
# The device itself is the only place these can come from: apps pulled from
# the App Store (and anything sideloaded) have no catalogue artwork left to
# fetch, but SpringBoard still hands over exactly the icon shown on the home
# screen. Fetching happens once per app and is cached on disk, because each
# icon is a separate round trip over USB - fine as a one-off, far too slow to
# repeat every time the list is drawn.
# ---------------------------------------------------------------------------

ICONS_DIR = LOCK_DIR / "icons"
SAFE_BUNDLE_ID = re.compile(r"[A-Za-z0-9._-]{1,200}")

_ICONS_SCRIPT = r'''
import asyncio, inspect, json, pathlib, sys
from pymobiledevice3.lockdown import create_using_usbmux
from pymobiledevice3.services.springboard import SpringBoardServicesService

async def main():
    out_dir = pathlib.Path(sys.argv[1])
    udid = sys.argv[2] or None
    bundle_ids = json.loads(sys.stdin.read())
    lockdown = create_using_usbmux(serial=udid) if udid else create_using_usbmux()
    if inspect.iscoroutine(lockdown):
        lockdown = await lockdown
    springboard = SpringBoardServicesService(lockdown)
    connect = getattr(springboard, "connect", None)
    if connect:
        opened = connect()
        if inspect.iscoroutine(opened):
            await opened
    for bundle_id in bundle_ids:
        try:
            data = springboard.get_icon_pngdata(bundle_id)
            if inspect.iscoroutine(data):
                data = await data
            data = bytes(data)
            # Only keep real PNGs - a failed lookup can come back as an
            # empty or truncated blob, and a broken file in the cache would
            # never be retried.
            if data.startswith(b"\x89PNG\r\n\x1a\n"):
                (out_dir / (bundle_id + ".png")).write_bytes(data)
        except Exception:
            pass

asyncio.run(main())
'''

_icons_lock = threading.Lock()
_icons_fetching = False


def icon_path(bundle_id: str) -> Path:
    return ICONS_DIR / f"{bundle_id}.png"


# While an app is still installing, iOS hands out a placeholder instead of its
# icon - the grey wireframe grid. Cached forever, that placeholder becomes the
# app's face in SideKit even years later. The giveaway is weight: the
# placeholder is ~11 KB where real icons run 30-70 KB.
PLACEHOLDER_ICON_LIMIT = 20 * 1024
ICON_RECHECK_SECONDS = 0


def icon_needs_refresh(bundle_id: str) -> bool:
    path = icon_path(bundle_id)
    try:
        stats = path.stat()
    except OSError:
        return True   # нет файла
    if stats.st_size >= PLACEHOLDER_ICON_LIMIT:
        return False
    # Suspiciously small: ask the phone again, but not on every refresh - some
    # icons really are this simple, and re-fetching those forever is waste.
    return time.time() - stats.st_mtime > ICON_RECHECK_SECONDS


def prefetch_icons(bundle_ids: list, udid: str | None) -> None:
    """Kick off a background fetch for every icon not already cached. One
    subprocess handles the whole batch over a single device connection."""
    global _icons_fetching
    with _icons_lock:
        if _icons_fetching:
            return
        missing = [
            b for b in bundle_ids
            if SAFE_BUNDLE_ID.fullmatch(b or "") and icon_needs_refresh(b)
        ]
        if not missing:
            return
        # Claimed before the thread starts, so an icon request arriving
        # immediately after knows to wait rather than give up.
        _icons_fetching = True

    def job():
        global _icons_fetching
        try:
            ICONS_DIR.mkdir(parents=True, exist_ok=True)
            subprocess.run(
                [PYTHON_EXE, "-W", "ignore", "-c", _ICONS_SCRIPT, str(ICONS_DIR), udid or ""],
                input=json.dumps(missing), text=True, capture_output=True, timeout=600, **NO_CONSOLE)
        except Exception:
            pass
        finally:
            with _icons_lock:
                _icons_fetching = False

    threading.Thread(target=job, daemon=True).start()


def read_cached_icon(bundle_id: str, wait_seconds: float = 45.0) -> bytes | None:
    """The cached icon, waiting for the batch fetch to reach this app if one
    is still running."""
    if not SAFE_BUNDLE_ID.fullmatch(bundle_id or ""):
        return None
    path = icon_path(bundle_id)
    deadline = time.time() + wait_seconds
    while True:
        if path.exists():
            try:
                return path.read_bytes()
            except Exception:
                return None
        with _icons_lock:
            still_fetching = _icons_fetching
        if not still_fetching or time.time() > deadline:
            return None
        time.sleep(0.25)


def _tk_dialog(kind: str, title: str, default_name: str = "") -> dict:
    """File dialogs on Windows, drawn by the Tk toolkit that ships with
    Python. Runs in a separate process because Tk insists on owning the main
    thread, which this server's is not."""
    script = (
        "import sys, tkinter as tk\n"
        "from tkinter import filedialog\n"
        "root = tk.Tk(); root.withdraw(); root.attributes('-topmost', True)\n"
        "kind, title, name = sys.argv[1], sys.argv[2], sys.argv[3]\n"
        "if kind == 'open':\n"
        "    path = filedialog.askopenfilename(title=title,\n"
        "        filetypes=[('Приложения iOS', '*.ipa'), ('Все файлы', '*.*')])\n"
        "else:\n"
        "    path = filedialog.asksaveasfilename(title=title, initialfile=name,\n"
        "        defaultextension='.ipa', filetypes=[('Приложения iOS', '*.ipa')])\n"
        "print(path or '')\n"
    )
    try:
        result = subprocess.run(
            [PYTHON_EXE, "-c", script, kind, title, default_name],
            capture_output=True, text=True, timeout=600, **NO_CONSOLE)
    except Exception as e:
        return {"ok": False, "error": str(e)}
    path = (result.stdout or "").strip()
    if not path:
        return {"ok": False, "cancelled": True}
    return {"ok": True, "path": path}


def desktop_dir() -> Path:
    """Рабочий стол - место, куда выгруженный .ipa попадает без вопросов."""
    candidate = Path(os.environ.get("USERPROFILE", Path.home())) / "Desktop" if IS_WINDOWS \
        else Path.home() / "Desktop"
    return candidate if candidate.is_dir() else Path.home()


def auto_ipa_path(name: str, bundle_id: str) -> Path:
    """Имя файла по названию приложения. Если такой уже лежит - добавляется
    номер, чтобы прошлая выгрузка не затиралась молча."""
    base = (name or bundle_id or "app").strip()
    for bad in '/\\:*?"<>|':
        base = base.replace(bad, "-")
    base = base.strip(". ") or "app"
    folder = desktop_dir()
    target = folder / (base + ".ipa")
    n = 2
    while target.exists():
        target = folder / f"{base} ({n}).ipa"
        n += 1
    return target


def pick_ipa_files() -> dict:
    """Выбор сразу нескольких .ipa: один раз показал файлы - и все они уходят
    в очередь на установку, без возвращения к диалогу за каждым."""
    if IS_WINDOWS:
        script = (
            "import tkinter as tk\n"
            "from tkinter import filedialog\n"
            "root = tk.Tk(); root.withdraw(); root.attributes('-topmost', True)\n"
            "paths = filedialog.askopenfilenames(title='Выбери .ipa файлы',\n"
            "    filetypes=[('Приложения iOS', '*.ipa'), ('Все файлы', '*.*')])\n"
            "print('\\n'.join(paths))\n"
        )
        try:
            result = subprocess.run([PYTHON_EXE, "-c", script],
                                    capture_output=True, text=True, timeout=600, **NO_CONSOLE)
        except Exception as e:
            return {"ok": False, "error": str(e)}
        out = result.stdout or ""
    else:
        script = (
            "activate\n"
            'set chosen to choose file with prompt "Выбери .ipa файлы" '
            "with multiple selections allowed\n"
            'set out to ""\n'
            "repeat with f in chosen\n"
            "    set out to out & POSIX path of f & linefeed\n"
            "end repeat\n"
            "return out"
        )
        try:
            result = subprocess.run(["osascript", "-e", script],
                                    capture_output=True, text=True, timeout=None, **NO_CONSOLE)
        except Exception as e:
            return {"ok": False, "error": str(e)}
        if result.returncode != 0:
            return {"ok": False, "cancelled": True}
        out = result.stdout or ""

    paths = [line.strip() for line in out.splitlines() if line.strip()]
    ipas = [x for x in paths if x.lower().endswith(".ipa")]
    if not paths:
        return {"ok": False, "cancelled": True}
    if not ipas:
        return {"ok": False, "error": "Среди выбранного нет файлов .ipa."}
    return {"ok": True, "paths": ipas, "skipped": len(paths) - len(ipas)}


def pick_file_dialog(file_type: str = "ipa") -> dict:
    if IS_WINDOWS:
        return _tk_dialog("open", "Выбери .ipa файл")
    return _pick_file_dialog_mac(file_type)


def _pick_file_dialog_mac(file_type: str = "ipa") -> dict:
    """Opens a native macOS "choose file" dialog and blocks until the user
    picks something or cancels. This is what gives the user a normal Finder
    file browser instead of anything happening in a terminal."""
    # `activate` first: without it this dialog can open BEHIND SideKit's own
    # window (the osascript process isn't frontmost), which looks exactly
    # like the app freezing - the click does nothing visible and the UI is
    # blocked waiting on a dialog nobody can see.
    script = (
        "activate\n"
        'set chosen to choose file with prompt "Выбери .ipa файл" '
        f'of type {{"{file_type}"}}\n'
        "POSIX path of chosen"
    )
    try:
        result = subprocess.run(
            ["osascript", "-e", script], capture_output=True, text=True, timeout=None, **NO_CONSOLE)
        path = result.stdout.strip()
        if result.returncode != 0 or not path:
            return {"ok": False, "cancelled": True}
        return {"ok": True, "path": path}
    except Exception as e:
        return {"ok": False, "error": str(e)}


def pick_save_path_dialog(default_name: str) -> dict:
    if IS_WINDOWS:
        safe_name = (default_name or "app.ipa").strip() or "app.ipa"
        if not safe_name.lower().endswith(".ipa"):
            safe_name += ".ipa"
        return _tk_dialog("save", "Куда сохранить .ipa?", safe_name)
    return _pick_save_path_dialog_mac(default_name)


def _pick_save_path_dialog_mac(default_name: str) -> dict:
    """Native macOS "Save As" dialog - the user picks the exact file (not
    just a folder) the .ipa gets written to, instead of it silently landing
    in some fixed app-managed folder they'd have to go hunting for."""
    safe_name = (default_name or "app.ipa").replace('"', "").strip() or "app.ipa"
    if not safe_name.lower().endswith(".ipa"):
        safe_name += ".ipa"
    default_dir = str(Path.home() / "Downloads")
    script = (
        "activate\n"  # same reason as in pick_file_dialog()
        'set chosen to choose file name with prompt "Куда сохранить .ipa?" '
        f'default name "{safe_name}" default location (POSIX file "{default_dir}")\n'
        "POSIX path of chosen"
    )
    try:
        result = subprocess.run(
            ["osascript", "-e", script], capture_output=True, text=True, timeout=None, **NO_CONSOLE)
        path = result.stdout.strip()
        if result.returncode != 0 or not path:
            return {"ok": False, "cancelled": True}
        return {"ok": True, "path": path}
    except Exception as e:
        return {"ok": False, "error": str(e)}


def reveal_in_finder(path: str) -> dict:
    try:
        if IS_WINDOWS:
            # explorer needs the comma glued to the switch, and it returns a
            # non-zero exit code even when it works - so its result is ignored.
            subprocess.run(["explorer", f"/select,{Path(path)}"], timeout=10, **NO_CONSOLE)
        else:
            subprocess.run(["open", "-R", path], timeout=10, **NO_CONSOLE)
        return {"ok": True}
    except Exception as e:
        return {"ok": False, "error": str(e)}


# ---------------------------------------------------------------------------
# zsign-backed action (only needed for non-App-Store ipas)
# ---------------------------------------------------------------------------

def sign_ipa(ipa_path: str, cert_path: str, cert_password: str, profile_path: str, output_path: str | None) -> dict:
    tool = find_tool("zsign")
    if not tool:
        return {"ok": False, "error": "zsign не установлен"}
    out_path = output_path or str(Path(ipa_path).with_name(Path(ipa_path).stem + "-signed.ipa"))
    cmd = [tool, "-c", cert_path, "-p", cert_password or "", "-m", profile_path, "-o", out_path, ipa_path]
    rc, out, err = run(cmd, timeout=180)
    return {"ok": rc == 0, "path": out_path if rc == 0 else None, "raw": out + err}


# ---------------------------------------------------------------------------
# HTTP server
# ---------------------------------------------------------------------------

class Handler(BaseHTTPRequestHandler):
    protocol_version = "HTTP/1.1"

    def log_message(self, fmt, *args):
        pass  # keep quiet, there's no visible terminal anyway

    def _send_json(self, obj, status=200):
        body = json.dumps(obj, ensure_ascii=False).encode("utf-8")
        self.send_response(status)
        self.send_header("Content-Type", "application/json; charset=utf-8")
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        self.wfile.write(body)

    def _send_html(self, html: str):
        body = html.encode("utf-8")
        self.send_response(200)
        self.send_header("Content-Type", "text/html; charset=utf-8")
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        self.wfile.write(body)

    def _read_json_body(self) -> dict:
        length = int(self.headers.get("Content-Length", 0))
        if length == 0:
            return {}
        raw = self.rfile.read(length)
        try:
            return json.loads(raw)
        except Exception:
            return {}

    def do_GET(self):
        try:
            path = self.path.split("?")[0]
            query = {}
            if "?" in self.path:
                from urllib.parse import parse_qs
                query = {k: v[0] for k, v in parse_qs(self.path.split("?", 1)[1]).items()}

            if path == "/":
                self._send_html(active_index_html().read_text(encoding="utf-8"))
            elif path == "/favicon.ico":
                # Окно на Windows рисует Edge, и без своей иконки он ставит
                # свою. Отдаём иконку приложения - она попадает и в заголовок
                # окна, и в панель задач.
                icon = RESOURCES_DIR / "SideKit.ico"
                if icon.exists():
                    body = icon.read_bytes()
                    self.send_response(200)
                    self.send_header("Content-Type", "image/x-icon")
                    self.send_header("Content-Length", str(len(body)))
                    self.send_header("Cache-Control", "max-age=86400")
                    self.end_headers()
                    self.wfile.write(body)
                else:
                    self.send_response(204)
                    self.end_headers()
            elif path == "/api/report-progress":
                self._send_json(report_state())
            elif path == "/api/setup-progress":
                from urllib.parse import parse_qs, urlparse
                step = (parse_qs(urlparse(self.path).query).get("step") or [""])[0]
                self._send_json(setup_step_state(step))
            elif path == "/api/status":
                status = get_status()
                status["version"] = SERVER_VERSION
                status["update"] = update_note()
                self._send_json(status)
            elif path == "/api/devices":
                devices = list_devices()
                # The moment a phone is seen, write down what's on it. Waiting
                # for the user to open a particular screen would mean losing
                # the ids of apps that vanish before they ever do.
                for device in devices.get("devices", []):
                    if not device.get("needs_trust"):
                        remember_installed_apps(None, device.get("udid"))
                        break
                self._send_json(devices)
            elif path == "/api/apps":
                result = list_apps(query.get("udid"), query.get("system") == "1")
                # Start pulling icons for exactly the apps about to be shown,
                # so they're already on their way by the time the page asks.
                if result.get("apps"):
                    bundle_ids = [a["bundle_id"] for a in result["apps"]]
                    prefetch_icons(bundle_ids, query.get("udid"))
                    # Record their App Store ids while the apps are still
                    # here to be asked - that record is the only way back if
                    # one of them disappears later.
                    remember_installed_apps(bundle_ids, query.get("udid"))
                self._send_json(result)
            elif path == "/api/vanished-apps":
                remember_installed_apps(None, query.get("udid"))
                result = list_vanished_apps(query.get("udid"), query.get("all") == "1")
                # The phone still holds the home-screen icon of a vanished
                # app, so this list can look like the home screen too - but
                # nothing has asked for those icons before now.
                if result.get("apps"):
                    prefetch_icons([a["bundle_id"] for a in result["apps"]], query.get("udid"))
                self._send_json(result)
            elif path == "/api/restore-progress":
                self._send_json(get_restore_progress())
            elif path == "/api/app-icon":
                icon = read_cached_icon(query.get("bundle_id", ""))
                if icon is None:
                    self._send_json({"error": "no icon"}, status=404)
                else:
                    self.send_response(200)
                    self.send_header("Content-Type", "image/png")
                    self.send_header("Content-Length", str(len(icon)))
                    self.send_header("Cache-Control", "max-age=86400")
                    self.end_headers()
                    self.wfile.write(icon)
            elif path == "/api/memory-stats":
                known = load_known_apps()
                self._send_json({
                    "count": len([1 for v in known.values() if v.get("item_id")]),
                    "collecting": _remember_running,
                })
            elif path == "/api/downloads":
                self._send_json({"files": list_downloaded_ipas()})
            elif path == "/api/apple-id-status":
                self._send_json(ipatool_auth_status())
            elif path == "/api/search":
                term = query.get("q", "")
                limit = int(query.get("limit", "8"))
                self._send_json(ipatool_search(term, limit))
            elif path == "/api/download-progress":
                self._send_json(get_download_progress())
            elif path == "/api/install-progress":
                self._send_json(get_install_progress())
            else:
                self._send_json({"error": "not found"}, status=404)
        except Exception as e:
            self._send_json({"error": str(e), "trace": traceback.format_exc()}, status=500)

    def do_POST(self):
        try:
            path = self.path.split("?")[0]
            body = self._read_json_body()

            if path == "/api/setup":
                self._send_json(run_setup())
            elif path.startswith("/api/setup/"):
                self._send_json(start_setup_step(path.rsplit("/", 1)[-1]))
            elif path == "/api/logout":
                self._send_json(ipatool_logout())
            elif path == "/api/login":
                self._send_json(ipatool_login(body.get("email", ""), body.get("password", ""),
                                             body.get("auth_code"), bool(body.get("force"))))
            elif path == "/api/download":
                dest = body.get("dest_path")
                if not dest and body.get("to_desktop"):
                    # Выгрузка без вопросов «куда сохранить»: сразу на
                    # Рабочий стол, под названием приложения.
                    folder = desktop_dir()
                    problem = check_writable_dir(folder)
                    if problem:
                        self._send_json({"ok": False, "error": problem})
                        return
                    dest = str(auto_ipa_path(body.get("name", ""), body.get("bundle_id", "")))
                self._send_json(ipatool_download(body.get("bundle_id", ""), bool(body.get("purchase")), dest))
            elif path == "/api/apply-update":
                self._send_json(apply_update_now())
            elif path == "/api/report":
                self._send_json(start_report())
            elif path == "/api/pick-ipa-files":
                self._send_json(pick_ipa_files())
            elif path == "/api/pick-save-path":
                self._send_json(pick_save_path_dialog(body.get("default_name", "app.ipa")))
            elif path == "/api/reveal":
                self._send_json(reveal_in_finder(body.get("path", "")))
            elif path == "/api/install":
                self._send_json(install_ipa(body.get("ipa_path", ""), body.get("udid")))
            elif path == "/api/restore":
                item_id = body.get("item_id")
                try:
                    item_id = int(item_id) if item_id else None
                except (TypeError, ValueError):
                    item_id = None
                self._send_json(restore_app(body.get("bundle_id", ""), item_id,
                                            body.get("name"), body.get("udid")))
            elif path == "/api/download-control":
                action = body.get("action", "")
                if action == "cancel" and get_install_progress().get("running"):
                    # Past the download stage the same button has to stop the
                    # install instead, or "cancel" would quietly do nothing.
                    self._send_json(cancel_install())
                else:
                    self._send_json(control_download(action))
            elif path == "/api/uninstall":
                self._send_json(uninstall_app(body.get("bundle_id", ""), body.get("udid")))
            elif path == "/api/pick-file":
                self._send_json(pick_file_dialog())
            elif path == "/api/shutdown":
                self._send_json({"ok": True})
                threading.Thread(target=_delayed_exit, daemon=True).start()
            elif path == "/api/sign":
                self._send_json(sign_ipa(
                    body.get("ipa_path", ""), body.get("cert_path", ""),
                    body.get("cert_password", ""), body.get("profile_path", ""),
                    body.get("output_path"),
                ))
            else:
                self._send_json({"error": "not found"}, status=404)
        except Exception as e:
            self._send_json({"error": str(e), "trace": traceback.format_exc()}, status=500)


def _delayed_exit():
    time.sleep(0.3)
    os._exit(0)


def seed_known_apps() -> None:
    """Merges the bundled known_apps.json into this machine's record. Those
    ids are what let a fresh install already offer to bring apps back -
    including apps Apple has since pulled from the store, whose ids can no
    longer be looked up anywhere.

    Merging rather than copying-if-absent on purpose: the record gets created
    the moment a phone is plugged in, so a copy-only version loses the whole
    bundled list to a race with the first scan. Anything already known about
    an app (its seen_on history in particular) wins over the bundled entry."""
    source = RESOURCES_DIR / "known_apps.json"
    if not source.exists():
        return
    try:
        bundled = json.loads(source.read_text(encoding="utf-8"))
    except Exception:
        return
    if not isinstance(bundled, dict):
        return

    known = load_known_apps()
    added = 0
    for bundle_id, entry in bundled.items():
        if bundle_id not in known:
            known[bundle_id] = entry
            added += 1
        elif not known[bundle_id].get("item_id") and entry.get("item_id"):
            known[bundle_id]["item_id"] = entry["item_id"]
            known[bundle_id].setdefault("name", entry.get("name", ""))
            added += 1
    if added:
        save_known_apps(known)


def open_ui_window(url: str) -> None:
    """Shows the interface. On macOS the native window (SideKitUI) is started
    by the launcher and this is only a fallback; on Windows there is no such
    binary, so Edge is opened in app mode instead - same look as a real
    window, no address bar or tabs, and it is already on every Windows 10/11
    machine."""
    if IS_MAC:
        # На Маке окно рисует SideKitUI. Раньше здесь был откат на браузер:
        # если движок уже работал, интерфейс открывался вкладкой в браузере -
        # именно это и выглядело как «программа стала браузерной».
        ui = RESOURCES_DIR.parent / "MacOS" / "SideKitUI"
        if ui.exists():
            try:
                subprocess.Popen([str(ui), url])
                return
            except Exception:
                pass

    if IS_WINDOWS:
        candidates = [
            Path(os.environ.get("PROGRAMFILES(X86)", r"C:\Program Files (x86)"))
            / "Microsoft" / "Edge" / "Application" / "msedge.exe",
            Path(os.environ.get("PROGRAMFILES", r"C:\Program Files"))
            / "Microsoft" / "Edge" / "Application" / "msedge.exe",
            Path(os.environ.get("LOCALAPPDATA", "")) / "Microsoft" / "Edge"
            / "Application" / "msedge.exe",
            # Если Edge удалён - Chrome умеет то же самое отдельным окном.
            Path(os.environ.get("PROGRAMFILES", r"C:\Program Files"))
            / "Google" / "Chrome" / "Application" / "chrome.exe",
            Path(os.environ.get("PROGRAMFILES(X86)", r"C:\Program Files (x86)"))
            / "Google" / "Chrome" / "Application" / "chrome.exe",
            Path(os.environ.get("LOCALAPPDATA", "")) / "Google" / "Chrome"
            / "Application" / "chrome.exe",
        ]
        for browser in candidates:
            if browser.exists():
                try:
                    subprocess.Popen([
                        str(browser), f"--app={url}",
                        f"--user-data-dir={LOCK_DIR / 'window'}",  # own window, not a tab
                        "--window-size=1100,820",
                    ], **NO_CONSOLE)
                    return
                except Exception:
                    break
    webbrowser.open(url)



# ---------------------------------------------------------------------------
# Обновления по интернету
#
# Программа - это два файла: движок (server.py) и интерфейс (index.html).
# Они лежат в открытом хранилище, и при запуске SideKit смотрит, не появилось
# ли там версии свежее. Скачанное кладётся в папку пользователя (в /Applications
# без пароля администратора не записать) и подхватывается при следующем старте.
UPDATE_BASE = "https://raw.githubusercontent.com/dinarishakov186-source/sidekit/main/"
UPDATE_URL_FILE = LOCK_DIR / "update_url.txt"
UPDATE_DIR = LOCK_DIR / "update"
_update_note: dict = {}


def update_base_url() -> str:
    """Адрес хранилища. Лежит в файле, чтобы можно было поменять без пересборки."""
    try:
        if UPDATE_URL_FILE.exists():
            custom = UPDATE_URL_FILE.read_text(encoding="utf-8").strip()
            if custom.startswith("https://"):
                return custom if custom.endswith("/") else custom + "/"
    except Exception:
        pass
    return UPDATE_BASE


def _https_context():
    """Проверка сертификатов. На Windows у Python бывает пустой список
    доверенных центров - тогда любая загрузка падает с CERTIFICATE_VERIFY_FAILED,
    и обновления молча не приезжают. Набор сертификатов есть в certifi, он
    ставится вместе с библиотекой для iPhone."""
    import ssl
    # Сначала certifi: на Windows системный список бывает и непустым, но без
    # нужных центров - тогда загрузка всё равно падает. Набор certifi полный.
    try:
        import certifi
        return ssl.create_default_context(cafile=certifi.where())
    except Exception:
        pass
    try:
        return ssl.create_default_context()
    except Exception:
        return None


def _fetch(url: str, timeout: int = 20) -> bytes:
    import urllib.request
    request = urllib.request.Request(url, headers={"User-Agent": "SideKit"})
    context = _https_context()
    with urllib.request.urlopen(request, timeout=timeout, context=context) as response:
        return response.read()


def _version_of(path: Path) -> str:
    try:
        text = path.read_text(encoding="utf-8")
        return text.split('SERVER_VERSION = "', 1)[1].split('"', 1)[0]
    except Exception:
        return ""


def running_version() -> str:
    """Версия, которая реально будет работать: своя или уже скачанная."""
    found = _version_of(UPDATE_DIR / "server.py")
    return max(found, SERVER_VERSION) if found else SERVER_VERSION


def adopt_update_if_ready() -> None:
    """Если рядом лежит скачанная версия свежее нынешней - запускаемся из неё.
    Она уже прошла проверку запуском при скачивании."""
    if os.environ.get("SIDEKIT_UPDATED") == "1":
        return                      # уже работаем из обновления
    candidate = UPDATE_DIR / "server.py"
    if not candidate.exists() or _version_of(candidate) <= SERVER_VERSION:
        return
    os.environ["SIDEKIT_UPDATED"] = "1"
    os.environ["SIDEKIT_HOME"] = str(RESOURCES_DIR)
    try:
        os.execv(PYTHON_EXE, [PYTHON_EXE, str(candidate)] + sys.argv[1:])
    except Exception:
        pass                        # не вышло - работаем как есть


def check_for_updates() -> None:
    """Тихо смотрит, нет ли версии свежее, и складывает её рядом. Молчит при
    любой беде: без интернета программа обязана работать как обычно."""
    global _update_note
    try:
        base = update_base_url()
        info = json.loads(_fetch(base + "version.json").decode("utf-8"))
        latest = str(info.get("version", ""))
        if not latest or latest <= running_version():
            return
        staging = LOCK_DIR / "update.tmp"
        shutil.rmtree(staging, ignore_errors=True)
        staging.mkdir(parents=True, exist_ok=True)
        for name in ("server.py", "index.html"):
            data = _fetch(base + name)
            if len(data) < 1000:
                return              # подозрительно мало - не берём
            (staging / name).write_bytes(data)
        (staging / "version.json").write_text(json.dumps(info, ensure_ascii=False), encoding="utf-8")

        # Движок проверяем запуском: сломанное обновление хуже отсутствия.
        check = subprocess.run([PYTHON_EXE, str(staging / "server.py"), "--selftest"],
                               capture_output=True, text=True, timeout=90, **NO_CONSOLE)
        if check.returncode != 0:
            shutil.rmtree(staging, ignore_errors=True)
            return
        shutil.rmtree(UPDATE_DIR, ignore_errors=True)
        staging.replace(UPDATE_DIR)
        _update_note = {"available": True, "version": latest,
                        "notes": str(info.get("notes", ""))}
    except Exception:
        pass


_server = None
_server_port = 0


def restart_with_python(exe: str) -> None:
    """Перезапускает движок другим питоном на том же порту - окно остаётся
    открытым и просто перезагружает страницу."""
    def restart():
        time.sleep(0.8)
        try:
            if _server is not None:
                _server.server_close()
        except Exception:
            pass
        os.environ["SIDEKIT_PYSWITCH"] = "1"
        os.environ["SIDEKIT_HOME"] = str(RESOURCES_DIR)
        args = [exe, os.path.abspath(__file__), "--port", str(_server_port)]
        try:
            os.execv(exe, args)
        except Exception:
            subprocess.Popen(args, **NO_CONSOLE)
            os._exit(0)

    threading.Thread(target=restart, daemon=True).start()


def apply_update_now() -> dict:
    """Перезапускает движок на скачанной версии, не закрывая окно: новый
    занимает тот же порт, поэтому страница просто перезагружается."""
    candidate = UPDATE_DIR / "server.py"
    if not candidate.exists() or _version_of(candidate) <= SERVER_VERSION:
        return {"ok": False, "error": "Обновлять нечего — установлена свежая версия."}

    def restart():
        time.sleep(0.6)             # дать ответу дойти до окна
        try:
            if _server is not None:
                _server.server_close()
        except Exception:
            pass
        os.environ["SIDEKIT_UPDATED"] = "1"
        os.environ["SIDEKIT_HOME"] = str(RESOURCES_DIR)
        args = [PYTHON_EXE, str(candidate), "--port", str(_server_port)]
        try:
            os.execv(PYTHON_EXE, args)
        except Exception:
            subprocess.Popen(args, **NO_CONSOLE)
            os._exit(0)

    threading.Thread(target=restart, daemon=True).start()
    return {"ok": True, "version": _version_of(candidate), "port": _server_port}


# Папка для того, что программа доносит себе сама. Внутрь /Applications без
# пароля администратора не записать, поэтому - рядом с данными пользователя.
USER_BIN_DIR = LOCK_DIR / "bin"
LEGACY_NAME = "ipatool-legacy.exe" if IS_WINDOWS else "ipatool-legacy"


def legacy_ipatool() -> Path | None:
    """Запасной ipatool 2.2.0. Он ходит к Apple по постоянному адресу, и
    выручает, когда свежий получает от Apple 404 при вводе кода."""
    for folder in (USER_BIN_DIR, BIN_DIR):
        candidate = folder / LEGACY_NAME
        if candidate.exists():
            return candidate
    return None


def ensure_legacy_ipatool() -> Path | None:
    """Если запасного рядом нет - скачивает его сам. Так починка доезжает
    обычным обновлением, которое возит только два файла программы."""
    existing = legacy_ipatool()
    if existing:
        return existing
    system = "windows" if IS_WINDOWS else "macos"
    arch = "arm64" if platform.machine().lower() in ("arm64", "aarch64") else "amd64"
    url = ("https://github.com/majd/ipatool/releases/download/v2.2.0/"
           f"ipatool-2.2.0-{system}-{arch}.tar.gz")
    try:
        import io, tarfile
        data = _fetch(url, timeout=120)
        USER_BIN_DIR.mkdir(parents=True, exist_ok=True)
        target = USER_BIN_DIR / LEGACY_NAME
        with tarfile.open(fileobj=io.BytesIO(data), mode="r:gz") as archive:
            member = next((m for m in archive.getmembers()
                           if m.isfile() and "ipatool" in Path(m.name).name), None)
            if member is None:
                return None
            source = archive.extractfile(member)
            if source is None:
                return None
            target.write_bytes(source.read())
        if not IS_WINDOWS:
            os.chmod(target, 0o755)
        return target
    except Exception as e:
        remember_error("докачка запасного ipatool", str(e))
        return None


_recent_errors: list = []


def remember_error(where: str, text: str) -> None:
    """Запоминает последние неудачи для отчёта. Пароль сюда не попадает:
    записывается только то, что ответила Apple или система."""
    if not text:
        return
    _recent_errors.append(time.strftime("%H:%M:%S") + " · " + where + " · " + text.strip()[:1500])
    del _recent_errors[:-15]


def update_note() -> dict:
    """Есть ли рядом версия свежее той, что работает сейчас. Считается по
    файлам, а не по памяти: обновление могло скачаться в прошлый запуск."""
    candidate = UPDATE_DIR / "server.py"
    version = _version_of(candidate) if candidate.exists() else ""
    if not version or version <= SERVER_VERSION:
        return {}
    notes = ""
    try:
        notes = str(json.loads((UPDATE_DIR / "version.json").read_text(encoding="utf-8")).get("notes", ""))
    except Exception:
        pass
    return {"available": True, "version": version, "notes": notes}


def active_index_html() -> Path:
    """Интерфейс из обновления, если он скачан."""
    updated = UPDATE_DIR / "index.html"
    return updated if updated.exists() else INDEX_HTML


def _human_size(num: float) -> str:
    for unit in ("Б", "КБ", "МБ", "ГБ", "ТБ"):
        if num < 1024 or unit == "ТБ":
            return f"{num:.1f} {unit}"
        num /= 1024
    return str(num)


def _tool_version(path) -> str:
    try:
        out = subprocess.run([str(path), "--version"], capture_output=True,
                             text=True, timeout=20, **NO_CONSOLE)
        return (out.stdout or out.stderr or "").strip().splitlines()[0][:80]
    except Exception as e:
        return "не отвечает (" + str(e)[:60] + ")"


def _reachable(url: str) -> str:
    """Достаём ли мы нужные сайты. Без этого невозможно отличить «программа
    сломалась» от «интернет до этого адреса не доходит»."""
    try:
        started = time.time()
        _fetch(url, timeout=12)
        return "доступен (" + str(int((time.time() - started) * 1000)) + " мс)"
    except Exception as e:
        return "НЕДОСТУПЕН — " + str(e)[:120]


_report_job: dict = {"running": False, "done": False}


def start_report() -> dict:
    """Отчёт собирается в фоне. На Windows он занимает до полуминуты (опрос
    телефона, проверка связи), и окно успевало оборвать запрос - кнопка
    выглядела нерабочей."""
    if _report_job.get("running"):
        return {"ok": True, "started": True, "already": True}
    _report_job.update({"running": True, "done": False, "path": None, "error": None})

    def work():
        try:
            result = build_report()
        except Exception as e:
            result = {"ok": False, "error": str(e)}
        _report_job.update({"running": False, "done": True,
                            "path": result.get("path"), "error": result.get("error"),
                            "ok": result.get("ok")})

    threading.Thread(target=work, daemon=True).start()
    return {"ok": True, "started": True}


def report_state() -> dict:
    return dict(_report_job)


def build_report() -> dict:
    """Собирает подробную картину компьютера в один файл на Рабочем столе.
    Пароли и содержимое приложений сюда не попадают - только то, что нужно,
    чтобы понять причину неполадки, не переспрашивая по десять раз."""
    L = ["Отчёт SideKit", "Время: " + time.strftime("%Y-%m-%d %H:%M:%S"), ""]

    L.append("== ПРОГРАММА ==")
    L.append("Версия движка: " + SERVER_VERSION)
    L.append("Работает версия: " + running_version())
    note = update_note()
    L.append("Скачанное обновление: " + (note.get("version") if note else "нет"))
    L.append("Папка программы: " + str(RESOURCES_DIR))
    L.append("Папка данных: " + str(LOCK_DIR))
    L.append("Интерфейс: " + str(active_index_html()))
    L.append("Адрес обновлений: " + update_base_url())

    L += ["", "== КОМПЬЮТЕР =="]
    L.append("Система: " + platform.platform())
    L.append("Разрядность и процессор: " + platform.machine() + " · " + (platform.processor() or "—"))
    try:
        L.append("Ядер: " + str(os.cpu_count()))
    except Exception:
        pass
    try:
        usage = shutil.disk_usage(str(Path.home()))
        L.append("Диск: свободно " + _human_size(usage.free) + " из " + _human_size(usage.total))
    except Exception:
        pass
    try:
        if IS_MAC:
            memory = subprocess.run(["sysctl", "-n", "hw.memsize"], capture_output=True,
                                    text=True, timeout=10).stdout.strip()
            if memory.isdigit():
                L.append("Оперативная память: " + _human_size(int(memory)))
            model = subprocess.run(["sysctl", "-n", "hw.model"], capture_output=True,
                                   text=True, timeout=10).stdout.strip()
            if model:
                L.append("Модель Мака: " + model)
        elif IS_WINDOWS:
            class MemoryStatus(ctypes.Structure):
                _fields_ = [("dwLength", ctypes.c_ulong), ("dwMemoryLoad", ctypes.c_ulong),
                            ("ullTotalPhys", ctypes.c_ulonglong), ("ullAvailPhys", ctypes.c_ulonglong),
                            ("ullTotalPageFile", ctypes.c_ulonglong), ("ullAvailPageFile", ctypes.c_ulonglong),
                            ("ullTotalVirtual", ctypes.c_ulonglong), ("ullAvailVirtual", ctypes.c_ulonglong),
                            ("ullAvailExtendedVirtual", ctypes.c_ulonglong)]
            info = MemoryStatus()
            info.dwLength = ctypes.sizeof(MemoryStatus)
            if ctypes.windll.kernel32.GlobalMemoryStatusEx(ctypes.byref(info)):
                L.append("Оперативная память: " + _human_size(info.ullTotalPhys)
                         + " (свободно " + _human_size(info.ullAvailPhys) + ")")
    except Exception:
        pass
    L.append("Имя пользователя в системе: " + (os.environ.get("USER") or os.environ.get("USERNAME") or "—"))
    L.append("Язык и кодировка: " + str(locale.getdefaultlocale()) + " · " + sys.getfilesystemencoding())

    L += ["", "== PYTHON =="]
    L.append("Сейчас работает на: " + sys.version.split()[0] + " (" + sys.executable + ")")
    try:
        pip_version = subprocess.run([sys.executable, "-m", "pip", "--version"],
                                     capture_output=True, text=True, timeout=30, **NO_CONSOLE)
        L.append("pip: " + (pip_version.stdout or pip_version.stderr).strip()[:120])
    except Exception as e:
        L.append("pip: не отвечает (" + str(e)[:60] + ")")
    L.append("Все Python на компьютере:")
    for exe in python_candidates():
        version = ".".join(str(x) for x in interpreter_version(exe))
        L.append("  " + exe + " — " + version
                 + (" · библиотека есть" if interpreter_has_library(exe) else " · библиотеки нет"))

    L += ["", "== СОСТАВНЫЕ ЧАСТИ =="]
    main_tool = find_tool("ipatool")
    L.append("ipatool: " + (str(main_tool) + " · " + _tool_version(main_tool) if main_tool else "НЕ НАЙДЕН"))
    spare = legacy_ipatool()
    L.append("запасной ipatool: " + (str(spare) + " · " + _tool_version(spare) if spare else "нет (докачается при нужде)"))
    L.append("zsign: " + (str(find_tool("zsign")) if find_tool("zsign") else "нет (для App Store не нужен)"))
    try:
        import pymobiledevice3
        version = getattr(pymobiledevice3, "__version__", "версия неизвестна")
        L.append("библиотека pymobiledevice3: есть, " + str(version))
    except Exception as e:
        L.append("библиотека pymobiledevice3: НЕТ (" + str(e) + ")")

    L += ["", "== СВЯЗЬ =="]
    L.append("GitHub (обновления): " + _reachable(update_base_url() + "version.json"))
    L.append("Apple (вход и скачивание): " + _reachable("https://itunes.apple.com/lookup?id=284882215"))

    L += ["", "== ТЕЛЕФОН =="]
    try:
        L.append("Устройства: " + json.dumps(list_devices(), ensure_ascii=False)[:1500])
    except Exception as e:
        L.append("Устройства: не удалось получить (" + str(e) + ")")
    if IS_WINDOWS:
        try:
            service = subprocess.run(["sc", "query", "Apple Mobile Device Service"],
                                     capture_output=True, text=True, timeout=20, **NO_CONSOLE)
            state = "РАБОТАЕТ" if "RUNNING" in service.stdout.upper() else "не работает"
            L.append("Драйвер Apple (служба): " + (state if service.returncode == 0 else "НЕ УСТАНОВЛЕН"))
        except Exception as e:
            L.append("Драйвер Apple: не удалось проверить (" + str(e)[:60] + ")")
    try:
        L.append("Приложений в памяти программы: " + str(len(load_known_apps() or {})))
    except Exception:
        pass
    state = _read_login_state()
    L.append("Вход в Apple ID: " + ("выполнен, " + str(state.get("email")) if state.get("logged_in") else "не выполнен"))

    L += ["", "== ПОСЛЕДНИЕ НЕУДАЧИ =="]
    L += _recent_errors or ["(в этом запуске ошибок не записано)"]

    for log in (Path.home() / "Library" / "Logs" / "SideKit.log", LOCK_DIR / "server.log"):
        try:
            if log.exists():
                tail = log.read_text(encoding="utf-8", errors="replace").splitlines()[-200:]
                L += ["", "--- " + str(log) + " (последние строки) ---"] + tail
        except Exception:
            pass

    target = desktop_dir() / ("Отчёт SideKit " + time.strftime("%Y-%m-%d %H-%M") + ".txt")
    try:
        target.write_text("\n".join(L), encoding="utf-8")
    except Exception as e:
        return {"ok": False, "error": "Не получилось сохранить отчёт: " + str(e)}
    reveal_in_finder(str(target))
    return {"ok": True, "path": str(target)}

def main():
    # SideKit now ships its own native window (Contents/MacOS/SideKitUI),
    # and the launcher starts this server for it with SIDEKIT_NATIVE_UI=1.
    # In that mode nothing here should touch a browser: the launcher reads
    # the port out of the lock file and hands it to the native window
    # instead. The browser path stays for running server.py by hand.
    if "--selftest" in sys.argv:
        # Короткая самопроверка для обновлений: файл читается и запускается.
        print("SideKit " + SERVER_VERSION + " — самопроверка пройдена")
        return

    adopt_update_if_ready()
    switch_python_if_needed()
    native_ui = os.environ.get("SIDEKIT_NATIVE_UI") == "1"
    seed_known_apps()
    def watch_updates():
        # Проверяем и при запуске, и раз в полчаса: программу держат открытой
        # днями, и ждать перезапуска ради обновления незачем.
        while True:
            check_for_updates()
            time.sleep(1800)

    threading.Thread(target=watch_updates, daemon=True).start()

    existing_url = find_existing_instance_url()
    if existing_url and (UPDATE_DIR / "server.py").exists() \
            and _version_of(UPDATE_DIR / "server.py") > SERVER_VERSION:
        # Рядом лежит версия свежее той, что уже работает. Цепляться к
        # старому движку нельзя - иначе обновление не применится никогда.
        existing_url = None
    if existing_url:
        # SideKit is already running on the SAME version - just point at the
        # FIRST instance instead of starting a second, competing
        # server/process.
        if not native_ui:
            open_ui_window(existing_url)
        return

    # If an older-version server is still lingering in the background
    # (e.g. left over from before an update), tell it to exit so it can't
    # keep silently answering for a newer download.
    shut_down_stale_instance()

    wanted_port = 0
    if "--port" in sys.argv:
        try:
            wanted_port = int(sys.argv[sys.argv.index("--port") + 1])
        except Exception:
            wanted_port = 0
    ThreadingHTTPServer.allow_reuse_address = True
    try:
        server = ThreadingHTTPServer(("127.0.0.1", wanted_port), Handler)
    except OSError:
        # Порт мог не успеть освободиться - берём любой свободный.
        server = ThreadingHTTPServer(("127.0.0.1", 0), Handler)
    port = server.server_address[1]
    global _server, _server_port
    _server, _server_port = server, port
    write_lock(port)
    url = f"http://127.0.0.1:{port}/"

    def open_browser():
        time.sleep(0.4)
        open_ui_window(url)

    if not native_ui:
        threading.Thread(target=open_browser, daemon=True).start()
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        pass
    finally:
        remove_lock()


if __name__ == "__main__":
    try:
        main()
    except Exception:
        err = traceback.format_exc()
        try:
            subprocess.run([
                "osascript", "-e",
                f'display alert "SideKit не смог запуститься" message {json.dumps(err[-900:])} as critical',
            ], **NO_CONSOLE)
        except Exception:
            pass
        raise
