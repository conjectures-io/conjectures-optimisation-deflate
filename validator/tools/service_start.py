"""Start a service in the foreground, or start/stop it under PM2."""

from __future__ import annotations

import argparse
import fcntl
import json
import os
import shutil
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SERVICES = {
    "service": ("submission-api", "service.api"),
    "service-worker": ("gate-worker", "service.worker"),
    "chain-watcher": ("chain-watcher", "workers.chain_watcher"),
    "weight-setter": ("weight-setter", "workers.weight_setter"),
}


def process_list(output: str) -> list[dict]:
    """Read jlist's final JSON document, allowing daemon startup banners before it."""
    # Only accept a complete array extending to the end of stdout. Do not extract
    # an arbitrary nested array from a malformed/truncated process record.
    lines = output.splitlines(keepends=True)
    for index, line in enumerate(lines):
        if not line.lstrip().startswith("["):
            continue
        try:
            value = json.loads("".join(lines[index:]))
        except ValueError:
            continue
        if not isinstance(value, list) or any(
            not isinstance(item, dict)
            or not isinstance(item.get("name"), str)
            or not isinstance(item.get("pm2_env"), dict)
            for item in value
        ):
            raise ValueError("invalid PM2 process records")
        return value
    raise ValueError("missing complete PM2 process list")


def start_background(service: str, *, stop: bool = False) -> int:
    pm2 = shutil.which("pm2")
    if pm2 is None:
        print(
            "PM2 is not installed or not on PATH. Install Node.js/npm, then run "
            "`npm install -g pm2`. Instructions: https://pm2.keymetrics.io/docs/usage/quick-start/",
            file=sys.stderr,
        )
        return 2
    name, module = SERVICES[service]
    managed_name = f"miniz-oxide-{name}"
    # Serialize duplicate checks and starts for concurrent invocations in this checkout.
    lock_dir = ROOT / "validator/.work"
    lock_dir.mkdir(parents=True, exist_ok=True)
    with (lock_dir / "pm2-start.lock").open("a") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        result = subprocess.run(
            [pm2, "jlist", "--silent"], capture_output=True, text=True, check=False
        )
        if result.returncode:
            print("Cannot inspect PM2 processes; no service changed.", file=sys.stderr)
            return result.returncode
        try:
            processes = process_list(result.stdout)
            matches = [
                p
                for p in processes
                if p.get("name") == managed_name
                or (
                    p.get("pm2_env", {}).get("pm_cwd") == str(ROOT / "validator")
                    and (
                        p.get("name") == name
                        or p.get("pm2_env", {}).get("args") in (["-m", module], f"-m {module}")
                    )
                )
            ]
        except (ValueError, AttributeError, TypeError):
            print("Cannot parse PM2 process list; no service changed.", file=sys.stderr)
            return 2
        if stop:
            if not matches:
                print(f"{managed_name} is not registered in PM2; nothing to stop.")
                return 0
            ids = [p.get("pm_id") for p in matches]
            if any(type(pid) is not int or pid < 0 for pid in ids):
                print("Invalid PM2 process ID; no service stopped.", file=sys.stderr)
                return 2
            return subprocess.run([pm2, "stop", *(str(pid) for pid in ids)], check=False).returncode
        if matches:
            inactive = [
                p for p in matches if p.get("pm2_env", {}).get("status") in {"stopped", "errored"}
            ]
            if len(matches) == 1 and inactive:
                pid = inactive[0].get("pm_id")
                if type(pid) is not int or pid < 0:
                    print("Invalid PM2 process ID; no service restarted.", file=sys.stderr)
                    return 2
                print(f"Resuming {inactive[0]['name']} (PM2 id={pid}).", flush=True)
                return subprocess.run([pm2, "restart", str(pid)], check=False).returncode
            for process in matches:
                status = process.get("pm2_env", {}).get("status", "unknown")
                print(
                    f"Warning: {process.get('name')} is already registered in PM2 "
                    f"(id={process.get('pm_id')}, status={status}); no duplicate started. "
                    "Use pm2 restart <id> to restart it.",
                    file=sys.stderr,
                )
            return 0
        return subprocess.run(
            [pm2, "start", str(ROOT / "pm2/service.config.js"), "--only", managed_name],
            check=False,
        ).returncode


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("service", choices=SERVICES)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--background", action="store_true")
    mode.add_argument("--stop", action="store_true", help="stop this service under PM2")
    args = parser.parse_args()
    if args.background or args.stop:
        return start_background(args.service, stop=args.stop)
    os.chdir(ROOT / "validator")
    os.execv(sys.executable, [sys.executable, "-m", SERVICES[args.service][1]])
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
