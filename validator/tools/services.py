"""Manage this competition's application processes and local PostgreSQL."""

from __future__ import annotations

import argparse
import dataclasses
import shutil
import subprocess
import sys
from typing import cast

from tools.service_start import ROOT, SERVICES, Pm2Process, process_list, start_background

# baseline-seed is a one-shot: it seeds miner/examples as the reference frontier and exits.
WORKERS = ("baseline-seed", "service-worker", "chain-watcher", "weight-setter")


def command(*args: str) -> int:
    return subprocess.run(list(args), cwd=ROOT, check=False).returncode


def inspect() -> list[Pm2Process]:
    if shutil.which("pm2") is None:
        raise ValueError("PM2 missing: install Node.js/npm, then npm install -g pm2")
    result = subprocess.run(
        ["pm2", "jlist", "--silent"], capture_output=True, text=True, check=False
    )
    if result.returncode:
        raise ValueError("Cannot inspect PM2 processes")
    return process_list(result.stdout)


def selected(processes: list[Pm2Process], service: str) -> list[Pm2Process]:
    name, module = SERVICES[service]
    return [
        p
        for p in processes
        if p.get("name") == f"miniz-oxide-{name}"
        or (
            p.get("pm2_env", {}).get("pm_cwd") == str(ROOT / "validator")
            and (
                p.get("name") == name
                or p.get("pm2_env", {}).get("args") in (["-m", module], f"-m {module}")
            )
        )
    ]


@dataclasses.dataclass
class Args:
    action: str = ""
    with_api: bool = False
    external_db: bool = False
    keep_db: bool = False
    service: str | None = None
    lines: int = 100
    no_follow: bool = False


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="action", required=True)
    up = sub.add_parser("up")
    up.add_argument("--with-api", action="store_true")
    up.add_argument(
        "--external-db", action="store_true", help="migrate configured DB; skip local Docker"
    )
    down = sub.add_parser("down")
    down.add_argument("--keep-db", action="store_true")
    sub.add_parser("status")
    logs = sub.add_parser("logs")
    logs.add_argument("service", nargs="?", choices=[*SERVICES, "db"])
    logs.add_argument("--lines", type=int, default=100)
    logs.add_argument("--no-follow", action="store_true")
    args = parser.parse_args(argv, namespace=Args())
    try:
        processes = inspect()  # Fail before mutating anything if PM2 is unavailable.
        if args.action == "up":
            if not args.external_db and (code := command("just", "db-up")):
                return code
            if code := command("just", "db-migrate"):
                return code
            for service in (*WORKERS, *(("service",) if args.with_api else ())):
                if code := start_background(service):
                    print(
                        f"Startup failed at {service}; earlier services remain running.",
                        file=sys.stderr,
                    )
                    return code
            return 0
        if args.action == "down":
            # Stop intake first; never tear down DB after a failed application stop.
            failed = 0
            for service in SERVICES:
                failed = start_background(service, stop=True) or failed
            if failed or args.keep_db:
                return failed
            return command("docker", "compose", "stop", "db")
        if args.action == "status":
            for service in SERVICES:
                matches = selected(processes, service)
                if not matches:
                    print(f"{service}: not registered")
                for process in matches:
                    env = process["pm2_env"]
                    print(
                        f"{service}: {env.get('status', 'unknown')} "
                        f"(PM2 id={process.get('pm_id')}, pid={process.get('pid', 0)})"
                    )
            print(
                "Local PostgreSQL (process status is not an application health check):", flush=True
            )
            return command("docker", "compose", "ps", "db")
        if args.lines < 0:
            parser.error("--lines must be nonnegative")
        if args.service == "db":
            return command(
                "docker",
                "compose",
                "logs",
                "--tail",
                str(args.lines),
                *(("--follow",) if not args.no_follow else ()),
                "db",
            )
        paths: list[str] = []
        for service in [args.service] if args.service else SERVICES:
            for process in selected(processes, service):
                for key in ("pm_out_log_path", "pm_err_log_path"):
                    path = cast("str | None", process["pm2_env"].get(key))
                    if path and path not in paths:
                        paths.append(path)
        if not paths:
            print("No managed service logs found.")
            return 0
        return command(
            "tail", "-n", str(args.lines), *(("-F",) if not args.no_follow else ()), "--", *paths
        )
    except (ValueError, OSError) as exc:
        print(str(exc), file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
