"""Remove finished private verification workspaces; active and unknown paths are kept."""

from __future__ import annotations

import argparse
import fcntl
import os
import shutil
import time
from pathlib import Path
from typing import cast

ROOT = Path(__file__).resolve().parents[2] / "data/verification-workspace"


def cleanup(root: Path, age_seconds: float, *, apply: bool = False) -> list[Path]:
    if age_seconds < 0:
        raise ValueError("age must be nonnegative")
    removed: list[Path] = []
    if root.is_symlink():
        raise ValueError("workspace root must not be a symlink")
    if not root.exists():
        return removed
    for path in sorted(root.iterdir()):
        if path.is_symlink() or not path.is_dir() or not path.name.startswith("verify-"):
            continue
        report = path / "report.json"
        if report.is_symlink() or not report.is_file():
            continue
        if time.time() - report.stat().st_mtime < age_seconds:
            continue
        active = path / ".active"
        descriptor: int | None = None
        try:
            if active.exists():
                descriptor = os.open(active, os.O_RDONLY | os.O_NOFOLLOW)
                try:
                    fcntl.flock(descriptor, fcntl.LOCK_EX | fcntl.LOCK_NB)
                except BlockingIOError:
                    continue  # A live verifier owns the lock, even if its PID is reused.
            removed.append(path)
            if apply:
                shutil.rmtree(path)  # fd-based rmtree does not traverse symlink children.
        except FileNotFoundError:
            continue  # A concurrent owner/cleaner already removed this workspace.
        finally:
            if descriptor is not None:
                os.close(descriptor)
    return removed


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--days", type=float, default=7)
    parser.add_argument("--apply", action="store_true")
    args = parser.parse_args()
    for path in cleanup(ROOT, cast(float, args.days) * 86400, apply=cast(bool, args.apply)):
        print(path)


if __name__ == "__main__":
    main()
