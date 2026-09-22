"""Remove finished private verification workspaces; active and unknown paths are kept."""

from __future__ import annotations

import argparse
import fcntl
import os
import shutil
import tempfile
import time
from pathlib import Path
from typing import cast

REPO = Path(__file__).resolve().parents[2]
ROOT = REPO / "data/verification-workspace"
LEGACY = (
    "validator/lean/Slot/Types.lean",
    "validator/lean/Slot/Funs.lean",
    "validator/lean/Proof/Parse.lean",
    "validator/lean/slot.llbc",
    "validator/.work/axioms.lean",
)


def archive_legacy(repo: Path, *, apply: bool = False) -> list[Path]:
    """Archive exact retired outputs, preserving unpublished proof work.

    Run after stopping old-version workers. New verifiers never touch these paths.
    No recursive .work/build deletion and no traversal through symlink parents.
    """
    paths = [repo / relative for relative in LEGACY]
    paths = [
        path
        for path in paths
        if path.is_file() and not any(parent.is_symlink() for parent in (path, *path.parents))
    ]
    if apply and paths:
        root = repo / "data/verification-workspace"
        if any(parent.is_symlink() for parent in (root, *root.parents)):
            raise ValueError("archive root must not traverse symlinks")
        root.mkdir(parents=True, exist_ok=True)
        archive = Path(tempfile.mkdtemp(prefix="legacy-", dir=root))
        for path in paths:
            target = archive / path.relative_to(repo)
            target.parent.mkdir(parents=True, exist_ok=True)
            path.rename(target)
        print(f"Legacy files preserved in {archive}")
    return paths


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
    parser.add_argument(
        "--legacy", action="store_true", help="archive exact legacy outputs; stop old workers first"
    )
    args = parser.parse_args()
    if cast(bool, args.legacy):
        for path in archive_legacy(REPO, apply=cast(bool, args.apply)):
            print(path)
        return
    for path in cleanup(ROOT, cast(float, args.days) * 86400, apply=cast(bool, args.apply)):
        print(path)


if __name__ == "__main__":
    main()
