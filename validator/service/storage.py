"""Where a submission's two files land, written so a crash cannot leave half of one."""

from __future__ import annotations

import os
import tempfile
from pathlib import Path

NAMES = ("parse.rs", "Parse.lean")


def write_submission(directory: Path, parse_rs: bytes, parse_lean: bytes) -> None:
    """Write both files into `directory`, each atomically.

    The gate reads this directory in another process, possibly moments later, so a
    partially written parse.rs would be handed to it as though it were complete. Each
    file is written to a temporary name in the same directory and renamed into place --
    a rename within one filesystem is atomic, so a reader sees either the old file or the
    whole new one, never a prefix.
    """
    directory.mkdir(parents=True, exist_ok=True)
    for name, payload in zip(NAMES, (parse_rs, parse_lean), strict=True):
        _atomic_write(directory / name, payload)
    _fsync_dir(directory)


def _atomic_write(path: Path, payload: bytes) -> None:
    fd, tmp = tempfile.mkstemp(dir=path.parent, prefix=f".{path.name}.", suffix=".tmp")
    try:
        with os.fdopen(fd, "wb") as handle:
            handle.write(payload)
            handle.flush()
            # Rename is atomic, but only durable once the data itself is on disk: without
            # this, a power loss can leave the new name pointing at empty blocks.
            os.fsync(handle.fileno())
        os.replace(tmp, path)
    except BaseException:
        Path(tmp).unlink(missing_ok=True)
        raise


def _fsync_dir(directory: Path) -> None:
    # Persist the directory entries themselves, so the renames survive a crash too.
    fd = os.open(directory, os.O_RDONLY)
    try:
        os.fsync(fd)
    finally:
        os.close(fd)
