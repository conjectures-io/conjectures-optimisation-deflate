"""Private verification inputs and build outputs; shared dependencies are read-only."""

from __future__ import annotations

import fcntl
import hashlib
import json
import os
import shutil
import tempfile
from pathlib import Path
from typing import TextIO


class Workspace:
    def __init__(self, root: Path, parent: Path | None = None):
        parent = parent or root.parent / "data/verification-workspace"
        parent.mkdir(parents=True, exist_ok=True)
        self.path: Path = Path(tempfile.mkdtemp(prefix="verify-", dir=parent)).resolve()
        self.hashes: dict[str, str] = {}
        self.events: list[dict[str, str]] = []
        self.lock: TextIO = (self.path / ".active").open("w")
        fcntl.flock(self.lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        self.lock.write(str(os.getpid()))
        self.lock.flush()
        (self.path / "report.json").write_text('{"status": "running"}\n')
        (self.path / "logs").mkdir()
        (self.path / "slot/generated").mkdir(parents=True)
        lean = self.path / "lean"
        lean.mkdir()
        for name in ("Lz77", "Verify"):
            shutil.copytree(root / "lean" / name, lean / name)
        for name in (
            "Lz77.lean",
            "Slot.lean",
            "Verify.lean",
            "Proof.lean",
            "lakefile.toml",
            "lake-manifest.json",
            "lean-toolchain",
        ):
            shutil.copyfile(root / "lean" / name, lean / name)
        (lean / "Proof").mkdir()
        shutil.copyfile(root / "lean/Proof/Axioms.lean", lean / "Proof/Axioms.lean")
        (lean / ".lake").mkdir()
        packages = root / "lean/.lake/packages"
        if packages.exists():
            (lean / ".lake/packages").symlink_to(packages.resolve(), target_is_directory=True)
        shutil.copyfile(root / "rust-toolchain.toml", self.path / "rust-toolchain.toml")

    def snapshot(self, name: str, data: bytes, destination: str) -> None:
        self.hashes[name] = hashlib.sha256(data).hexdigest()
        path = self.path / destination
        path.write_bytes(data)
        path.chmod(0o444)

    def record(self, stage: str, status: str, detail: str = "") -> None:
        self.events.append({"stage": stage, "status": status, "detail": detail})

    def finish(self, code: int, keep: str) -> None:
        (self.path / "report.json").write_text(
            json.dumps(
                {
                    "exit_code": code,
                    "hashes": self.hashes,
                    "stages": self.events,
                },
                indent=2,
            )
            + "\n"
        )
        (self.path / ".active").unlink(missing_ok=True)
        self.lock.close()
        if keep == "never" or (keep == "auto" and code == 0):
            shutil.rmtree(self.path)
