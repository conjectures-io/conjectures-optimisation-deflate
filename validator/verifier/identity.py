"""Identity used to reuse successful verification; reports are not attestations."""

from __future__ import annotations

import hashlib
import json
import os
import subprocess
from pathlib import Path
from typing import cast

ROOT = Path(__file__).resolve().parent.parent


def fingerprint() -> str:
    # Hash actual trusted inputs, not merely a user-supplied version string.
    from verifier.pins import PINNED

    files = {name: hashlib.sha256((ROOT / name).read_bytes()).hexdigest() for name in PINNED}
    tools = Path(os.environ.get("AENEAS_WORK", str(ROOT / ".work/aeneas")))
    for name in ("aeneas", "charon", "charon-driver"):
        path = tools / name
        if name.startswith("charon") and (tools / "charon/bin" / name).is_file():
            path = tools / "charon/bin" / name
        files[f"tool:{name}"] = hashlib.sha256(path.read_bytes()).hexdigest()
    files["toolchain_override"] = os.environ.get("CHARON_TOOLCHAIN", "nightly-2026-08-18")
    return hashlib.sha256(json.dumps(files, sort_keys=True).encode()).hexdigest()


def observed_snapshot() -> dict[str, object]:
    """Actual trusted inputs for a finished gate result, including dirty checkouts."""
    from verifier.pins import PINNED

    files: dict[str, str | None] = {}
    for name in PINNED:
        path = ROOT / name
        files[name] = hashlib.sha256(path.read_bytes()).hexdigest() if path.is_file() else None
    pins_file = ROOT / "verifier/PINS.json"
    expected_digest: str | None = None
    pin_drift: list[str] = []
    try:
        expected_bytes = pins_file.read_bytes()
        expected_digest = hashlib.sha256(expected_bytes).hexdigest()
        expected = cast(object, json.loads(expected_bytes))
        if not isinstance(expected, dict):
            pin_drift = ["verifier/PINS.json: invalid format"]
        else:
            expected_files = cast(dict[str, object], expected)
            pin_drift = sorted(
                name
                for name in files.keys() | expected_files.keys()
                if files.get(name) != expected_files.get(name)
            )
    except (OSError, ValueError):
        pin_drift = ["verifier/PINS.json: unavailable"]
    tools = Path(os.environ.get("AENEAS_WORK", str(ROOT / ".work/aeneas")))
    binaries: dict[str, str | None] = {}
    for name in ("aeneas", "charon", "charon-driver"):
        path = tools / name
        if name.startswith("charon") and (tools / "charon/bin" / name).is_file():
            path = tools / "charon/bin" / name
        binaries[name] = hashlib.sha256(path.read_bytes()).hexdigest() if path.is_file() else None
    repo = ROOT.parent
    try:
        commit = subprocess.run(
            ["git", "rev-parse", "HEAD"], cwd=repo, capture_output=True, text=True, check=False
        )
        dirty = subprocess.run(
            ["git", "status", "--porcelain", "--untracked-files=no"],
            cwd=repo,
            capture_output=True,
            text=True,
            check=False,
        )
        revision = commit.stdout.strip() if commit.returncode == 0 else None
        modified = bool(dirty.stdout.strip()) if dirty.returncode == 0 else None
    except OSError:
        revision = None
        modified = None
    return {
        "files": files,
        "expected_pins_sha256": expected_digest,
        "pin_drift": pin_drift,
        "tools": binaries,
        "toolchain_override": os.environ.get("CHARON_TOOLCHAIN", "nightly-2026-08-18"),
        "git_commit": revision,
        "git_dirty": modified,
    }


def required_fingerprint() -> str:
    """A separate scorer can use the operator-published verifier identity."""
    value = os.environ.get("VERIFY_REQUIRED_FINGERPRINT")
    if value is None:
        return fingerprint()
    if len(value) != 64 or any(c not in "0123456789abcdef" for c in value):
        raise ValueError("VERIFY_REQUIRED_FINGERPRINT must be a sha256 hex digest")
    return value


if __name__ == "__main__":
    print(fingerprint())
