"""Identity used to reuse successful verification; reports are not attestations."""

from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path

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
