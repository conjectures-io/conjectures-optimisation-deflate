"""Canonical evidence hashes, independent of database initialization."""

import hashlib
import json


def canonical(value: object) -> bytes:
    return json.dumps(value, sort_keys=True, separators=(",", ":"), allow_nan=False).encode()


def sha256(value: object) -> str:
    return hashlib.sha256(canonical(value)).hexdigest()
