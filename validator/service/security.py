"""What the service checks about a signed write before it trusts anything in it.

Order matters here: shape first, then freshness, then the signature. A malformed ss58
address reaching `Keypair()` is caught by a bare `except Exception` inside sig.verify and
comes back as "not verified", which tells a miner nothing about what they got wrong --
and makes every malformed request pay for a curve operation.
"""

from __future__ import annotations

import re
import time

# ss58 addresses are base58 (no 0, O, I, l) and 47-48 characters on the 42-prefix format
# this subnet uses. Checked for shape only; whether the key is real is settled by the
# signature, not by a regex.
SS58 = re.compile(r"^[1-9A-HJ-NP-Za-km-z]{46,49}$")
# sr25519 signatures are 64 bytes; accept them with or without the 0x prefix.
SIGNATURE = re.compile(r"^(0x)?[0-9a-fA-F]{128}$")
# sha256, hex.
DIGEST = re.compile(r"^[0-9a-f]{64}$")


class Invalid(ValueError):
    """A write that is malformed, stale or unsigned. Carries the miner-facing reason."""


def check_hotkey(hotkey: str) -> str:
    if not SS58.match(hotkey or ""):
        raise Invalid("hotkey is not an ss58 address")
    return hotkey


def check_signature(signature: str) -> str:
    if not SIGNATURE.match(signature or ""):
        raise Invalid("signature is not 64 hex-encoded bytes")
    return signature


def check_digest(digest: str) -> str:
    if not DIGEST.match(digest or ""):
        raise Invalid("digest is not a hex sha256")
    return digest


def check_fresh(timestamp: int, window_seconds: int, *, now: float | None = None) -> int:
    """Refuse a signature whose timestamp is too far from ours, in either direction.

    Both directions on purpose: a timestamp far in the past is a replay, and one far in
    the future would let a miner mint a signature today that stays valid for a round that
    has not opened yet.
    """
    current = time.time() if now is None else now
    drift = abs(current - timestamp)
    if drift > window_seconds:
        raise Invalid(
            f"signed timestamp is {drift:.0f}s from the validator's clock "
            f"(at most {window_seconds}s); check the clock and resubmit"
        )
    return timestamp
