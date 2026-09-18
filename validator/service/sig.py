"""Hotkey signatures (sr25519) over the submission hash, shared by the service and the miner.

The keypair comes from `bittensor-wallet` rather than `substrate-interface`, which this
used before. Not a preference: `substrate-interface` pulls `scalecodec`, and the bittensor
SDK the chain workers need pulls `cyscale`, which claims the same namespace and refuses to
import while the other is installed. A validator has to run both, so one of them had to
go. `bittensor-wallet` is the Bittensor stack's own keypair, it is what the SDK already
depends on, and it is small enough that a miner installing it costs nothing.

The two are wire-compatible -- same ss58 addresses, same sr25519 signatures, each verifies
the other's -- so a signature made by either side still verifies here.
"""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
from typing import cast

from bittensor_wallet import Keypair

SS58_FORMAT = 42
# sr25519, as `bittensor_wallet.Keypair` numbers the curves. Named rather than passed as a
# bare 1 so a future default change cannot silently move us to another curve.
SR25519 = 1


def digest_of(parse_rs: bytes, parse_lean: bytes) -> str:
    # sha256(parse.rs ‖ Parse.lean), hex: what a submission is, and what the miner signs.
    h = hashlib.sha256()
    h.update(parse_rs)
    h.update(parse_lean)
    return h.hexdigest()


def submit_message(digest: str, hotkey: str, timestamp: int) -> bytes:
    """What a miner signs: the files, who is submitting them, and when.

    The digest binds the signature to these exact two files, so a captured signature
    cannot be reused to submit different ones. The hotkey binds it to the submitter. The
    unix `timestamp` is what makes a captured request perishable -- the service refuses a
    signature whose timestamp is outside a few minutes of its own clock, so an upload
    recorded off the wire cannot be replayed into a later round.
    """
    return f"submit:{digest}:{hotkey}:{timestamp}".encode()


def verify(hotkey: str, message: bytes, signature_hex: str) -> bool:
    # True iff `signature_hex` is a valid sr25519 signature of `message` by the ss58 `hotkey`.
    try:
        kp = Keypair(ss58_address=hotkey, ss58_format=SS58_FORMAT, crypto_type=SR25519)
        return bool(kp.verify(message, bytes.fromhex(signature_hex.removeprefix("0x"))))
    except Exception:  # noqa: BLE001 - any malformed key or signature is simply "not verified"
        return False


def load_keypair(hotkey_file: str) -> Keypair:
    # A Bittensor hotkey JSON file (its `secretSeed`), or a `//Name` dev URI for tests.
    if hotkey_file.startswith("//"):
        return Keypair.create_from_uri(hotkey_file, crypto_type=SR25519)
    raw = json.loads(Path(hotkey_file).read_text())  # pyright: ignore[reportAny] -- validated below
    if not isinstance(raw, dict):
        raise ValueError(f"{hotkey_file} is not a JSON object")
    # A JSON object's keys are always strings; that much the isinstance check above already proved.
    data = cast(dict[str, object], raw)
    seed = data.get("secretSeed") or data.get("privateKey")
    if not isinstance(seed, str) or not seed:
        raise ValueError(f"{hotkey_file} has no secretSeed")
    # bittensor_wallet's stub types `seed` as bytes, but the binding is a PyString and
    # rejects bytes at runtime -- a hex string is what it actually takes, which is what a
    # hotkey file stores.
    return Keypair.create_from_seed(seed, crypto_type=SR25519)  # pyright: ignore[reportArgumentType]


def sign(kp: Keypair, message: bytes) -> str:
    # Hex signature of `message` by `kp`.
    return kp.sign(message).hex()
