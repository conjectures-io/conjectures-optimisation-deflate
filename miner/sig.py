"""The hotkey signature that authorises one competition submission, as the platform checks it.

Submissions go to conjectures-validator, which serves every competition from one API. This
is the miner's half of that wire contract; the platform's half is
`submission_api/competition_sig.py` in that repository. The contract is the *message*, not
this file, so each side keeps its own copy -- and `test_miner_sig.py` pins this copy to the
exact bytes the platform rebuilds, so the two cannot drift without a test failing here.

Not `validator/service/sig.py`. That signs the old service's `submit:<digest>:...` message,
which names no competition; the platform's message does, so a signature made for one
competition cannot be replayed against another. The service keeps its own signer for as long
as it runs.

The keypair comes from `bittensor-wallet`, for the reason `service/sig.py` gives: it is the
Bittensor stack's own keypair, small, and wire-compatible with the platform's -- same ss58
addresses, same sr25519 signatures, each verifies the other's.
"""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
from typing import Final, cast

from bittensor_wallet import Keypair as Keypair  # re-exported: submit.py types its keypair with it

COMPETITION_SUBMIT_PREFIX: Final = "conjectures-competition-submit-v1"
# sr25519, as `bittensor_wallet.Keypair` numbers the curves. Named rather than passed as a
# bare 1 so a future default change cannot silently move us to another curve.
SR25519: Final = 1


def digest_of(parse_rs: bytes, parse_lean: bytes) -> str:
    """sha256(parse.rs ‖ Parse.lean), hex: what a submission is, and part of what is signed."""
    h = hashlib.sha256()
    h.update(parse_rs)
    h.update(parse_lean)
    return h.hexdigest()


def submit_message(*, competition: str, digest: str, hotkey: str, timestamp: int) -> str:
    """The exact text a hotkey signs to authorise one submission to one competition.

    Byte-for-byte what the platform rebuilds from the request it received: the slug it
    resolved from the path, the digest of the bytes it read, the hotkey header and the
    timestamp header. Change a character and every submit is refused as a bad signature.
    """
    return "\n".join(
        (
            COMPETITION_SUBMIT_PREFIX,
            f"competition: {competition}",
            f"digest: {digest}",
            f"hotkey: {hotkey}",
            f"timestamp: {timestamp}",
        )
    )


def sign(kp: Keypair, message: str) -> str:
    """Hex signature over the UTF-8 bytes of `message`, which is what the platform verifies."""
    return kp.sign(message.encode("utf-8")).hex()


def load_keypair(hotkey_file: str) -> Keypair:
    """A Bittensor hotkey JSON file (its `secretSeed`), or a `//Name` dev URI for tests."""
    if hotkey_file.startswith("//"):
        return Keypair.create_from_uri(hotkey_file, crypto_type=SR25519)
    raw = json.loads(Path(hotkey_file).read_text())  # pyright: ignore[reportAny] -- validated below
    if not isinstance(raw, dict):
        raise ValueError(f"{hotkey_file} is not a JSON object")
    data = cast(dict[str, object], raw)
    seed = data.get("secretSeed") or data.get("privateKey")
    if not isinstance(seed, str) or not seed:
        raise ValueError(f"{hotkey_file} has no secretSeed")
    # bittensor_wallet's stub types `seed` as bytes, but the binding rejects bytes at
    # runtime -- a hex string is what it takes, which is what a hotkey file stores.
    return Keypair.create_from_seed(seed, crypto_type=SR25519)  # pyright: ignore[reportArgumentType]
