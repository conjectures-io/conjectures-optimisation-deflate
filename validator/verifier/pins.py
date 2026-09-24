#!/usr/bin/env python3
"""Pin integrity: everything a submission is judged against, hashed in PINS.json.

Run at CI and setup time, never per submission -- verify.py's gate trusts the
checkout it's given and no longer checks this itself.

    verifier/pins.py --check   fail if PINS.json is stale (CI, setup)
    verifier/pins.py --write   re-pin after an operator-side change

Exit 0 unchanged, 1 drifted, 2 PINS.json itself is broken.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from pathlib import Path
from typing import NoReturn, cast

ROOT = Path(__file__).resolve().parent.parent

# Everything that participates in the verdict, pinned by hash in PINS.json.
PINNED = [
    "lean/Lz77/Spec.lean",
    "lean/Lz77/Lemmas.lean",
    "lean/Lz77/Interface.lean",
    "lean/Lz77/Search.lean",
    "lean/Lz77.lean",
    "lean/Verify/Obligation.lean",
    "lean/Verify.lean",
    "lean/Proof/Axioms.lean",
    "lean/Proof.lean",
    "lean/Slot.lean",
    "lean/lakefile.toml",
    "lean/lean-toolchain",
    "lean/lake-manifest.json",
    "measure/src/main.rs",
    "measure/src/deflate.rs",
    "measure/src/token.rs",
    "measure/src/loader.rs",
    "measure/src/method.rs",
    "measure/src/record.rs",
    "measure/Cargo.toml",
    "measure/Cargo.lock",
    # Copied verbatim into every generated crate, so these decide how each
    # candidate is compiled -- the manifest carries the optimisation profile and
    # the shim is the only thing between `parse` and the C ABI.
    "measure/candidate/Cargo.toml",
    "measure/candidate/lib.rs",
    "incumbent/parse.rs",
    "slot/Cargo.toml",
    "slot/src/lib.rs",
    "slot/Cargo.lock",
    "rust-toolchain.toml",
    "verifier/verify.py",
    "verifier/workspace.py",
    "verifier/resolved.py",
    "verifier/identity.py",
    "db/verification.py",
    "db/aggregation.py",
    "db/admission.py",
    "db/admission_statistics.py",
    "scoring/admission.py",
    "scoring/eligibility.py",
    "scoring/config.py",
    "bench/storage.py",
    "bench/artifacts.py",
    "db/scoring.py",
    "db/models.py",
    "db/submissions.py",
    "service/worker.py",
    "precheck/Cargo.toml",
    "precheck/Cargo.lock",
    "precheck/src/main.rs",
    "verifier/extract.sh",
    "verifier/config.sh",
    "verifier/make-corpus.py",
    "sandbox/__init__.py",
    "sandbox/bwrap.py",
    "bench/__init__.py",
    "bench/driver.py",
    "bench/corpora.py",
    "bench/errors.py",
    "bench/results.py",
    "bench/verdict.py",
    "bench/report.py",
]

# Deliberately not pinned: `corpora.toml` and the corpus itself, which every
# validator is expected to point at its own held-out data; `bench/__main__.py`
# and `bench/analyze.py`/`compare.py`/`plot.py`, which report on a measurement
# and never take part in one.

PINS_FILE = ROOT / "verifier/PINS.json"


def sha(p: Path) -> str:
    # Hex sha256 of a file, the unit of pinning.
    return hashlib.sha256(p.read_bytes()).hexdigest()


def stop(msg: str) -> NoReturn:
    # PINS.json itself is broken: never blame the checkout, exit 2.
    print(f"PINS ERROR\n  {msg}", file=sys.stderr)
    sys.exit(2)


def load_pins(pins_file: Path) -> dict[str, str]:
    # PINS.json is the tamper check itself: a wrong shape must fail loudly, not cast silently.
    try:
        data = json.loads(pins_file.read_text())  # pyright: ignore[reportAny] -- validated below
    except json.JSONDecodeError as e:
        stop(f"{pins_file.relative_to(ROOT)} is not valid JSON: {e}")
    if not isinstance(data, dict) or not all(
        isinstance(k, str) and isinstance(v, str)
        for k, v in data.items()  # pyright: ignore[reportUnknownVariableType]
    ):
        stop(f"{pins_file.relative_to(ROOT)} must be a JSON object of string to string")
    return cast(dict[str, str], data)


def pins_changed() -> list[str]:
    # Pinned files whose hash no longer matches PINS.json.
    if not PINS_FILE.exists():
        stop("verifier/PINS.json is missing; run `verifier/pins.py --write`")
    pinned = load_pins(PINS_FILE)
    current = {p: sha(ROOT / p) for p in pinned if (ROOT / p).exists()}
    return sorted(p for p in pinned if current.get(p) != pinned[p])


def write() -> None:
    # Record the current hashes; an operator's deliberate acknowledgment of a change.
    current = {p: sha(ROOT / p) for p in PINNED if (ROOT / p).exists()}
    PINS_FILE.write_text(json.dumps(current, indent=2, sort_keys=True) + "\n")
    print(f"wrote {PINS_FILE.relative_to(ROOT)} ({len(current)} files)")


def check() -> None:
    # CI and setup call this; a miner's submission never does.
    changed = pins_changed()
    if changed:
        print(
            "PINS DRIFTED\n  the contract, the engine or the gate has been modified:\n  "
            + "\n  ".join(changed)
        )
        sys.exit(1)
    print(f"pins ok — {len(load_pins(PINS_FILE))} contract, engine and gate files unchanged")


def main() -> None:
    ap = argparse.ArgumentParser(description=(__doc__ or "").split("\n")[0])
    ap.add_argument("--check", action="store_true", help="fail if PINS.json is stale")
    ap.add_argument("--write", action="store_true", help="re-pin after an operator-side change")
    args = ap.parse_args()
    do_check = cast(bool, args.check)
    do_write = cast(bool, args.write)
    if do_check == do_write:
        ap.error("exactly one of --check or --write is required")
    write() if do_write else check()


if __name__ == "__main__":
    main()
