"""Seed the operator baselines as the validator starts: the reference Pareto frontier.

Runs as the one-shot PM2 process `lz77-baseline-seed`, which `pm2 start
pm2/service.config.js` and `just up` start beside the long-running processes. Seeding is
incremental (bench.baselines): on a fresh validator it verifies and benchmarks every
complete example in miner/examples plus miner/template on both corpora, about an hour;
after that a start reuses what is stored and finishes in seconds, redoing only what a
changed verifier or corpus invalidated. It exits when done and PM2 does not restart it.

`BASELINE_SEED_ON_START=0` turns it off, for a host that must never seed. A gate-only
machine started with `--only lz77-gate-worker` never runs it, so one host seeds.
"""

from __future__ import annotations

import os
import shutil
import subprocess
import sys
from collections.abc import Mapping, Sequence
from pathlib import Path

VALIDATOR = Path(__file__).resolve().parents[1]
OFF = frozenset({"0", "false", "no", "off"})


def enabled(env: Mapping[str, str] = os.environ) -> bool:
    return env.get("BASELINE_SEED_ON_START", "1").strip().lower() not in OFF


def cargo() -> str:
    # PM2 inherits whatever PATH it was started from, which on a root box often lacks
    # rustup's bin; setup installs cargo there, so fall back to it rather than refuse.
    home = Path(os.environ.get("CARGO_HOME", Path.home() / ".cargo"))
    found = shutil.which("cargo") or shutil.which("cargo", path=str(home / "bin"))
    if found is None:
        raise SystemExit(
            "[baselines] cargo not found on PATH or in $CARGO_HOME/bin; run ./setup.sh"
        )
    os.environ["PATH"] = f"{Path(found).parent}{os.pathsep}{os.environ.get('PATH', '')}"
    return found


def main(argv: Sequence[str] | None = None) -> int:
    if not enabled():
        print("[baselines] BASELINE_SEED_ON_START is off; not seeding", flush=True)
        return 0
    binary = cargo()
    # What `just baseline-seed` builds first: the slot the benchmark links and the harness.
    for crate in ("slot", "measure"):
        subprocess.run([binary, "build", "--release", "-q"], cwd=VALIDATOR / crate, check=True)
    from bench import baselines

    print("[baselines] seeding the reference frontier (incremental)", flush=True)
    code = baselines.main(list(argv) if argv is not None else [])
    print(f"[baselines] done (exit {code})", flush=True)
    return code


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
