#!/usr/bin/env python3
"""Show the proof state at one line of a submission's Parse.lean: goals and hypotheses.

    verifier/probe.py <submission-dir> <line> [--stop]

Extracts the submission's parse.rs exactly as the gate does, into a private workspace,
inserts `trace_state` before the tactic at <line> (with --stop, also `all_goals sorry`, so
the rest of that proof is skipped) into a copy of the proof, elaborates the copy there, and
prints what Lean saw. Generated `_✝` hypotheses and the `[> let ... <]` markers are dropped.
Use it when a `first | ... | ...` chain or a `scalar_tac` fails and the error hides the goal.
"""

from __future__ import annotations

import argparse
import os
import re
import shutil
import subprocess
import sys
from pathlib import Path
from typing import cast

from loguru import logger

ROOT = Path(__file__).resolve().parent.parent
NOISE = re.compile(r"^(_✝|_ :|\s*\[> let|warning:|Note:|\s*$)")
WORKSPACE = re.compile(r"^workspace: (.+)$", re.MULTILINE)


def instrument(source: str, line: int, stop: bool) -> str:
    # Insert `trace_state` (and `all_goals sorry`) before `line`, at that line's indentation.
    lines = source.split("\n")
    if not 1 <= line <= len(lines):
        sys.exit(f"line {line} is outside the file (1..{len(lines)})")
    target = lines[line - 1]
    indent = target[: len(target) - len(target.lstrip())]
    inserted = [indent + "trace_state"] + ([indent + "all_goals sorry"] if stop else [])
    return "\n".join(lines[: line - 1] + inserted + lines[line - 1 :])


def extract(submission: Path) -> Path:
    # The gate's own extraction stage, kept, so the probe sees the `slot.*` the proof is judged on.
    r = subprocess.run(
        [
            sys.executable,
            str(ROOT / "verifier/verify.py"),
            str(submission / "parse.rs"),
            "--stage",
            "extract",
            "--keep",
            "always",
        ],
        capture_output=True,
        text=True,
    )
    m = WORKSPACE.search(r.stdout)
    if r.returncode != 0 or m is None:
        sys.exit(f"extraction failed:\n{r.stdout}{r.stderr}")
    return Path(m.group(1)) / "lean"


def elaborate(lean: Path, probe: Path) -> str:
    # Build the extracted model first: `lake env lean` elaborates against the oleans on disk.
    elan_home = Path(os.environ.get("ELAN_HOME", ROOT / ".work/elan"))
    lake = elan_home / "bin/lake"
    lake_command = str(lake) if lake.is_file() else shutil.which("lake")
    if lake_command is None:
        sys.exit("lake not found; run ./setup.sh to install the Lean toolchain")
    build = subprocess.run(
        [lake_command, "build", "Lz77", "Slot"], cwd=lean, capture_output=True, text=True
    )
    if build.returncode != 0:
        sys.exit(f"the extracted model does not build:\n{build.stderr}{build.stdout}")
    r = subprocess.run(
        [lake_command, "env", "lean", str(probe)], cwd=lean, capture_output=True, text=True
    )
    return r.stdout + r.stderr


def tidy(output: str, probe: Path) -> str:
    # Keep goal states and errors; drop generated names, bind markers and warnings.
    kept = [ln for ln in output.split("\n") if not NOISE.match(ln)]
    return "\n".join(kept).replace(str(probe), "Parse.lean")


def main() -> None:
    # Dispatch.
    ap = argparse.ArgumentParser(prog="probe.py", description=(__doc__ or "").split("\n")[0])
    ap.add_argument("submission", help="directory with parse.rs and Parse.lean")
    ap.add_argument("line", type=int, help="1-based line in Parse.lean to look at")
    ap.add_argument("--stop", action="store_true", help="also close the goals there with sorry")
    args = ap.parse_args()
    submission = Path(cast(str, args.submission)).resolve()
    line, stop = cast(int, args.line), cast(bool, args.stop)
    proof = submission / "Parse.lean"
    if not proof.is_file() or not (submission / "parse.rs").is_file():
        sys.exit(f"{submission} must contain parse.rs and Parse.lean")
    lean = extract(submission)
    probe = lean / "Probe.lean"
    probe.write_text(instrument(proof.read_text(), line, stop))
    logger.info(f"[probe] {proof} line {line}: elaborating in {lean.parent}")
    print(tidy(elaborate(lean, probe), probe))


if __name__ == "__main__":
    main()
