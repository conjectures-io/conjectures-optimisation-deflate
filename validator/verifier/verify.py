#!/usr/bin/env python3
"""The submission gate: six stages, nothing compiled for speed until the proof is accepted.

    verifier/verify.py <submission-dir>              verify and score
    verifier/verify.py <submission-dir> --no-score   the proof gate only

Pin integrity (the contract, the engine and the gate itself) is verifier/pins.py's job,
run at CI and setup time, not here: this gate trusts the checkout it is given.

    VERIFY_SANDBOX=off           run without bubblewrap (a miner's laptop; never a validator)
    VERIFY_LEAN_TIMEOUT=900      seconds the proof may take to elaborate
    VERIFY_LEAN_MEMORY_MB=16384  cgroup cap via `systemd-run --user`; 0 disables
    VERIFY_CORPUS=<name|dir>     score against this corpus instead of the default
                                 one in validator/corpora.toml

The benchmark (stage 6) has its own sandbox and its own env vars: bench/driver.py.
`--results FILE` writes the score as JSON, which is what the worker reads.

The stage report on stdout is the contract miners and tests read; diagnostics go
to stderr. Exit 0 accepted, 1 rejected, 2 the validator itself is misconfigured.
"""

from __future__ import annotations

import argparse
import dataclasses
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import time
from pathlib import Path
from typing import NoReturn, cast

from loguru import logger

ROOT = Path(__file__).resolve().parent.parent
LEAN = ROOT / "lean"

sys.path.insert(0, str(ROOT))
import bench  # noqa: E402 - after sys.path so the sibling package resolves
from bench import corpora, report, verdict  # noqa: E402

# The two files a submission supplies, and where they land.
SUBMISSION_FILES = {
    "parse.rs": "slot/generated/parse.rs",
    "Parse.lean": "lean/Proof/Parse.lean",
}

# What the submission's parser is called in the report and the results file.
SUBMISSION = "submission"

ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}

# Prover-friendly Rust, (regex, why it is rejected).
POLICY = [
    (r"\bunsafe\b", "`unsafe` is outside the translated subset"),
    (
        r"'[a-zA-Z_][a-zA-Z_0-9]*\s*:\s*(?:while|loop|for)\b",
        "labelled loops: Aeneas cannot translate labelled break/continue",
    ),
    (r"\b(?:break|continue)\s+'", "labelled break/continue"),
    (r"\bfor\b\s+\w+\s+\bin\b", "`for` loops go through Iterator, which is opaque"),
    (
        r"\.iter\(\)|\.into_iter\(\)|\.chunks\(|\.windows\(|\.fold\(|\.map\(|\.filter\(",
        "iterator adapters are opaque; use indices",
    ),
    (r"\bdyn\b|\bimpl\s+(?:Fn|Iterator)", "trait objects and impl-trait are opaque"),
    (r"\buse\s+crate::", "the slot is compiled as its own crate root"),
    (
        r"\bstd::arch|core::arch|_mm_|__m128|__m256|target_feature",
        "SIMD is outside the subset (and cannot improve ratio anyway)",
    ),
    (r"\bextern\b|\basm!|\binclude!", "no foreign code"),
    (r"\bstatic\s+mut\b", "mutable statics"),
    (
        r"\bmod\b\s+\w+|\binclude_str!|\binclude_bytes!",
        "the slot is one file; no modules and no embedded data",
    ),
]

# Lean commands that run code at elaboration time; a tactic proof needs none. Rule 7.
LEAN_POLICY = [
    (r"#eval\b", "`#eval` runs arbitrary code at elaboration time"),
    (r"\brun_(?:cmd|tac|elab|meta)\b", "runs arbitrary code at elaboration time"),
    (r"\b(?:builtin_)?initialize\b", "`initialize` runs code when the module loads"),
    (
        r"\belab(?:_rules)?\b|\bmacro(?:_rules)?\b|\bsyntax\b|\bdeclare_syntax_cat\b",
        "a custom elaborator or macro can run arbitrary code; a proof needs none",
    ),
    (r"\bdbg_trace\b|\btrace\s*\"", "tracing can forge lines in the build log"),
    (
        r"\bimport\s+(?!Lz77\b|Slot\b|Mathlib\b|Aeneas\b)",
        "a proof imports Lz77, Slot, Mathlib and Aeneas only",
    ),
]

MAX_FILE_BYTES = 512 * 1024

# Stage 3 output, hashed again after the proof builds.
EXTRACTED = ["lean/Slot/Types.lean", "lean/Slot/Funs.lean"]

# Memory is a cgroup, not an rlimit: RLIMIT_AS/DATA kill Lean's allocator at thread creation.
SANDBOX = os.environ.get("VERIFY_SANDBOX", "bwrap")
LEAN_TIMEOUT = int(os.environ.get("VERIFY_LEAN_TIMEOUT", "900"))
LEAN_MEMORY_MB = int(os.environ.get("VERIFY_LEAN_MEMORY_MB", "16384"))

# Built outside the sandbox first, then bind-mounted read-only inside it.
TRUSTED_LIBS = ["Lz77", "Slot"]

# The axiom report comes from this file alone, never from the build log a proof can write to.
AXIOM_QUERY = "import Verify.Obligation\n#print axioms accepted\n"
AXIOM_REPORT = re.compile(
    r"^'accepted' (?:depends on axioms: \[(.*)\]|does not depend on any axioms)$"
)


def sha(p: Path) -> str:
    # Hex sha256 of a file, the unit of pinning.
    return hashlib.sha256(p.read_bytes()).hexdigest()


def fail(stage: str, msg: str) -> NoReturn:
    # Reject the submission: the verdict line on stdout, exit 1.
    logger.info(f"[gate] rejected at stage {stage}")
    print(f"\nREJECTED at stage {stage}\n  {msg}")
    sys.exit(1)


def misconfigured(msg: str) -> NoReturn:
    # Stop because the validator is broken, never blaming the submission: exit 2.
    logger.warning(f"[gate] validator misconfigured: {msg.splitlines()[0]}")
    print(f"\nVALIDATOR ERROR\n  {msg}")
    sys.exit(2)


def run(
    cmd: list[str], timeout: float | None = None, cwd: Path | None = None
) -> subprocess.CompletedProcess[str]:
    # Run a command with config.sh's environment; a timeout becomes exit 124, not an exception.
    env = dict(os.environ)
    cfg = subprocess.run(
        ["bash", "-c", f'. "{ROOT}/verifier/config.sh" && env'],
        capture_output=True,
        text=True,
    )
    for line in cfg.stdout.splitlines():
        if "=" in line:
            k, v = line.split("=", 1)
            env[k] = v
    t0 = time.monotonic()
    try:
        r = subprocess.run(cmd, env=env, capture_output=True, text=True, timeout=timeout, cwd=cwd)
    except subprocess.TimeoutExpired as e:
        out = e.stdout.decode(errors="replace") if isinstance(e.stdout, bytes) else (e.stdout or "")
        r = subprocess.CompletedProcess(cmd, 124, out, f"timed out after {timeout}s")
    logger.debug(
        f"[gate] {Path(str(cmd[0])).name} exit={r.returncode} in {time.monotonic() - t0:.1f}s"
    )
    return r


def sandbox_prefix() -> list[str]:
    # bubblewrap args confining the proof: everything read-only but Lake's build dir, no network.
    if SANDBOX == "off":
        return []
    lake = (LEAN / ".lake").resolve()
    args = [
        "bwrap",
        "--ro-bind",
        "/",
        "/",
        "--dev",
        "/dev",
        "--proc",
        "/proc",
        "--tmpfs",
        "/tmp",
        "--unshare-all",
        "--die-with-parent",
        "--ro-bind",
        str(ROOT),
        str(ROOT),
    ]
    if lake.is_dir():
        args += ["--bind", str(lake), str(lake)]
        pkgs = (lake / "packages").resolve()
        if pkgs.is_dir():
            args += ["--ro-bind", str(pkgs), str(pkgs)]
        build = (lake / "build").resolve()
        for sub in ("lib/lean", "ir"):
            for lib in TRUSTED_LIBS:
                for p in sorted((build / sub).glob(f"{lib}*")):
                    args += ["--ro-bind", str(p), str(p)]
    args += ["--chdir", str(LEAN), "--"]
    if LEAN_MEMORY_MB > 0 and shutil.which("systemd-run"):
        args = [
            "systemd-run",
            "--user",
            "--scope",
            "--quiet",
            "-p",
            f"MemoryMax={LEAN_MEMORY_MB}M",
        ] + args
    return args


def check_sandbox() -> str:
    # Refuse to run as a validator without a working sandbox; return the limits in force.
    if SANDBOX == "off":
        logger.warning("[gate] running UNSANDBOXED (VERIFY_SANDBOX=off)")
        return "UNSANDBOXED, VERIFY_SANDBOX=off"
    if not shutil.which("bwrap"):
        misconfigured(
            "bubblewrap is not installed and VERIFY_SANDBOX is not `off`.\n"
            "  A validator must sandbox the proof: `sudo apt install bubblewrap`.\n"
            "  A miner checking their own submission may set VERIFY_SANDBOX=off."
        )
    probe = subprocess.run(
        [
            "bwrap",
            "--ro-bind",
            "/",
            "/",
            "--dev",
            "/dev",
            "--proc",
            "/proc",
            "--unshare-all",
            "--die-with-parent",
            "true",
        ],
        capture_output=True,
        text=True,
    )
    if probe.returncode != 0:
        misconfigured(
            "bubblewrap is installed but cannot create a sandbox here:\n  "
            + probe.stderr.strip().replace("\n", "\n  ")
            + "\n  On Ubuntu 24.04: "
            + "`sudo sysctl -w kernel.apparmor_restrict_unprivileged_userns=0`."
        )
    mem = f"{LEAN_MEMORY_MB} MB" if LEAN_MEMORY_MB > 0 and shutil.which("systemd-run") else "no cap"
    if mem == "no cap":
        logger.warning("[gate] systemd-run not found: the proof runs without a memory cap")
    return f"bwrap, {LEAN_TIMEOUT}s, {mem}"


# ── The stages ────────────────────────────────────────────────────────────


def stage_intake(sub: Path) -> None:
    # Copy exactly parse.rs and Parse.lean in; anything else in the directory is a rejection.
    if not sub.is_dir():
        misconfigured(f"{sub} is not a directory")
    for name in SUBMISSION_FILES:
        src = sub / name
        if not src.is_file():
            fail("0 (intake)", f"the submission has no {name}")
        if src.stat().st_size > MAX_FILE_BYTES:
            fail("0 (intake)", f"{name} is {src.stat().st_size} bytes; limit is {MAX_FILE_BYTES}")
    extra = sorted(
        p.name
        for p in sub.iterdir()
        if p.name not in SUBMISSION_FILES
        and not p.name.startswith(".")
        and p.suffix in {".rs", ".lean"}
    )
    if extra:
        fail("0 (intake)", f"a submission is two files; found also: {', '.join(extra)}")
    for name, dest in SUBMISSION_FILES.items():
        (ROOT / dest).parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(sub / name, ROOT / dest)
        logger.debug(f"[gate] {name} {sha(sub / name)[:16]} -> {dest}")
    print(f"0 intake      ok — {sub.name}: parse.rs, Parse.lean")


def scan(text: str, rules: list[tuple[str, str]]) -> list[str]:
    # Every match of `rules` in `text`, as `line ~N: <match> — <why>`.
    bad: list[str] = []
    for pattern, why in rules:
        for m in re.finditer(pattern, text):
            line = text[: m.start()].count("\n") + 1
            bad.append(f"line ~{line}: {m.group(0)!r} — {why}")
    return bad


def scan_rust(src: str) -> list[str]:
    # Rust policy with comments stripped, so a rule named in a doc comment is not a violation.
    stripped = re.sub(r"//[^\n]*", "", src)
    stripped = re.sub(r"/\*.*?\*/", "", stripped, flags=re.S)
    return scan(stripped, POLICY)


def scan_lean(src: str) -> list[str]:
    # Lean policy on the raw text: a `--` inside a string literal must not hide the line.
    return scan(src, LEAN_POLICY)


def stage_policy() -> None:
    # Reject Rust outside the translated subset and Lean that runs code.
    bad = scan_rust((ROOT / "slot/generated/parse.rs").read_text())
    bad += [f"Parse.lean {b}" for b in scan_lean((ROOT / "lean/Proof/Parse.lean").read_text())]
    if bad:
        fail("1 (policy)", "\n  ".join(bad))
    print("1 policy      ok — the Rust is inside the subset; the proof runs no code")


def stage_extract() -> dict[str, str]:
    # Run charon+aeneas ourselves; an extraction supplied by the miner is never trusted.
    r = run([str(ROOT / "verifier/extract.sh")])
    if r.returncode == 2:
        misconfigured((r.stderr or r.stdout).strip()[:2000])
    if r.returncode != 0:
        fail("3 (extract)", (r.stderr or r.stdout).strip()[:2000])
    hashes = {p: sha(ROOT / p) for p in EXTRACTED}
    logger.debug(
        f"[gate] extracted {', '.join(f'{Path(p).name} {h[:16]}' for p, h in hashes.items())}"
    )
    print("3 extract     ok — charon+aeneas re-run by the verifier, no new axioms")
    return hashes


def stage_build(limits: str) -> None:
    # Build the trusted libraries outside the sandbox, then the proof and gate inside it.
    r = run(["lake", "build", *TRUSTED_LIBS], cwd=LEAN)
    out = r.stdout + r.stderr
    if r.returncode != 0:
        if "unknown package" in out or "no such file" in out.lower():
            misconfigured(out.strip()[-2000:])
        errs = [ln for ln in out.splitlines() if ln.startswith("error")]
        fail("3 (extract)", "the extracted slot does not build:\n  " + "\n  ".join(errs[:20]))
    prefix = sandbox_prefix()
    logger.debug(f"[gate] sandbox: {' '.join(prefix) if prefix else 'off'}")
    r = run(prefix + ["lake", "build", "Verify"], cwd=LEAN, timeout=LEAN_TIMEOUT)
    out = r.stdout + r.stderr
    if r.returncode == 124:
        fail("4 (statement)", f"the proof did not finish elaborating in {LEAN_TIMEOUT}s")
    if r.returncode != 0:
        errs = [ln for ln in out.splitlines() if ln.startswith("error")]
        fail("4 (statement)", "\n  ".join(errs[:20]) or out.strip()[-2000:])
    print(f"4 statement   ok — `LZ77.Obligation slot.parse` typechecks ({limits})")


def stage_axioms(extracted: dict[str, str]) -> None:
    # Read the axioms from a dedicated lean run, then re-hash the pins and the extraction.
    query = ROOT / ".work/axioms.lean"
    query.parent.mkdir(exist_ok=True)
    query.write_text(AXIOM_QUERY)
    r = run(sandbox_prefix() + ["lake", "env", "lean", str(query)], cwd=LEAN, timeout=LEAN_TIMEOUT)
    logger.debug(f"[gate] axiom query stdout: {r.stdout.strip()!r}")
    reports = [m for m in map(AXIOM_REPORT.match, r.stdout.splitlines()) if m]
    if r.returncode != 0 or len(reports) != 1:
        misconfigured(
            "the axiom query did not produce exactly one report:\n"
            + (r.stdout + r.stderr).strip()[-2000:]
        )
    names = {n.strip() for n in (reports[0].group(1) or "").split(",") if n.strip()}
    extra = names - ALLOWED_AXIOMS
    if extra:
        fail("5 (axioms)", f"the proof rests on {sorted(extra)}")
    changed = [p for p in EXTRACTED if sha(ROOT / p) != extracted[p]]
    if changed:
        fail(
            "5 (axioms)",
            "the extraction changed while the proof was being checked:\n  " + "\n  ".join(changed),
        )
    print(f"5 axioms      ok — {sorted(names)}; extraction intact")


def bench_config() -> bench.Config:
    # Env-var defaults live in bench/driver.py. The reference bars are context
    # for a report, never part of a verdict, and cost more than the parsers do.
    return dataclasses.replace(bench.Config.from_env(ROOT), bars=False)


def stage_score(results: Path | None) -> int:
    # Only now compile natively: round trip, compressed bytes, speed floor.
    # The engine measures and this decides; SPEED_FLOOR is the only policy here.
    corpus = corpora.default(ROOT)
    logger.debug(f"[gate] scoring against {corpus.name} ({corpus.path})")
    if not any(corpus.path.iterdir()):
        misconfigured(f"corpus {corpus.path} is empty; run `verifier/make-corpus.py`")
    print("6 score       running…\n")

    proved = ROOT / SUBMISSION_FILES["parse.rs"]
    try:
        measured = bench.run(
            bench_config(), {SUBMISSION: proved}, corpus, speed_floor=verdict.SPEED_FLOOR
        )
    except bench.Blamed as e:
        fail("6 (score)", f"{e}\n{e.detail[-2000:]}")
    except bench.Failed as e:
        misconfigured(f"{e}\n{e.detail[-2000:]}")
    except bench.Misconfigured as e:
        misconfigured(str(e))

    run = measured.only()
    # What was measured must be what was extracted and proved. They are one file
    # on disk, so this can only fail if something rewrote it mid-gate.
    if (run.meta.methods[SUBMISSION].source_sha256 or "") != sha(proved):
        fail("6 (score)", "the parse.rs that was measured is not the one that was proved")

    print(report.table(measured, verdict.SPEED_FLOOR))
    v = verdict.judge(run, SUBMISSION, verdict.SPEED_FLOOR)
    print()
    for f in v.failures[:20]:
        print(f"  {f}")
    print(v.line())
    if results is not None:
        results.write_text(json.dumps(report.summary(measured, verdict.SPEED_FLOOR), indent=2))
    return 0 if v.accepted else 1


def main() -> None:
    # Parse arguments and run the stages in order; the order is the design.
    ap = argparse.ArgumentParser(description=(__doc__ or "").split("\n")[0])
    ap.add_argument("submission", help="directory with parse.rs and Parse.lean")
    ap.add_argument("--no-score", action="store_true", help="stop after the proof gate")
    ap.add_argument("--results", type=Path, help="write the score as JSON here")
    args = ap.parse_args()
    submission = cast(str, args.submission)
    no_score = cast(bool, args.no_score)
    results = cast("Path | None", args.results)

    t0 = time.monotonic()
    limits = check_sandbox()
    if not no_score:
        try:
            bench_limits = bench.check(bench_config())
        except bench.Misconfigured as e:
            misconfigured(str(e))
        logger.debug(f"[gate] benchmark sandbox: {bench_limits}")
    print(f"verifying {submission}\n")
    stage_intake(Path(submission).resolve())
    stage_policy()
    extracted = stage_extract()
    stage_build(limits)
    stage_axioms(extracted)
    logger.info(f"[gate] proof accepted in {time.monotonic() - t0:.1f}s ({limits})")
    if no_score:
        print("\nproof accepted (scoring skipped)")
        return
    sys.exit(stage_score(results))


if __name__ == "__main__":
    main()
