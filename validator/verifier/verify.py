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
import datetime as dt
import hashlib
import json
import os
import re
import signal
import subprocess
import sys
import tempfile
import time
import tomllib
from pathlib import Path
from typing import NoReturn, cast

from loguru import logger
from sqlalchemy.exc import SQLAlchemyError

ROOT = Path(__file__).resolve().parent.parent
lean_root = ROOT / "lean"

sys.path.insert(0, str(ROOT))
import bench  # noqa: E402 - after sys.path so the sibling package resolves
import db  # noqa: E402
from bench import corpora, report, verdict  # noqa: E402
from sandbox import bwrap  # noqa: E402
from verifier import resolved  # noqa: E402
from verifier.identity import fingerprint  # noqa: E402
from verifier.workspace import Workspace  # noqa: E402

work_root = ROOT
active_workspace: Workspace | None = None

# The two files a submission supplies, and where they land.
SUBMISSION_FILES = {
    "parse.rs": "slot/generated/parse.rs",
    "Parse.lean": "lean/Proof/Parse.lean",
}

# What the submission's parser is called in the report and the results file.
SUBMISSION = "submission"

ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}

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
EXTRACTED = ["lean/Slot/Types.lean", "lean/Slot/Funs.lean", "lean/Slot/Constants.lean"]

# Memory is a cgroup, not an rlimit: RLIMIT_AS/DATA kill Lean's allocator at thread creation.
SANDBOX = os.environ.get("VERIFY_SANDBOX", "bwrap")
TOOL_TIMEOUT = int(os.environ.get("VERIFY_TOOL_TIMEOUT", "900"))
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
    if active_workspace is not None:
        active_workspace.record(stage, "rejected", msg)
    logger.info(f"[gate] rejected at stage {stage}")
    print(f"\nREJECTED at stage {stage}\n  {msg}")
    sys.exit(1)


def misconfigured(msg: str) -> NoReturn:
    # Stop because the validator is broken, never blaming the submission: exit 2.
    if active_workspace is not None:
        active_workspace.record("infrastructure", "error", msg)
    logger.warning(f"[gate] validator misconfigured: {msg.splitlines()[0]}")
    print(f"\nVALIDATOR ERROR\n  {msg}")
    sys.exit(2)


def tool_environment() -> dict[str, str]:
    # Configuration is operator-owned; never pass database/API credentials to tools.
    cfg = subprocess.run(
        ["bash", "-c", 'source "$1" && env -0', "config", str(ROOT / "verifier/config.sh")],
        capture_output=True,
        check=True,
    )
    values = dict(entry.split("=", 1) for entry in cfg.stdout.decode().split("\0") if "=" in entry)
    allowed = {
        "PATH",
        "HOME",
        "ELAN_HOME",
        "RUSTUP_HOME",
        "CARGO_HOME",
        "AENEAS_WORK",
        "CHARON_DIR",
        "CHARON_TOOLCHAIN",
        "LEAN_TOOLCHAIN",
        "XDG_RUNTIME_DIR",
        "DBUS_SESSION_BUS_ADDRESS",
    }
    env = {key: value for key, value in values.items() if key in allowed} | {
        "LANG": "C.UTF-8",
        "LC_ALL": "C.UTF-8",
        "TMPDIR": "/tmp",
    }
    for key in ("AENEAS_WORK", "CHARON_DIR", "ELAN_HOME", "CARGO_HOME", "RUSTUP_HOME"):
        if key in env:
            env[key] = str(Path(env[key]).resolve())
    return env


def sandbox_spec(*, proof: bool = True, output: str = "Proof") -> bwrap.Sandbox:
    env = tool_environment()
    home = Path(env["HOME"])
    dependencies = [
        ROOT / "verifier",
        work_root,
        ROOT / "lean/.lake/packages",
        Path(env["AENEAS_WORK"]),
        Path(env["ELAN_HOME"]),
        Path(env.get("RUSTUP_HOME", str(home / ".rustup"))),
        Path(env.get("CARGO_HOME", str(home / ".cargo"))) / "bin",
    ]
    frozen: list[Path] = [lean_root / ".lake/packages"]
    if proof:
        build = lean_root / ".lake/build/lib/lean"
        # Submitted elaboration can write only its own module outputs. It cannot
        # forge the obligation or modify a previously checked dependency.
        writable = (build / output,) if output else ()
        for path in writable:
            path.mkdir(parents=True, exist_ok=True)
    else:
        writable = (lean_root / ".lake", lean_root / "Slot", lean_root / ".extract")
        # Extraction has its own writable output directory; inputs remain read-only.
        if not (lean_root / "slot.llbc").exists():
            (lean_root / "slot.llbc").touch()
        writable += (lean_root / "slot.llbc",)
    return bwrap.Sandbox(
        enabled=SANDBOX != "off",
        ro_binds=tuple(p for p in dependencies if p.exists()),
        rw_binds=writable,
        memory_mb=LEAN_MEMORY_MB,
        minimal=True,
        frozen_binds=tuple(frozen),
    )


def run(
    cmd: list[str],
    timeout: float | None = None,
    cwd: Path | None = None,
    *,
    proof: bool = True,
    output: str = "Proof",
) -> bwrap.Result:
    result = bwrap.run(
        sandbox_spec(proof=proof, output=output),
        cmd,
        cwd=cwd or work_root,
        timeout=timeout or (LEAN_TIMEOUT if proof else TOOL_TIMEOUT),
        env=tool_environment(),
    )
    if active_workspace is not None:
        logs = active_workspace.path / "logs"
        (logs / f"{len(list(logs.iterdir())):03d}-{Path(cmd[0]).name}.log").write_text(
            result.stdout + result.stderr
        )
    return result


def check_sandbox() -> str:
    if SANDBOX == "off":
        logger.warning("[gate] running UNSANDBOXED (VERIFY_SANDBOX=off)")
        return "UNSANDBOXED, VERIFY_SANDBOX=off"
    try:
        bwrap.check(True)
        bwrap.check_resources(bwrap.Sandbox(memory_mb=LEAN_MEMORY_MB))
    except bwrap.Unavailable as exc:
        misconfigured(str(exc))
    return f"bwrap, {LEAN_TIMEOUT}s, {LEAN_MEMORY_MB} MB"


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
        assert active_workspace is not None
        data = (sub / name).read_bytes()
        if len(data) > MAX_FILE_BYTES:
            fail("0 (intake)", f"{name} exceeds the size limit")
        active_workspace.snapshot(name, data, dest)
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
    checker = ROOT / "precheck/target/release/submission-precheck"
    if not checker.is_file():
        misconfigured(
            "missing syntax checker: build validator/precheck with cargo build --release --locked"
        )
    with tempfile.TemporaryDirectory(prefix="syntax-") as tmp:
        path = Path(tmp) / "parse.rs"
        path.write_text(src)
        result = subprocess.run(
            [str(checker), str(path)], capture_output=True, text=True, timeout=30
        )
    if result.returncode not in (0, 1):
        misconfigured("syntax checker failed: " + result.stderr)
    diagnostics = cast(dict[str, list[dict[str, str | int]]], json.loads(result.stdout))[
        "diagnostics"
    ]
    return [f"line ~{entry['line']}: {entry['message']}" for entry in diagnostics]


def scan_lean(src: str) -> list[str]:
    # Lean policy on the raw text: a `--` inside a string literal must not hide the line.
    return scan(src, LEAN_POLICY)


def stage_policy(*, check_proof: bool = True) -> None:
    # Reject Rust outside the translated subset and Lean that runs code.
    bad = scan_rust((work_root / "slot/generated/parse.rs").read_text())
    if check_proof:
        bad += [
            f"Parse.lean {b}" for b in scan_lean((work_root / "lean/Proof/Parse.lean").read_text())
        ]
    if bad:
        fail("1 (policy)", "\n  ".join(bad))
    print("1 policy      ok — source prefilters passed")


def stage_static() -> None:
    compiler = run(
        ["rustup", "run", tool_environment()["CHARON_TOOLCHAIN"], "rustc", "--version"],
        timeout=30,
        proof=False,
    )
    if compiler.returncode:
        misconfigured("Rust toolchain preflight failed: " + compiler.stderr.strip())
    r = run(
        [
            str(ROOT / "verifier/extract.sh"),
            str(work_root / "slot/generated/parse.rs"),
            str(lean_root),
            "compile",
        ],
        proof=False,
    )
    if r.returncode == 2:
        misconfigured((r.stderr or r.stdout).strip()[-2000:])
    if r.returncode:
        fail("2 (static)", (r.stdout + r.stderr).strip()[-2000:])
    try:
        operations = resolved.check(lean_root / "slot.llbc")
    except resolved.Unsupported as exc:
        fail("2 (static)", str(exc))
    print(f"2 static      ok — resolved operations: {', '.join(operations)}")


def stage_extract() -> dict[str, str]:
    # Run charon+aeneas ourselves; an extraction supplied by the miner is never trusted.
    r = run(
        [
            str(ROOT / "verifier/extract.sh"),
            str(work_root / "slot/generated/parse.rs"),
            str(lean_root),
            "translate",
        ],
        proof=False,
    )
    if r.returncode == 2:
        misconfigured((r.stderr or r.stdout).strip()[:2000])
    if r.returncode != 0:
        fail("3 (extract)", (r.stderr or r.stdout).strip()[:2000])
    hashes = {p: sha(work_root / p) for p in EXTRACTED}
    logger.debug(
        f"[gate] extracted {', '.join(f'{Path(p).name} {h[:16]}' for p, h in hashes.items())}"
    )
    print("3 extract     ok — charon+aeneas re-run by the verifier, no new axioms")
    return hashes


def stage_build(limits: str) -> None:
    if not (lean_root / ".lake/packages/aeneas").exists():
        misconfigured("Lean dependency cache is missing; run just init")
    lean = run(["lake", "env", "lean", "--version"], cwd=lean_root, timeout=30, proof=False)
    if lean.returncode:
        misconfigured("Lean toolchain preflight failed: " + (lean.stdout + lean.stderr).strip())
    # Build trusted libraries in the compiler sandbox, then restrict writes for the proof and gate.
    r = run(["lake", "build", *TRUSTED_LIBS], cwd=lean_root, proof=False)
    out = r.stdout + r.stderr
    if r.returncode != 0:
        if any(
            message in out.lower()
            for message in (
                "unknown package",
                "no such file",
                "read-only file system",
                "permission denied",
            )
        ):
            misconfigured(out.strip()[-2000:])
        errs = [ln for ln in out.splitlines() if ln.startswith("error")]
        fail("3 (extract)", "the extracted slot does not build:\n  " + "\n  ".join(errs[:20]))
    r = run(
        ["lake", "env", "lean", "-o", ".lake/build/lib/lean/Proof/Parse.olean", "Proof/Parse.lean"],
        cwd=lean_root,
        timeout=LEAN_TIMEOUT,
    )
    out = r.stdout + r.stderr
    if r.returncode == 124:
        fail("4 (statement)", f"the proof did not finish elaborating in {LEAN_TIMEOUT}s")
    if r.returncode != 0:
        fail("4 (statement)", out.strip()[-2000:])
    r = run(
        [
            "lake",
            "env",
            "lean",
            "-o",
            ".lake/build/lib/lean/Verify/Obligation.olean",
            "Verify/Obligation.lean",
        ],
        cwd=lean_root,
        timeout=LEAN_TIMEOUT,
        output="Verify",
    )
    out = r.stdout + r.stderr
    if r.returncode == 124:
        fail("4 (statement)", f"the proof did not finish elaborating in {LEAN_TIMEOUT}s")
    if r.returncode != 0:
        errs = [ln for ln in out.splitlines() if ln.startswith("error")]
        fail("4 (statement)", "\n  ".join(errs[:20]) or out.strip()[-2000:])
    print(f"4 statement   ok — `LZ77.Obligation slot.parse` typechecks ({limits})")


def stage_axioms(extracted: dict[str, str]) -> None:
    # Read the axioms from a dedicated lean run, then re-hash the pins and the extraction.
    query = work_root / "axioms.lean"
    query.parent.mkdir(exist_ok=True)
    query.write_text(AXIOM_QUERY)
    r = run(["lake", "env", "lean", str(query)], cwd=lean_root, timeout=LEAN_TIMEOUT, output="")
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
    changed = [p for p in EXTRACTED if sha(work_root / p) != extracted[p]]
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

    proved = work_root / SUBMISSION_FILES["parse.rs"]
    assert active_workspace is not None
    expected = active_workspace.hashes["parse.rs"]
    if sha(proved) != expected:
        fail("6 (score)", "source changed after intake")
    try:
        measured = bench.run(
            bench_config(), {SUBMISSION: proved}, corpus, speed_floor=verdict.SPEED_FLOOR
        )
    except bench.Blamed as e:
        # Only the submission's own failure is a verdict; a broken incumbent is ours.
        if e.method != SUBMISSION:
            misconfigured(f"{e}\n{e.detail[-2000:]}")
        fail("6 (score)", f"{e}\n{e.detail[-2000:]}")
    except bench.Failed as e:
        misconfigured(f"{e}\n{e.detail[-2000:]}")
    except bench.Misconfigured as e:
        misconfigured(str(e))

    run = measured.only()
    # What was measured must be what was extracted and proved. They are one file
    # on disk, so this can only fail if something rewrote it mid-gate.
    if (run.meta.methods[SUBMISSION].source_sha256 or "") != expected:
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


def terminate(_signum: int, _frame: object) -> NoReturn:
    raise SystemExit(2)


def main() -> None:
    signal.signal(signal.SIGTERM, terminate)
    # Parse arguments and run the stages in order; the order is the design.
    ap = argparse.ArgumentParser(description=(__doc__ or "").split("\n")[0])
    ap.add_argument(
        "submission", nargs="?", default="", help="directory with parse.rs and Parse.lean"
    )
    ap.add_argument("--submission-id", type=int)
    ap.add_argument("--claim")
    ap.add_argument("--claim-token")
    ap.add_argument("--stage", choices=("full", "static", "lean", "extract"), default="full")
    ap.add_argument("--proof", type=Path)
    ap.add_argument("--keep", choices=("auto", "always", "never"), default="auto")
    ap.add_argument("--no-score", action="store_true", help="stop after the proof gate")
    ap.add_argument("--results", type=Path, help="write the score as JSON here")
    args = ap.parse_args()
    submission = cast(str, args.submission)
    stage = cast(str, args.stage)
    no_score = cast(bool, args.no_score) or stage != "full"
    results = cast("Path | None", args.results)

    store: db.Store | None = None
    sub_id = cast(int | None, args.submission_id)
    claim = cast(str | None, args.claim)
    if sub_id is not None:
        if SANDBOX == "off":
            misconfigured("DB verification requires the sandbox")
        from service.settings import load

        try:
            store = db.connect()
            store.ping()
        except SQLAlchemyError as exc:
            misconfigured(f"database preflight failed: {type(exc).__name__}")
        submission = str(load().submission_dir(sub_id))
    elif not submission:
        ap.error("a source/submission path or --submission-id is required")
    t0 = time.monotonic()
    limits = check_sandbox()
    native = cast(
        dict[str, dict[str, str]], tomllib.loads((ROOT / "rust-toolchain.toml").read_text())
    )["toolchain"]["channel"]
    if tool_environment()["CHARON_TOOLCHAIN"] != native:
        misconfigured("extraction and native Rust toolchains must match")
    overrides = [
        key
        for key, value in os.environ.items()
        if value
        and (
            key in {"RUSTFLAGS", "CARGO_ENCODED_RUSTFLAGS", "RUSTUP_TOOLCHAIN"}
            or key.startswith("CARGO_PROFILE_RELEASE_")
        )
    ]
    if overrides:
        misconfigured(
            "verification requires the pinned compilation recipe; unset " + ", ".join(overrides)
        )
    if not no_score:
        try:
            bench_limits = bench.check(bench_config())
        except bench.Misconfigured as e:
            misconfigured(str(e))
        logger.debug(f"[gate] benchmark sandbox: {bench_limits}")
    global active_workspace, work_root, lean_root
    active_workspace = Workspace(ROOT)
    work_root = active_workspace.path
    lean_root = work_root / "lean"
    code = 2
    token = ""
    cached = False
    verification_id = ""
    try:
        print(f"verifying {submission}\nworkspace: {work_root}\n")
        if stage == "full" or sub_id is not None:
            stage_intake(Path(submission).resolve())
        else:
            with tempfile.TemporaryDirectory(prefix="verification-input-") as tmp:
                inputs = Path(tmp)
                (inputs / "parse.rs").write_bytes(Path(submission).read_bytes())
                proof = cast(Path | None, args.proof)
                if stage == "lean" and proof is None:
                    misconfigured("--stage lean requires --proof FILE")
                (inputs / "Parse.lean").write_bytes(proof.read_bytes() if proof else b"")
                stage_intake(inputs)
        if store is not None and sub_id is not None:
            verification_id = fingerprint()
            token, cached = store.verification.begin(
                sub_id,
                (work_root / "slot/generated/parse.rs").read_bytes(),
                (lean_root / "Proof/Parse.lean").read_bytes(),
                verification_id,
                lean_only=stage == "lean",
                reuse=stage == "full",
                expected_claim=dt.datetime.fromisoformat(claim) if claim else None,
                expected_attempt=cast(str | None, args.claim_token),
            )
        if not cached:
            stage_policy(check_proof=stage != "static")
            stage_static()
            active_workspace.record("static", "passed")
            if store is not None and sub_id is not None and stage != "lean":
                if fingerprint() != verification_id:
                    misconfigured("trusted verification inputs changed during static analysis")
                store.verification.publish(sub_id, token, "static")
            if stage != "static":
                extracted = stage_extract()
                if stage != "extract":
                    stage_build(limits)
                    stage_axioms(extracted)
                    active_workspace.record("lean", "passed")
                    if store is not None and sub_id is not None:
                        if fingerprint() != verification_id:
                            misconfigured(
                                "trusted verification inputs changed during Lean checking"
                            )
                        store.verification.publish(sub_id, token, "lean")
        else:
            print("reusing matching static and Lean verification")
        logger.info(f"[gate] verification accepted in {time.monotonic() - t0:.1f}s ({limits})")
        if no_score:
            print(
                "\nproof accepted (scoring skipped)"
                if stage in ("full", "lean")
                else f"\n{stage} verification accepted (scoring skipped)"
            )
            code = 0
        else:
            if store is not None and fingerprint() != verification_id:
                misconfigured("trusted verification inputs changed before native compilation")
            code = stage_score(results)
            if code == 0 and store is not None and sub_id is not None:
                store.verification.publish(sub_id, token, "measured")
    except (OSError, SQLAlchemyError, ValueError, db.verification.StaleAttempt) as exc:
        misconfigured(str(exc))
    except SystemExit as exc:
        code = exc.code if isinstance(exc.code, int) else 2
        raise
    finally:
        active_workspace.finish(code, cast(str, args.keep))
        if store is not None:
            store.close()
    sys.exit(code)


if __name__ == "__main__":
    main()
