#!/usr/bin/env python3
"""The submission gate.

    verifier/verify.py <submission-dir>      verify and score a submission
    verifier/verify.py <submission-dir> --no-score
    verifier/verify.py --pin                 re-pin the contract after an
                                             operator-side change

A submission directory contains exactly two files:

    parse.rs      the miner's LZ77 parser
    Parse.lean    the miner's proof that it satisfies the published contract

They are copied into `slot/src/parse.rs` and `lean/Proof/Parse.lean` and nothing
else is taken from the submission -- in particular not an extraction, and not a
statement of what was proved.

Six stages, and **the order is the design**. Nothing is compiled for speed and
nothing is timed until the proof has been accepted, so a submission cannot buy
validator time with a program that has no proof.

    1  policy      the submitted Rust is inside the prover-friendly subset
    2  pins        the contract and harness are byte-identical to what is pinned
    3  extract     the verifier runs charon+aeneas ITSELF on the submitted Rust
    4  statement   `LZ77.Obligation slot.parse` typechecks from the miner's proof
    5  axioms      nothing beyond propext / Classical.choice / Quot.sound
    6  score       only now: build, round-trip, compressed bytes, time budget

Every stage that runs a subprocess runs it under a **wall-clock budget** (see
`TIMEOUTS`), because a submission's `Parse.lean` is half a megabyte of arbitrary
tactic script and Lean's own `maxHeartbeats` can be raised from inside that file.
A budget outside the process is the only version of the limit a submission cannot
argue with, and a timeout kills the whole process group so nothing is left
pinning cores.

Exit codes: 0 accepted, 1 rejected, 2 the validator itself is misconfigured.
"""

import argparse
import hashlib
import json
import os
import re
import shutil
import signal
import subprocess
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
LEAN = ROOT / "lean"

#: The two files a submission supplies, and where they land.
SUBMISSION_FILES = {
    "parse.rs": "slot/src/parse.rs",
    "Parse.lean": "lean/Proof/Parse.lean",
}

#: Everything that participates in the verdict, pinned by hash. A submission
#: cannot change any of it, so it cannot edit the contract it is judged against
#: nor the encoder it is scored through.
PINNED = [
    "lean/Lz77/Spec.lean",
    "lean/Lz77/Lemmas.lean",
    "lean/Lz77/Interface.lean",
    "lean/Lz77.lean",
    "lean/Verify/Obligation.lean",
    "lean/Verify.lean",
    "lean/Proof/Axioms.lean",
    "lean/Proof.lean",
    "lean/Slot.lean",
    "lean/lakefile.toml",
    "lean/lean-toolchain",
    "lean/lake-manifest.json",
    "harness/src/deflate.rs",
    "harness/src/token.rs",
    "harness/src/baseline.rs",
    "harness/src/main.rs",
    "harness/src/reference.rs",
    "harness/src/headroom.rs",
    "harness/Cargo.toml",
    "slot/Cargo.toml",
    "slot/src/lib.rs",
    "verifier/verify.py",
    "verifier/extract.sh",
    "verifier/config.sh",
    "verifier/make-corpus.py",
]

ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}

#: Prover-friendly Rust, enforced. Each entry is (regex, why it is rejected).
#: Every one of these was found by something failing rather than by reading a
#: manual, and each is documented with a worked example in
#: `../miner/RULES.md`. A miner who discovers a rule by failing is a miner
#: who leaves.
POLICY = [
    (r"\bunsafe\b", "`unsafe` is outside the translated subset"),
    (r"'[a-zA-Z_][a-zA-Z_0-9]*\s*:\s*(?:while|loop|for)\b",
     "labelled loops: Aeneas cannot translate labelled break/continue"),
    (r"\b(?:break|continue)\s+'", "labelled break/continue"),
    (r"\bfor\b\s+\w+\s+\bin\b", "`for` loops go through Iterator, which is opaque"),
    (r"\.iter\(\)|\.into_iter\(\)|\.chunks\(|\.windows\(|\.fold\(|\.map\(|\.filter\(",
     "iterator adapters are opaque; use indices"),
    (r"\bdyn\b|\bimpl\s+(?:Fn|Iterator)", "trait objects and impl-trait are opaque"),
    (r"\buse\s+crate::", "the slot is compiled as its own crate root"),
    (r"\bstd::arch|core::arch|_mm_|__m128|__m256|target_feature",
     "SIMD is outside the subset (and cannot improve ratio anyway)"),
    (r"\bextern\b|\basm!|\binclude!", "no foreign code"),
    (r"\bstatic\s+mut\b", "mutable statics"),
    (r"\bmod\b\s+\w+|\binclude_str!|\binclude_bytes!",
     "the slot is one file; no modules and no embedded data"),
]

#: Namespaces a submitted proof may not declare into, and why.
#:
#: A proof that declares `slot.parse` is claiming to *be* the extraction rather
#: than to be about it. The structural defence is that `Verify/Obligation.lean`
#: imports `Lz77` and `Slot` itself, so the gate resolves those names to the
#: operator's definitions and a submission's redeclaration collides at import.
#: This check exists so the rejection says what went wrong.
#:
#: It was found by attack, not by review: a submission that omitted `import Slot`
#: from its own `Parse.lean` left `slot.parse` free, defined it as a program it
#: could prove, and passed the statement check — while stage 6 scored the real
#: `parse.rs`, which nothing had proved anything about.
PROOF_POLICY = [
    (r"^\s*namespace\s+(?:slot|LZ77)\b",
     "a submission may not open the `slot` or `LZ77` namespace: those names are "
     "the extraction and the contract, and a proof is about them, not a "
     "redefinition of them"),
    (r"^\s*(?:@\[[^\]]*\]\s*)?(?:noncomputable\s+)?(?:private\s+|protected\s+)?"
     r"(?:def|abbrev|theorem|lemma|instance|axiom|opaque|structure|inductive)\s+"
     r"(?:slot|LZ77)\.",
     "a submission may not declare into `slot.` or `LZ77.`"),
    (r"^\s*axiom\s", "a submission may not introduce axioms; stage 5 would reject it anyway"),
]

#: Submitted files larger than this are rejected before anything is run.
MAX_FILE_BYTES = 512 * 1024

#: Wall-clock budgets, in seconds. A submission's `Parse.lean` is half a megabyte
#: of arbitrary tactic script, so **stage 4 is the one stage a miner can make
#: cost whatever they like**: `set_option maxHeartbeats 0`, a `simp` over a
#: generated term, `decide` on something large. Lean's own `maxHeartbeats` is not
#: the control here, because the submission can raise it from inside the file.
#: A wall clock outside the process can't be argued with.
#:
#: Generous against the reference submissions, which elaborate in well under a
#: minute; the budget is here to bound a hostile or accidental hang, not to make
#: proving a race. Override for a slow validator with
#: `VERIFY_TIMEOUT_STATEMENT=1800`.
TIMEOUTS = {
    "extract": int(os.environ.get("VERIFY_TIMEOUT_EXTRACT", 600)),
    "statement": int(os.environ.get("VERIFY_TIMEOUT_STATEMENT", 900)),
    "score": int(os.environ.get("VERIFY_TIMEOUT_SCORE", 1800)),
}


def sha(p: Path) -> str:
    return hashlib.sha256(p.read_bytes()).hexdigest()


def fail(stage: str, msg: str) -> None:
    print(f"\nREJECTED at stage {stage}\n  {msg}")
    sys.exit(1)


def misconfigured(msg: str) -> None:
    print(f"\nVALIDATOR ERROR\n  {msg}")
    sys.exit(2)


class Timeout(Exception):
    """A stage exceeded its wall-clock budget."""

    def __init__(self, seconds, output=""):
        super().__init__(f"exceeded {seconds}s")
        self.seconds = seconds
        self.output = output


def run(cmd, timeout=None, **kw):
    """Run `cmd` with the toolchain environment, optionally under a wall clock.

    `start_new_session` puts the child in its own process group so that a
    timeout kills *lake and every worker it spawned*, not just the shell in
    front of them. Without that, a submission whose elaboration hangs leaves
    `lean` processes pinning cores after the verifier has moved on.
    """
    env = dict(os.environ)
    cfg = subprocess.run(
        ["bash", "-c", f'. "{ROOT}/verifier/config.sh" && env'],
        capture_output=True, text=True,
    )
    for line in cfg.stdout.splitlines():
        if "=" in line:
            k, v = line.split("=", 1)
            env[k] = v
    if timeout is None:
        return subprocess.run(cmd, env=env, capture_output=True, text=True, **kw)

    proc = subprocess.Popen(
        cmd, env=env, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
        text=True, start_new_session=True, **kw
    )
    try:
        out, err = proc.communicate(timeout=timeout)
    except subprocess.TimeoutExpired:
        try:
            os.killpg(os.getpgid(proc.pid), signal.SIGKILL)
        except (ProcessLookupError, PermissionError):
            proc.kill()
        out, err = proc.communicate()
        raise Timeout(timeout, (out or "") + (err or ""))
    return subprocess.CompletedProcess(cmd, proc.returncode, out, err)


# ---------------------------------------------------------------------------


def stage_intake(sub: Path) -> None:
    """Copy the submission in. Not a numbered stage: it is the precondition."""
    if not sub.is_dir():
        misconfigured(f"{sub} is not a directory")
    for name, dest in SUBMISSION_FILES.items():
        src = sub / name
        if not src.is_file():
            fail("0 (intake)", f"the submission has no {name}")
        if src.stat().st_size > MAX_FILE_BYTES:
            fail("0 (intake)", f"{name} is {src.stat().st_size} bytes; limit is {MAX_FILE_BYTES}")
    extra = sorted(
        p.name for p in sub.iterdir()
        if p.name not in SUBMISSION_FILES and not p.name.startswith(".")
        and p.suffix in {".rs", ".lean"}
    )
    if extra:
        fail("0 (intake)", f"a submission is two files; found also: {', '.join(extra)}")
    for name, dest in SUBMISSION_FILES.items():
        shutil.copyfile(sub / name, ROOT / dest)
    print(f"0 intake      ok — {sub.name}: parse.rs, Parse.lean")


def stage_policy() -> None:
    src = (ROOT / "slot/src/parse.rs").read_text()
    # Strip comments, so a rule *named* in a doc comment is not a violation.
    stripped = re.sub(r"//[^\n]*", "", src)
    stripped = re.sub(r"/\*.*?\*/", "", stripped, flags=re.S)
    bad = []
    for pattern, why in POLICY:
        for m in re.finditer(pattern, stripped):
            line = stripped[: m.start()].count("\n") + 1
            bad.append(f"parse.rs line ~{line}: {m.group(0)!r} — {why}")

    # And the proof, for the one thing a proof must not do: declare the names it
    # is supposed to be reasoning about.
    proof = (ROOT / "lean/Proof/Parse.lean").read_text()
    proof = re.sub(r"--[^\n]*", "", proof)
    proof = re.sub(r"/-.*?-/", "", proof, flags=re.S)
    for pattern, why in PROOF_POLICY:
        for m in re.finditer(pattern, proof, flags=re.M):
            line = proof[: m.start()].count("\n") + 1
            bad.append(f"Parse.lean line ~{line}: {m.group(0).strip()!r} — {why}")

    if bad:
        fail("1 (policy)", "\n  ".join(bad))
    print("1 policy      ok — the submitted Rust is inside the subset, "
          "the proof declares nothing it should be proving about")


def stage_pins(rewrite: bool) -> None:
    pins_file = ROOT / "verifier/PINS.json"
    current = {p: sha(ROOT / p) for p in PINNED if (ROOT / p).exists()}
    if rewrite:
        pins_file.write_text(json.dumps(current, indent=2, sort_keys=True) + "\n")
        print(f"wrote {pins_file.relative_to(ROOT)} ({len(current)} files)")
        return
    if not pins_file.exists():
        misconfigured("verifier/PINS.json is missing; run `verify.py --pin`")
    pinned = json.loads(pins_file.read_text())
    changed = sorted(p for p in pinned if current.get(p) != pinned[p])
    if changed:
        fail(
            "2 (pins)",
            "the contract or the harness has been modified:\n  "
            + "\n  ".join(changed)
            + "\n  A submission supplies only parse.rs and Parse.lean.",
        )
    print(f"2 pins        ok — {len(pinned)} contract and harness files unchanged")


def stage_extract() -> None:
    try:
        r = run([str(ROOT / "verifier/extract.sh")], timeout=TIMEOUTS["extract"])
    except Timeout as t:
        fail("3 (extract)", f"charon+aeneas did not finish within {t.seconds}s")
    if r.returncode == 2:
        misconfigured((r.stderr or r.stdout).strip()[:2000])
    if r.returncode != 0:
        fail("3 (extract)", (r.stderr or r.stdout).strip()[:2000])
    print("3 extract     ok — charon+aeneas re-run by the verifier, no new axioms")


#: Stage 4 may need to build twice -- a cached build does not re-emit the axiom
#: report, so `stage_axioms` touches the gate and rebuilds. The budget is spent
#: *across* those calls rather than granted afresh to each, so the stage as a
#: whole is bounded by `TIMEOUTS["statement"]` and not by a multiple of it.
_statement_spent = 0.0


def stage_build() -> str:
    global _statement_spent
    left = TIMEOUTS["statement"] - _statement_spent
    t0 = time.monotonic()
    try:
        if left <= 0:
            raise Timeout(TIMEOUTS["statement"])
        r = run(["lake", "build", "Verify"], cwd=LEAN, timeout=left)
    except Timeout as t:
        fail(
            "4 (statement)",
            f"the proof did not elaborate within {TIMEOUTS['statement']}s.\n"
            "  A submission controls how long its own tactic script takes, so this\n"
            "  budget is a gate and not a hint: reduce the proof's cost rather than\n"
            "  asking for more time. Raise VERIFY_TIMEOUT_STATEMENT only if the\n"
            "  *reference* submissions do not fit either, which means the validator\n"
            "  is underpowered rather than the submission being slow.",
        )
    finally:
        _statement_spent += time.monotonic() - t0
    out = r.stdout + r.stderr
    if r.returncode != 0:
        if "unknown package" in out or "no such file" in out.lower():
            misconfigured(out.strip()[-2000:])
        errs = [l for l in out.splitlines() if l.startswith("error")]
        fail("4 (statement)", "\n  ".join(errs[:20]) or out.strip()[-2000:])
    print("4 statement   ok — `LZ77.Obligation slot.parse` typechecks")
    return out


def stage_axioms(build_output: str) -> None:
    def axiom_line(text):
        return next(
            (l for l in text.splitlines() if "'accepted' depends on axioms" in l), None
        )

    line = axiom_line(build_output)
    if line is None:
        # A cached build does not re-emit the message; force it.
        (LEAN / "Verify/Obligation.lean").touch()
        line = axiom_line(stage_build())
    if line is None:
        misconfigured("no axiom report was produced by Verify/Obligation.lean")
    names = set(re.findall(r"[A-Za-z_][A-Za-z_0-9.]*", line.split("[", 1)[1]))
    extra = names - ALLOWED_AXIOMS
    if extra:
        fail("5 (axioms)", f"the proof rests on {sorted(extra)}")
    print(f"5 axioms      ok — {sorted(ALLOWED_AXIOMS)}")


def stage_score() -> int:
    for crate in ("slot", "harness"):
        try:
            r = run(
                ["cargo", "build", "--release", "-q"],
                cwd=ROOT / crate, timeout=TIMEOUTS["score"],
            )
        except Timeout as t:
            fail("6 (score)", f"{crate} did not build within {t.seconds}s")
        if r.returncode != 0:
            fail("6 (score)", f"{crate} does not build:\n{r.stderr[-2000:]}")
    corpus = ROOT / "corpus"
    if not corpus.exists() or not any(corpus.iterdir()):
        misconfigured("corpus is empty; run `verifier/make-corpus.py`")
    try:
        r = run(
            [str(ROOT / "harness/target/release/harness"), str(corpus)],
            timeout=TIMEOUTS["score"],
        )
    except Timeout as t:
        fail(
            "6 (score)",
            f"scoring did not finish within {t.seconds}s. The parse has its own "
            "budget\n  inside the harness (ms per MiB); this is the backstop for "
            "everything else.",
        )
    print("6 score       running…\n")
    print(r.stdout.rstrip())
    if r.returncode != 0:
        print(r.stderr.rstrip())
    return r.returncode


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("submission", nargs="?", help="directory with parse.rs and Parse.lean")
    ap.add_argument("--pin", action="store_true", help="re-pin the contract and harness")
    ap.add_argument("--no-score", action="store_true", help="stop after the proof gate")
    args = ap.parse_args()

    if args.pin:
        stage_pins(rewrite=True)
        return
    if not args.submission:
        ap.error("a submission directory is required (or --pin)")

    print(f"verifying {args.submission}\n")
    stage_intake(Path(args.submission).resolve())
    stage_policy()
    stage_pins(rewrite=False)
    stage_extract()
    out = stage_build()
    stage_axioms(out)
    if args.no_score:
        print("\nproof accepted (scoring skipped)")
        return
    sys.exit(stage_score())


if __name__ == "__main__":
    main()
