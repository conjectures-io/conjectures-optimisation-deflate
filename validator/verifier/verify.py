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
    6  score       only now: build, round-trip, compressed bytes, speed floor

Exit codes: 0 accepted, 1 rejected, 2 the validator itself is misconfigured.
"""

import argparse
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
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

#: Submitted files larger than this are rejected before anything is run.
MAX_FILE_BYTES = 512 * 1024


def sha(p: Path) -> str:
    return hashlib.sha256(p.read_bytes()).hexdigest()


def fail(stage: str, msg: str) -> None:
    print(f"\nREJECTED at stage {stage}\n  {msg}")
    sys.exit(1)


def misconfigured(msg: str) -> None:
    print(f"\nVALIDATOR ERROR\n  {msg}")
    sys.exit(2)


def run(cmd, **kw):
    env = dict(os.environ)
    cfg = subprocess.run(
        ["bash", "-c", f'. "{ROOT}/verifier/config.sh" && env'],
        capture_output=True, text=True,
    )
    for line in cfg.stdout.splitlines():
        if "=" in line:
            k, v = line.split("=", 1)
            env[k] = v
    return subprocess.run(cmd, env=env, capture_output=True, text=True, **kw)


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
            bad.append(f"line ~{line}: {m.group(0)!r} — {why}")
    if bad:
        fail("1 (policy)", "\n  ".join(bad))
    print("1 policy      ok — the submitted Rust is inside the subset")


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
    r = run([str(ROOT / "verifier/extract.sh")])
    if r.returncode == 2:
        misconfigured((r.stderr or r.stdout).strip()[:2000])
    if r.returncode != 0:
        fail("3 (extract)", (r.stderr or r.stdout).strip()[:2000])
    print("3 extract     ok — charon+aeneas re-run by the verifier, no new axioms")


def stage_build() -> str:
    r = run(["lake", "build", "Verify"], cwd=LEAN)
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
        r = run(["cargo", "build", "--release", "-q"], cwd=ROOT / crate)
        if r.returncode != 0:
            fail("6 (score)", f"{crate} does not build:\n{r.stderr[-2000:]}")
    corpus = ROOT / "corpus"
    if not corpus.exists() or not any(corpus.iterdir()):
        misconfigured("corpus is empty; run `verifier/make-corpus.py`")
    r = run([str(ROOT / "harness/target/release/harness"), str(corpus)])
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
