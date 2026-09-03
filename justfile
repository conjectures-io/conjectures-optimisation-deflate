# conjectures-rust-competition — one entry point for both sides.
#
# Toolchain paths come from validator/verifier/config.sh and can all be
# overridden from the environment. See validator/docs/TOOLCHAIN.md.

root := justfile_directory()
val  := root / "validator"

default:
    @just --list

# --- Setup ------------------------------------------------------------------

# First-time setup: Lean toolchain, dependencies, and build the contract.
setup:
    {{val}}/verifier/setup.sh

# Build the scoring corpus. Pass source roots to override the defaults.
corpus *ROOTS:
    python3 {{val}}/verifier/make-corpus.py {{ROOTS}}

# Build both crates. Needed before `corpus`, which takes its binary part from
# the release output.
build:
    cd {{val}}/slot && cargo build --release -q
    cd {{val}}/harness && cargo build --release -q

# --- Submissions ------------------------------------------------------------

# The full gate, then the score. This is what a validator runs.
#   just check miner/template
check DIR *ARGS:
    python3 {{val}}/verifier/verify.py {{root}}/{{DIR}} {{ARGS}}

# The proof gate alone -- intake, policy, pins, extraction, statement, axioms.
check-proof DIR:
    python3 {{val}}/verifier/verify.py {{root}}/{{DIR}} --no-score

# Ratio only, no proof. Cheap. What a miner runs while tuning a parser.
# A validator never runs this.
score DIR:
    #!/usr/bin/env bash
    set -euo pipefail
    cp {{root}}/{{DIR}}/parse.rs {{val}}/slot/src/parse.rs
    cd {{val}}/slot && cargo build --release -q
    cd {{val}}/harness && cargo build --release -q
    ./target/release/harness {{val}}/corpus

# Translate a submission's Rust into Lean, and stop. For seeing what your proof
# will be about before writing it.
extract DIR:
    #!/usr/bin/env bash
    set -euo pipefail
    cp {{root}}/{{DIR}}/parse.rs {{val}}/slot/src/parse.rs
    {{val}}/verifier/extract.sh
    echo
    echo "read {{val}}/lean/Slot/Funs.lean -- that is what the proof is about"

# Build the Lean side of a submission: contract, extracted slot, proof, gate.
prove DIR:
    #!/usr/bin/env bash
    set -euo pipefail
    . {{val}}/verifier/config.sh
    cp {{root}}/{{DIR}}/parse.rs {{val}}/slot/src/parse.rs
    cp {{root}}/{{DIR}}/Parse.lean {{val}}/lean/Proof/Parse.lean
    {{val}}/verifier/extract.sh
    cd {{val}}/lean && lake build

# --- Operator ---------------------------------------------------------------

# Re-pin the contract and harness. Run after any operator-side change.
repin:
    python3 {{val}}/verifier/verify.py --pin

# What a submission costs, in lines.
cost DIR:
    #!/usr/bin/env bash
    set -euo pipefail
    python3 - <<EOF
    from pathlib import Path
    def code(f):
        n, blk = 0, False
        for l in Path(f).read_text().split("\n"):
            t = l.strip()
            if not t: continue
            if blk:
                if "-/" in t or "*/" in t: blk = False
                continue
            if t.startswith("/-") or t.startswith("/*"):
                if "-/" not in t and "*/" not in t: blk = True
                continue
            if t.startswith("--") or t.startswith("//"): continue
            n += 1
        return n
    d = Path("{{root}}/{{DIR}}")
    v = Path("{{val}}")
    print(f"{'the slot, in Rust':34} {code(d/'parse.rs'):5} lines")
    print(f"{'the proof -- PER PATCH':34} {code(d/'Parse.lean'):5} lines")
    print()
    for label, f in [("contract: Spec.lean", "lean/Lz77/Spec.lean"),
                     ("contract: Lemmas.lean", "lean/Lz77/Lemmas.lean"),
                     ("contract: Interface.lean", "lean/Lz77/Interface.lean"),
                     ("the gate: Obligation.lean", "lean/Verify/Obligation.lean")]:
        print(f"{label + '  -- paid ONCE':34} {code(v/f):5} lines")
    EOF

# Both reference submissions, end to end. The repository's own smoke test.
smoke: build
    just check miner/template
    just check miner/examples/hash-chains
