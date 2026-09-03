# conjectures-rust-competition

A competition in which miners submit **Rust**, a **Lean proof** gates it, and
accepted submissions are scored against a baseline by a fixed test harness.

The task is DEFLATE compression: you write the LZ77 parser, you prove that the
token stream it produces decodes back to the input, and you are scored on total
compressed bytes over a held-out corpus. Lower wins.

```
   your parse.rs  ──charon+aeneas──►  Lean  ──your Parse.lean──►  proof
        │                                                            │
        │                          the gate: LZ77.Obligation slot.parse
        │                                                            │
        └──cargo──► tokens ──► trusted DEFLATE encoder ──► bytes ◄───┘ accepted
                                                             │
                                        vs the incumbent, on the corpus
```

| | |
|---|---|
| **I want to submit** | [`miner/README.md`](miner/README.md) — step by step, with a template that already passes |
| **I run the competition** | [`validator/README.md`](validator/README.md) — the gate, the corpus, promotion |
| **Why it is built this way** | [`validator/docs/DESIGN.md`](validator/docs/DESIGN.md) |

## The two claims worth checking before you spend time

**The slot is not a sliver.** What you replace is the *entire LZ77 parsing stage*
— hash function, match verifier, candidate search, greedy decision, emission —
66 to 90 lines of Rust that Charon and Aeneas translate with **zero** hand-written
axioms. You are not tuning a constant.

**A real improvement costs about thirty proof lines.** The two submissions in
`miner/` differ by moving from a single-slot hash head to 16-deep hash chains.
That is worth **14.0%** on the corpus here, and its proof is **32 lines longer**:

| | `parse.rs` | `Parse.lean` | score |
|---|---|---|---|
| `miner/template` (hash head) | 66 | 204 | 1.000x — this is the incumbent |
| `miner/examples/hash-chains` | 90 | 236 | **0.860x** |

That ratio — a few dozen proof lines for a double-digit ratio win — is the whole
economic question, and it comes out of one design decision: **correctness does not
depend on the search.** The proof that the hash lands in range says nothing about
what the hash computes; the loop that maintains the chains has the postcondition
`True`. Only the bytes actually compared before a match is emitted are
load-bearing. Replace the search with a suffix automaton or a full optimal-parse
dynamic program and you rewrite one lemma.

## Is there anything left to win?

On the corpus in this repository:

| | bytes | vs incumbent |
|---|---|---|
| incumbent (`miner/template`) | 2,605,048 | — |
| accepted (`miner/examples/hash-chains`) | 2,239,367 | 0.860x |
| miniz_oxide level 9 | 2,126,479 | 0.816x |
| **libdeflate level 12** | **2,013,342** | **0.773x** |

libdeflate is 22.7% under the incumbent and 10.1% under the best accepted
submission, and that gap is **algorithmic** — lazy matching, better block
splitting, near-optimal parsing. All of it is inside the provable subset, because
SIMD cannot improve compression *ratio*: vectorisation makes the same decisions
faster, it never changes which match is chosen.

## Layout

```
miner/
  README.md              step by step: install, write, prove, submit
  RULES.md               prover-friendly Rust, with rejected/accepted pairs
  CONTRACT.md            what you must prove, and what you need not
  template/              a complete submission that passes. Start here.
  examples/hash-chains/  a real 14% improvement, with its proof and a diff

validator/
  README.md              running a round
  docs/DESIGN.md         why the slot, the metric and the gate are what they are
  docs/SCORING.md        the metric, the speed floor, corpus governance
  docs/THREAT_MODEL.md   what each stage of the gate stops
  docs/TOOLCHAIN.md      the pins, what `init` installs, and four traps
  docs/CORPUS.md         the reference corpus, with hashes
  lean/Lz77/             THE CONTRACT — written once, pinned, never by a miner
  lean/Verify/           THE GATE — three lines the verifier writes itself
  lean/Slot/             generated from the submission by the verifier
  lean/Proof/            where the submission's proof is placed
  slot/                  the crate root the submitted parse.rs becomes
  harness/               trusted DEFLATE encoder, round-trip check, scoring
  verifier/verify.py     the six-stage gate
  verifier/init.sh       installs Lean, Aeneas, Charon and Mathlib from nothing
```

## Quick start

```bash
just init                           # Lean, Aeneas, Charon, Mathlib, build, self-test
just smoke                          # both reference submissions, end to end
just check miner/template           # the gate, then the score, on one submission
```

`just init` starts from nothing and is idempotent: about 15 minutes and 9 GB on
a bare machine, seconds on one that already has the toolchain. `just doctor`
reports what is present without installing anything.
[`validator/docs/TOOLCHAIN.md`](validator/docs/TOOLCHAIN.md) has the pins and the
traps.

## Provenance

The target was chosen by measurement, not argument, in
[`../conjectures-research`](../conjectures-research): what Aeneas can translate,
what a proof costs, where the compression headroom actually is, and four claims
that measurement overturned. The mechanism — task commitment, pinned hashes, a
policy scanner, an axiom check, and the rule that nothing is timed until the proof
is accepted — comes from [`../conjectures-rust`](../conjectures-rust), whose own
target could not contain a win.
