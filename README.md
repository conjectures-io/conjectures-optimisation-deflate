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
load-bearing. Replace the search with a suffix automaton and you rewrite one lemma.

**Where that claim is measured and where it is expected.** Hash head to hash chains
is a change to the *search*, which is exactly what this design makes cheap. Most of
the headroom left is in the *decision* — lazy matching, and a shortest-path parse
over the whole block. Lazy matching keeps the loop's shape. A shortest-path parse
does not: it costs a block and then emits, so emission becomes a second pass over a
decision array, and keeping the cost bounded means keeping the firewall — have the
emission pass re-verify each match with `match_len` before emitting it, and the
dynamic program lands where the hash chain already is, free to be wrong because
nothing downstream believes it. That is expected to hold and nobody has paid for it
yet; it is the most valuable open question about the mechanism, and it is tracked in
[`validator/docs/ROADMAP.md`](validator/docs/ROADMAP.md).

## Is there anything left to win?

Yes: **180,026 bytes, or 8.0% against the current incumbent.** That is a measured
number, not an estimate — `just headroom` reprints it.

On the corpus in this repository:

| | bytes | vs incumbent |
|---|---|---|
| incumbent (`miner/template`) | 2,605,048 | 1.000x |
| accepted (`miner/examples/hash-chains`) | 2,239,367 | 0.860x |
| greedy, depth 256 — *the same algorithm, unconstrained* | 2,184,978 | 0.839x |
| miniz_oxide level 9 | 2,126,479 | 0.816x |
| lazy matching, depth 256 | 2,125,535 | 0.816x |
| **near-optimal shortest-path parse** | **2,059,341** | **0.791x** |
| libdeflate level 12 (whole compressor) | 2,013,342 | 0.773x |

The rows in the middle matter more than the last one. **libdeflate is not the
target, because two thirds of what separates it from the best submission is not
in the slot at all** — it is in the trusted harness, where no submission can
reach. The bolded row is the target: a parse, emitting the competition's own
tokens, through the competition's own encoder, so it is reachable by construction.

The 226,025 bytes between the best accepted submission and libdeflate split like
this:

| | bytes | of the gap | reachable in the slot? |
|---|---|---|---|
| a better **parse** | 180,026 | **79.6%** | **yes** |
| **block splitting** | 4,381 | 1.9% | no — harness |
| **entropy coder** + residual | 41,618 | 18.4% | no — harness |

Two things in that table were surprises. **Block splitting is nearly worthless
here** — 0.17% of the incumbent — so the "natural second slot" it was assumed to
be is the last thing worth building. And **the cheapest rung needs no new idea at
all**: plain greedy at depth 256 is the incumbent's own algorithm with the
proof-friendliness constraints lifted, and it already beats the accepted
submission by 2.4%.

None of this is threatened by SIMD, at any time budget, because the score is
*bytes*: vectorisation makes the same decisions faster, it never changes which
match is chosen.

[`validator/docs/ROADMAP.md`](validator/docs/ROADMAP.md) has the ladder, the
ordering, and what runs out when.

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
  docs/ROADMAP.md        what is left to win, measured, and in what order
  docs/SCORING.md        the metric, the time budget, corpus governance
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
just headroom                       # what is left to win, and how much is reachable
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
