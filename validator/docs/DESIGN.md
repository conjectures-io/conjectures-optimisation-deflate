# Design

**Reproduce:** `just smoke`.

Why the slot, the metric and the gate are what they are. The target was chosen by
measurement in [`../../../conjectures-research`](../../../conjectures-research) —
what Aeneas can translate, what a proof costs, and where the compression headroom
actually is — and four confident claims were overturned along the way. This
document is the design that came out of it, with the numbers that justify each
decision.

The numbers below are from the research repository's corpus (5.0 MB). This
repository's corpus is larger (8.1 MB) and the verdicts are the same; run
`just smoke` for current figures.

## What exists

```
   slot/src/parse.rs                 the miner's Rust — the whole LZ77 parsing stage
        │
        ├── charon + aeneas ────────► lean/Slot/{Types,Funs}.lean   (verifier re-runs this)
        │                                    │
        │                             lean/Proof/Parse.lean         the miner's proof
        │                                    │
        │                             lean/Lz77/*.lean              the contract, paid once
        │                                    │
        │                             lean/Verify/Obligation.lean   the gate (3 lines)
        │
        └── cargo ──► tokens ──► harness/src/deflate.rs ──► DEFLATE bytes
                                        │
                miniz_oxide + zlib ◄────┘        round-trip check
                                        │
                                   compressed bytes, vs the incumbent

   harness/src/reference.rs          unconstrained parsers, scored through the
   harness/src/headroom.rs           SAME encoder -- `just headroom` uses these to
                                     measure how much of the gap to libdeflate is
                                     reachable through the slot at all
```

## The result

One submission, taken all the way through:

```
1 policy      ok — the submitted Rust is inside the subset
2 pins        ok — 18 contract and harness files unchanged
3 extract     ok — charon+aeneas re-run by the verifier, no new axioms
4 statement   ok — `LZ77.Obligation slot.parse` typechecks
5 axioms      ok — ['Classical.choice', 'Quot.sound', 'propext']
6 score       running…

file                              raw   incumbent  submission    delta
binary.bin                    2000000      888358      833460   0.938x
json.txt                      1000000      195680      164110   0.839x
lean.txt                       152156       51733       43123   0.834x
prose.md.txt                   783633      349993      294431   0.841x
source.rs.txt                 1067137      367034      317953   0.866x
TOTAL                         5002926     1852798     1653077

  miniz_oxide level 1          2011928
  miniz_oxide level 9          1583615
  libdeflate level 12          1487126   <- the state of the art

score      0.89221x   parse time 2.43x   ACCEPTED — 10.779% smaller
```

## The four things this settles

### 1. The slot is not a sliver

The unit a miner replaces is the **entire LZ77 parsing stage** — 90 to 156 lines
of Rust containing the hash function, the match verifier, the chain walk, the
greedy decision and the emission. It translates through Charon and Aeneas with
**zero hand-written axioms**.

the research repository's `docs/EXP2_REAL_CODE.md` found that `miniz_oxide` itself does not extract. That does
not matter, because a miner *replaces* `find_match` rather than proving the
incumbent's version — the realisation that rescues the design, now demonstrated
rather than argued.

### 2. Correctness is independent of the search

This is the design decision that makes the economics work, and it is worth stating
precisely.

`hash3_spec` proves that the hash lands in `0..32768` and says nothing about what
it computes. `parse_loop0_loop0_spec` — the loop that maintains the chains — has
the postcondition `True`. Between the search and the emission sits one predicate:

```lean
def Found (input : Slice Std.U8) (n pos best_len best_dist : Std.Usize) : Prop :=
  best_len.val < 3 ∨
    (3 ≤ best_len.val ∧ best_len.val ≤ 258 ∧ pos.val + best_len.val ≤ n.val ∧
      1 ≤ best_dist.val ∧ best_dist.val ≤ 32768 ∧ best_dist.val ≤ pos.val ∧
      Matches input (pos.val - best_dist.val) pos.val best_len.val)
```

A submission may compute its matches with a suffix automaton, a binary tree, or a
full optimal-parse dynamic program. It rewrites `find_match_spec` and nothing
else. Nothing in the proof says the hash chain is acyclic, or that `prev` points
anywhere sensible, or that the match found is the best available — only that the
bytes were compared.

### 3. The marginal cost of a real improvement is about 30 lines

| | lines |
|---|---|
| the slot, in Rust | 90 → 156 |
| extracted model (generated) | 190 → 241 |
| the contract, its lemmas and interface — **paid once** | 131 |
| the gate — **paid once** | 4 |
| **the proof — paid per patch** | **231 → 263** |

The submission moved from a single-slot hash head to 16-deep hash chains, won
10.8% on ratio, and its proof grew by **32 lines**. Against
the research repository's `docs/EXP3_PERMUTATION.md`'s 449 lines for a radix sort, a whole parser at 263 is the
result that decides the economics, and it comes from two deliberate choices:

* **The contract was designed for the proof.** `copyN` describes a back-reference
  as the accumulator extended one byte at a time, so `copyN_take` reduces the
  whole obligation to `∀ k < len, input[pos-dist+k] = input[pos+k]` — exactly what
  a match-length loop already computes. A miner never mentions `copyN`. This is
  EXP3's "shape of the contract" lever applied on purpose; it was worth more than
  any tactic.
* **`Found` is a firewall.** The search's cost does not propagate into the
  emission's proof.

**The regime this was demonstrated in, stated plainly.** Hash head to hash chains
is a change to the **search structure**, and search structure is exactly what
`Found` was built to make cheap. The claim is real there and it is not yet tested
anywhere else. The remaining headroom is mostly *not* there: it is in the
**decision** — lazy matching, and a shortest-path parse over the whole block.
Lazy matching keeps the loop's shape (one token per iteration, `pos` monotone) and
should cost a case rather than a section. A shortest-path parse does not keep that
shape: it costs a whole block and *then* emits, so emission becomes a second pass
over a decision array.

The reason to expect the cost to stay bounded is that the firewall extends: if the
emission pass re-verifies each match with `match_len` before emitting it, exactly
as the greedy loop does now, then the dynamic program sits where the hash chain
sits today — free to be arbitrarily wrong, because nothing downstream believes it.
`find_match_spec` is replaced by a lemma of the same shape over the array.

Expected, not measured. Until a submission pays for it, "about thirty lines" is a
claim about search structure and [`ROADMAP.md`](ROADMAP.md) is where it is tracked.

### 4. The seam is not exhausted, and 80% of it is in the slot

`libdeflate` is some way under the best accepted submission, and the tempting
reading of that gap is "this is what is left to win". That reading is wrong,
because the gap has three components and a miner can only reach one of them: the
parse is the slot, while block splitting and the entropy coder are in the trusted
harness and identical for everyone.

`just headroom` measures the split rather than arguing about it. The reference
parsers in `harness/src/reference.rs` emit the competition's own token encoding
and are scored through the *same* `deflate::encode`, so whatever they reach is
reachable through the slot by construction — it is a parse and nothing else
changed. On this repository's 8.1 MB corpus:

| | bytes | of the gap | in the slot? |
|---|---|---|---|
| a better **parse** | 180,026 | **79.6%** | **yes** |
| **block splitting** | 4,381 | 1.9% | no |
| **entropy coder** + residual | 41,618 | 18.4% | no |

So the headline was directionally right and quantitatively loose. Two things fall
out of the measurement that argument did not produce:

* **Block splitting is not worth a second slot.** The best *fixed* block size per
  file beats the harness's 16,384 tokens by 4,381 bytes — 0.17% of the incumbent.
  A content-aware splitter beats the best fixed size, so that is a lower bound,
  but on something that looked like a percent. "A natural second slot", below, is
  wrong about the size of the prize.
* **The cheapest rung is not a new idea.** Plain greedy at depth 256 — the
  incumbent's own algorithm with the proof-friendliness constraints lifted —
  already beats the accepted submission by 2.4%, and lazy matching alone gets
  under `miniz_oxide` level 9.

[`ROADMAP.md`](ROADMAP.md) has the full ladder and the ordering.

## The gate

Six stages, and the order is the design. **Nothing is compiled for speed and
nothing is timed until the proof has been accepted**, so a submission cannot buy
validator time with a program that has no proof.

| stage | what it does | what it stops |
|---|---|---|
| 1 policy | scans the submitted Rust, and the proof for redeclarations | code outside the translated subset |
| 2 pins | hashes 18 contract and harness files | editing the contract you are judged against |
| 3 extract | **the verifier re-runs charon+aeneas itself** | an extraction that is a claim by the claimant |
| 4 statement | `LZ77.Obligation slot.parse` typechecks | a weakened theorem |
| 5 axioms | `#print axioms accepted` | `sorryAx` — Aeneas's own library contains `sorry` |
| 6 score | round-trip, bytes, time budget | everything else |

Stage 4 is v1's statement check done as a **type check** rather than a string
comparison, and that is the only version of it that cannot be gamed. The
verifier — not the miner — writes:

```lean
theorem accepted : LZ77.Obligation slot.parse :=
  fun input out h => Submission.parse_spec input out h
```

If the miner proved something weaker, this does not compile. Checked negatively:
substituting a proof of `⦃ fun _ => True ⦄` produces

```
Type mismatch: weak input out h has type
  slot.parse input out ⦃ x => True ⦄
but is expected to have type
  slot.parse input out ⦃ r => ↑r.1 ≤ input.length ∧ r.2.length = out.length ∧
                              LZ77.Valid (LZ77.bytes input) (LZ77.toks r.2 ↑r.1) ⦄
```

Stage 1 checked the same way: inserting `'outer: while` is rejected with
`line ~90: "'outer: while" — labelled loops`.

## Why the proof is load-bearing rather than decorative

A compressor that emits a stream which does not decode back is a silent,
catastrophic and *delayed* failure. Fuzzing finds most of the ways to get there;
`decode(parse(x)) = x` finds all of them. The harness still runs a differential
round-trip check against two independent inflaters — `miniz_oxide` and the system
zlib — because the harness must stay sound even if the contract has a bug, and a
disagreement between an accepted proof and the differential check is evidence
about the *contract*, which is exactly the failure worth catching loudly.

## What is deliberately out of scope

* **The entropy coder is trusted, not proved.** Huffman coding is a bijection the
  harness implements once and no miner touches, so nothing about it is in the
  obligation. Extending the competition to that layer means a second slot with its
  own contract.
* **Block splitting is in the harness**, so it is identical for everyone. It was
  described here as "a natural second slot"; `just headroom` prices it at 4,381
  bytes, or 0.17% of the incumbent, and it is now the *lowest* priority in
  [`ROADMAP.md`](ROADMAP.md). The entropy coder, at 41,618 bytes, is the second
  slot worth building.
* **`inflate` is not modelled.** The obligation is stated against `LZ77.decode`,
  the LZ77 layer of RFC 1951 with the Huffman coding stripped off. That is
  the research repository's `docs/RECOMMENDATION.md`'s own mitigation — *"ship the LZ77-layer property as a
  complete smaller gate first"* — and the reason it works is that the harness owns
  the entropy layer. A complete small theorem beats an incomplete large one.
* **The corpus is reproducible rather than held out**, so that the numbers here
  can be checked. A real round commit-reveals it and publishes shape statistics
  only.
* **Stability is not decided.** The score is a ratio, so a different-but-valid
  parse is fine. A bit-exact score would need the slot definition to say so.

## Honest risks

**The time budget was the wrong shape, and is now merely a guess.** It used to be
8x the incumbent's wall clock. A *relative* budget ratchets: promote a fast
submission and it becomes 8x a smaller number, so every promotion tightens the
gate against the slow near-optimal parsers that hold 80% of the remaining prize.
Measured, the frontier is ~400x the incumbent — the old floor would have rejected
it without looking at its bytes.

It is now **absolute**: 8000 ms per MiB of corpus, about 4x the reference
shortest-path parse. That removes the ratchet and bounds a validator's cost
directly. It does not remove the underlying trade-off: too loose and the
competition pays for compute rather than for algorithms. It is calibrated against
a frontier now (`just headroom`) rather than against `miniz_oxide`'s level-9 time,
which is an improvement and not a proof that 8000 is right.

One argument in the old framing was simply wrong and is worth retiring: a loose
budget does *not* put SIMD back on the critical path. The score is bytes, and
vectorisation never changes which match is chosen, so SIMD has nothing to win here
at any budget.

**The incumbent is weak.** It is a single-slot hash head — roughly level-1
quality. Early submissions will win easily, which is good for demonstrating that
the pipeline registers wins and bad as a measure of how hard the competition is.
The bar moves each time a submission is promoted.

**The trusted base includes Aeneas.** Its Lean library contains `sorry`, Charon
must be rebuilt against a pinned Aeneas, and the pair drifts. Stage 5 is what
stands between that and an unsound acceptance, and it is not optional.

**Two implementations of the token encoding.** `token.rs` and `LZ77.emit` are the
same function written twice, once to run and once to reason about. Keeping them in
step is a real obligation of the operator; the correspondence is tabulated in
`../harness/src/token.rs` and the arithmetic half is checked exhaustively by a test
over every legal `(dist, len)`.

**The marginal-cost claim is demonstrated in one regime only.** "About thirty proof
lines per improvement" is measured for a change to the *search*, which is what the
`Found` firewall was designed to make cheap, and the bulk of the remaining headroom
is in the *decision* instead. See claim 3 above and
[`ROADMAP.md`](ROADMAP.md#the-question-the-current-design-has-not-answered).

**The seam is finite and its size is now known.** 180,026 bytes are reachable
through this slot — roughly 8% against the current incumbent, and perhaps three to
five promotions' worth before the parse is exhausted. After that the competition
needs a second slot with its own contract, and only one of the candidates is worth
the work. [`ROADMAP.md`](ROADMAP.md) is that plan; without it this is a
demonstration with a shelf life rather than a mechanism.

**Miner supply is the binding constraint, not the mechanism.** A submission needs
restricted index-based Rust, Charon and Aeneas, Lean 4 with Mathlib and Aeneas
tactics, *and* enough DEFLATE to beat a hash-chain parser. That intersection is
small. What the repository can do about it, it does — a template that passes,
[`../../miner/RULES.md`](../../miner/RULES.md) written from real failures rather
than from a manual, and an idempotent `just init` — and what it cannot do about it
is create the population.

## Reproducing

```bash
just build                                   # the crates
just corpus                                  # the scoring corpus
just smoke                                   # both reference submissions, end to end
just check miner/examples/hash-chains        # the whole gate, then the score
just check-proof miner/examples/hash-chains  # the proof gate alone
just score miner/examples/hash-chains        # ratio only (what a miner runs)
just cost miner/examples/hash-chains         # what a submission costs, in lines
just headroom                                # where the gap to libdeflate is (slow)
```
