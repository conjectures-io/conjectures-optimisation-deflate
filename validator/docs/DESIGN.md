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

### 4. The seam is not exhausted

libdeflate reaches 1,487,126 bytes on this corpus: **19.7% under the incumbent and
10.0% under the accepted submission**, and the gap is algorithmic — lazy matching,
better block splitting, near-optimal parsing — all of it inside the provable
subset, because *SIMD cannot improve compression ratio*. Vectorisation makes the
same decisions faster; it never changes which match is chosen.

## The gate

Six stages, and the order is the design. **Nothing is compiled for speed and
nothing is timed until the proof has been accepted**, so a submission cannot buy
validator time with a program that has no proof.

| stage | what it does | what it stops |
|---|---|---|
| 1 policy | scans the submitted Rust | code outside the translated subset |
| 2 pins | hashes 18 contract and harness files | editing the contract you are judged against |
| 3 extract | **the verifier re-runs charon+aeneas itself** | an extraction that is a claim by the claimant |
| 4 statement | `LZ77.Obligation slot.parse` typechecks | a weakened theorem |
| 5 axioms | `#print axioms accepted` | `sorryAx` — Aeneas's own library contains `sorry` |
| 6 score | round-trip, bytes, speed floor | everything else |

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
* **Block splitting is in the harness**, so it is identical for everyone. It is
  worth ratio and it is a natural second slot.
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

**The speed floor is a guess.** 8x the incumbent, and the accepted submission used
2.4x of it. If a later submission is a near-optimal parser it will want much more,
and raising the floor eventually puts SIMD back on the critical path, at which
point the target dies. The constant is load-bearing in both directions and it has
not been calibrated against a real frontier.

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

## Reproducing

```bash
just build                                   # the crates
just corpus                                  # the scoring corpus
just smoke                                   # both reference submissions, end to end
just check miner/examples/hash-chains        # the whole gate, then the score
just check-proof miner/examples/hash-chains  # the proof gate alone
just score miner/examples/hash-chains        # ratio only (what a miner runs)
just cost miner/examples/hash-chains         # what a submission costs, in lines
```
