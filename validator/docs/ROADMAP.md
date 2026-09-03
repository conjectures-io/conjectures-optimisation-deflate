# Roadmap

**Reproduce every number here:** `just headroom`.

The LZ77 slot has a finite prize and a foreseeable end. That is not a criticism of
it — a competition whose remaining headroom is measured is a better competition
than one whose headroom is asserted — but it means the question "what happens when
this seam runs out" needs an answer before it runs out rather than after.

## How much is left in the current slot

`just headroom` decomposes the gap between the best accepted submission and
`libdeflate` level 12 by *construction*: every reference parser in
`harness/src/reference.rs` emits the competition's own token encoding and is
scored through the same trusted `deflate::encode`, so whatever it reaches is
reachable through the slot — it is a parse, and nothing else changed.

On this repository's corpus:

| arm | bytes | vs incumbent | ms/MiB |
|---|---|---|---|
| incumbent (`baseline.rs`, single-slot hash head) | 2,605,048 | 1.000x | 4.8 |
| accepted submission (16-deep hash chains) | 2,239,367 | 0.860x | 11.9 |
| reference: greedy, depth 256 | 2,184,978 | 0.839x | 17.0 |
| reference: lazy matching, depth 256 | 2,125,535 | 0.816x | 34.7 |
| reference: near-optimal shortest-path parse | **2,059,341** | **0.791x** | 1950 |
| libdeflate level 12 (whole compressor) | 2,013,342 | 0.773x | — |

The 226,025-byte gap between the accepted submission and libdeflate splits:

| | bytes | of the gap | reachable in the LZ77 slot? |
|---|---|---|---|
| a better **parse** | 180,026 | **79.6%** | **yes** |
| **block splitting** | 4,381 | 1.9% | no |
| **entropy coder** + residual | 41,618 | 18.4% | no |

**Four things follow, and two of them were surprises.**

**1. The slot holds ~80% of the advertised gap.** A miner who proves a
shortest-path parse wins 8.0% against the current incumbent, and the parse that
does it is in this repository. The headline number was directionally right.

**2. It is not the whole gap, and the docs should never have implied it was.**
About a fifth of the distance to libdeflate is behind the trusted harness and no
submission to this slot can reach it. `just headroom` exists so that this stays a
measured number rather than a rhetorical one.

**3. Block splitting is not worth a second slot.** This is the surprise. The
harness cuts a block every 16,384 tokens, and pricing the *best fixed* block size
per file recovers only 4,381 bytes — 0.17% of the incumbent. A content-aware
splitter would beat the best fixed size, so this is a lower bound, but it is a
lower bound on something that started out looking like a percent or more. The
design note that called block splitting "a natural second slot" was wrong about
the size of the prize. Deprioritised.

**4. The ladder is a rung shorter than it looks.** Plain greedy at depth 256 —
the *same algorithm* as the incumbent with the proof-friendliness constraints
lifted — already beats the accepted submission by 2.4%, and lazy matching alone
gets under `miniz_oxide` level 9. Neither needs a new idea. That is the cheapest
remaining ground and it should be the first thing a new miner is pointed at.

## The order to open new slots in

Ranked by measured prize, not by how interesting the contract would be.

### 1. Finish the LZ77 slot (180,026 bytes, in hand)

No new contract, no new work for the operator. Three rungs, in increasing order of
proof cost:

* **Deeper chains.** Purely a constant. The current proof does not change at all —
  `parse_loop0_loop0_spec` has postcondition `True` and the probe counter is what
  gives termination, so the depth is a number in the Rust with no Lean consequence.
* **Lazy matching.** Emit a literal at `pos` when `pos+1` has a longer match. The
  emission stays one token per iteration and `pos` stays monotone, so the loop
  invariant keeps its shape; there is one more case in the decision.
* **A shortest-path parse.** The real prize and the real proof question — see
  below.

### 2. The entropy coder (41,618 bytes, needs a contract)

The bigger of the two unreachable rows. A second slot over `deflate.rs`'s Huffman
stage, with an obligation of the same shape as this one: the bit stream decodes
back to the token stream. The contract is a different kind of work from `LZ77.Valid`
— bit-level, and `RULES.md` rule 3 (`%` over `&`) is precisely the wrong advice for
code that packs bits — so it is a genuine second project rather than a variation
on this one.

### 3. Block splitting (4,381 bytes, measured, not worth it)

Kept on the list only so that the measurement is on the record. Revisit if the
corpus changes shape enough to move the number.

## The question the current design has not answered

**The "~30 proof lines per improvement" claim is demonstrated for changes to the
search, and untested for changes to the decision.**

The two reference submissions differ by moving from a single-slot hash head to
16-deep hash chains: +14.0% on ratio for +32 lines of proof. That is a *search
structure* change, and search structure is exactly what the `Found` firewall was
built to make cheap. The claim is real in that regime.

The 180,026 bytes still in the slot are mostly not in that regime:

* **Lazy matching** still fits. One token per iteration, `pos` still monotone,
  `Found` still a firewall. Expect the proof to grow by a case, not by a section.
* **A shortest-path parse does not fit as written.** It computes a cost array over
  the whole block and *then* emits, so emission becomes a second pass reading a
  decision array. The current invariant — "the tokens written so far decode to
  `input.take pos`" — survives that, but only if the emission pass does not have
  to trust the array it is reading.

  The way to keep it cheap is to keep the firewall: have the emission pass call
  `match_len` and re-verify the bytes of each match **before** emitting it, exactly
  as the greedy loop does now. Then the dynamic program is in the same position the
  hash chain is in today — it may be arbitrarily wrong without threatening
  soundness, because nothing downstream believes it. `Found` is still the only
  thing the emission needs, and `find_match_spec` is replaced by a lemma of the
  same shape over the decision array.

  If that works, the marginal cost stays in the tens of lines and the design's
  central claim extends to the decision layer. **Nobody has paid for it yet**, and
  until somebody does, the honest version of the claim is the one stated at the
  top of this section.

Whoever writes that submission settles the most important open question about this
mechanism. It is worth more than the bytes.

## Not on the roadmap

* **A held-out corpus** is a property of running a round, not of the design. See
  [`SCORING.md`](SCORING.md).
* **Raising the time budget past the near-optimal parse.** It is already ~4x that
  parse ([`SCORING.md`](SCORING.md)). Past this point the competition starts paying
  for compute rather than for algorithms.
* **Collusion and Sybil resistance**, which are subnet-level and not addressed
  anywhere in this repository.
