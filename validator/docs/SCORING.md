# Scoring

## The metric

**Total compressed bytes over the corpus. Lower wins.**

It is an exact integer. Two validators on different hardware compute the *same*
number, which deletes the pinned CPU governor, the isolated cores, the variance
gate, the trimmed median, the interleaved arms, and — the one that actually
matters for a decentralised subnet — the possibility of two honest validators
disagreeing.

This is not a small convenience. The predecessor competition scored on wall clock,
had a ±10% noise floor against a 2% reward bar, and once had two arms running
*identical* work report 1.120x. Roughly half its harness complexity and all of its
scoring fragility existed to fight that noise. None of it is here.

## The time budget

A submission is rejected if its parse exceeds **8000 ms per MiB of corpus**.

Wall clock re-enters only as a **coarse gate**, where ±10% noise is harmless, and
never as the score. It exists because without it the degenerate submission is
zopfli: spend unbounded time to shave a fraction of a percent.

### Why it is absolute and not a multiple of the incumbent

It used to be *8x the incumbent's* time. That is the wrong shape, and not by a
little:

**A relative floor ratchets.** Promote a fast submission and the budget becomes 8x
a smaller number. Every promotion tightens the gate — so the competition grows
progressively more hostile to precisely the slow, near-optimal parsers that hold
the remaining compression headroom. The floor exists to exclude unbounded search,
not to exclude the frontier, and a relative one eventually does both.

The scale of the error is measurable. `just headroom` prices the frontier:

| parse | ms/MiB | bytes |
|---|---|---|
| the incumbent (single-slot hash head) | 4.8 | 2,605,048 |
| the accepted submission (16-deep chains) | 11.9 | 2,239,367 |
| greedy, depth 256 | 17.0 | 2,184,978 |
| lazy matching, depth 256 | 34.7 | 2,125,535 |
| **near-optimal shortest-path parse** | **1950** | **2,059,341** |

The bottom row holds ~80% of the remaining prize
([`ROADMAP.md`](ROADMAP.md)) and costs ~400x the incumbent. **A floor of 8x the
incumbent would have rejected it without looking at its bytes.**

8000 ms/MiB is ~4x that parse, so a submission can be a shortest-path parser
*and* be written for provability rather than for speed and still fit. On this
7.7 MiB corpus that is a ceiling of ~62 s in the parse, reached only by a
submission whose proof has already been accepted.

### What the constant is still trading off

Too tight, and the frontier is excluded — that is the failure the absolute form
fixes. Too loose, and the competition becomes a compute auction: at some budget
the winning move is more search rather than better search.

The old framing also worried that a loose floor "puts SIMD back on the critical
path". It does not, and this is worth being precise about, because it was the main
argument for keeping the floor tight. **The score is bytes.** SIMD makes the same
decisions faster; it never changes which match is chosen, so a vectorised
submission cannot score better than the same algorithm written plainly. A loose
budget therefore risks a compute auction, which an absolute ceiling bounds
directly — it does not risk SIMD becoming decisive, because SIMD has nothing to
win here at any budget.

It remains an operator dial. `just headroom` reprints the table it is calibrated
against; re-run it and revisit the number when the frontier moves.

## Why compression ratio and not speed

Three reasons, and the third is the one that makes the whole design work.

1. **It is exact**, as above.
2. **The headroom is real, durable, and measured.** libdeflate reaches ratios
   `miniz_oxide` cannot match *at any speed*, because the gap comes from
   near-optimal parsing rather than from tuning. On this repository's corpus it is
   22.7% under the incumbent, and `just headroom` shows that **79.6% of what is
   left is reachable through the slot** — the rest is behind the trusted harness.
   [`ROADMAP.md`](ROADMAP.md) has the decomposition.
3. **SIMD cannot improve compression ratio.** Vectorisation makes the same
   decisions faster; it never changes which match is chosen. So the best
   achievable ratio is purely algorithmic, and a competition scored on smallest
   output under a *generous* time budget is entirely inside the provable subset.
   The fact that SIMD is untranslatable stops mattering — and, because the score
   is bytes rather than time, it stops mattering at *any* budget rather than only
   while the budget is loose.

## The corpus

Five files, deliberately different in kind: Rust source, Markdown prose, Lean
source, JSON, and a binary. `verifier/make-corpus.py` builds them and prints a
hash of each.

**A corpus of one kind measures one kind of parse**, and this is not fussiness.
The first headroom measurement in the research phase used repetitive synthetic
data, compressed about 300:1, was dominated by match emission rather than match
finding, and reported that `miniz_oxide` was 6x faster than zlib. The conclusion
was backwards. Every number since has come from a corpus of real files.

### Governance

In a real round:

* **Held out.** Miners never see the contents.
* **Commit–reveal.** Publish a hash before the round, the contents after scoring.
* **Shape statistics published from the start** — byte-frequency histograms, mean
  line length, the proportion of each kind, the distribution of match lengths a
  reference parser finds. Publish these *from the beginning* or the corpus
  generator drifts into rewarding overfitting and nobody notices until a
  submission that is obviously tuned to the bytes wins.
* **Mixed, and re-mixed between rounds.** A fixed corpus is a fixed target.

The corpus in this repository is reproducible rather than held out, so that the
numbers in the docs can be rechecked. That is a property of the demonstration, not
of a round.

## Round trip

Every scored submission's output is decoded by **two independent inflaters** —
`miniz_oxide` and the system zlib behind `flate2` — and compared byte for byte
against the input.

This is empirical where the proof is universal, and both are here on purpose:

* The harness must stay memory-safe and terminating even if the contract has a
  bug, so it cannot rely on the proof.
* A disagreement between an accepted proof and the differential check is evidence
  about the **contract** or about **Charon/Aeneas**, and that is exactly the
  failure worth catching loudly rather than shipping.

The proof is what generalises the check from a corpus to all inputs. A compressor
that emits a stream which does not decode back is a silent, catastrophic and
*delayed* failure — you find out when you try to read the data. Fuzzing finds most
of the ways in; `decode(parse(x)) = x` finds all of them.

## Ranking and promotion

Rank accepted submissions by total bytes. Ties are ties — the metric is an
integer and there is nothing to break them with, so a tie should be resolved by
policy (earliest submission, say), not by measurement.

Promote the winner by copying its `parse.rs` over `harness/src/baseline.rs` and
running `just repin`. The incumbent is a frozen *copy* rather than a dependency so
that the file a miner edits and the file they are measured against can never be
the same object.

**The current incumbent is weak** — a single-slot hash head, roughly level-1
quality — so early submissions will win easily. That is good for demonstrating
that the pipeline registers wins and says nothing about how hard the competition
is once the bar has moved a few times.

## What is not scored

**Huffman coding and block splitting** sit in the trusted harness, identical for
every submission. That is what makes the score a fair comparison of *parses*.

How much they are worth is now measured rather than guessed, and the guess was
wrong about one of them: on this corpus the entropy coder accounts for 41,618
bytes of the gap to libdeflate and block splitting for **4,381** — 0.17% of the
incumbent. Huffman coding is a plausible second slot; block splitting is not.
[`ROADMAP.md`](ROADMAP.md) has the numbers and the ordering.
