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

## The speed floor

A submission is rejected if its parse takes more than **8x the incumbent's** wall
clock on the same corpus.

Wall clock re-enters only as a **coarse gate**, where ±10% noise is harmless, and
never as the score. It exists because without it the degenerate submission is
zopfli: spend unbounded time to shave a fraction of a percent.

**The constant is load-bearing in both directions and it is not calibrated.**
Too tight, and SIMD becomes decisive — at which point the target dies, because
SIMD is outside the provable subset. Too loose, and the competition becomes a
compute auction. 8x was chosen because the research phase measured that
`miniz_oxide`'s own best ratio sits around 8x its level-9 time; the reference
submission uses 3.0x of it. A near-optimal parser will want much more, and
somebody will have to decide.

## Why compression ratio and not speed

Three reasons, and the third is the one that makes the whole design work.

1. **It is exact**, as above.
2. **The headroom is real and durable.** libdeflate reaches ratios `miniz_oxide`
   cannot match *at any speed*, because the gap comes from near-optimal parsing
   and block splitting rather than from tuning. On this repository's corpus it is
   22.7% under the incumbent.
3. **SIMD cannot improve compression ratio.** Vectorisation makes the same
   decisions faster; it never changes which match is chosen. So the best
   achievable ratio is purely algorithmic, and a competition scored on smallest
   output under a *generous* speed floor is entirely inside the provable subset.
   The fact that SIMD is untranslatable stops mattering — but only while the floor
   stays loose.

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
Both are worth ratio and both are natural second slots, each needing its own
contract.
