# How emission is scored

Two components, on every accepted submission the validator holds.

| share | what it pays for | why it exists |
|---|---|---|
| **60%** | position on the Pareto frontier, weighted by how much that position actually buys | the frontier is where the engineering is, and it stays paid for as long as it stands |
| **40%** | the last ten improvements on the record, decaying, newest most | a field that stops improving stops collecting this, so the competition keeps moving |

What neither claims burns. So does the share of a hotkey that has since deregistered:
redistributing it would quietly pay everyone else for someone else's work.

`just weights-preview` reads the database without chain writes. Without a supplied
metagraph, miner payouts are labeled provisional; use `--metagraph hotkeys.json` with a
hotkey-to-UID map for eligibility-aware results.

## The 60%: the frontier

Each verified, accepted submission with a valid published aggregation is a point.
All points are scored before checking payout eligibility. Baselines and deregistered
hotkeys retain their positions. If a hotkey has several frontier points, only its
oldest frontier submission is payable (lowest submission ID breaks timestamp ties).
The other Pareto allocations burn; miner shares are never renormalized afterward.
Exact coordinate duplicates retain the oldest point. This is defensive handling;
registration requirements still apply at intake.

Each competitor is a point on two axes, both "lower is better":

- **time** — total compression seconds (LZ77 + shared DEFLATE encoding)
- **ratio** — compressed bytes as a percentage of raw, *not* absolute bytes, because the
  corpus changes between rounds and absolute bytes are not comparable across it

The Pareto frontier is the set of points nothing else beats on both axes at once. A
dominated point — something both slower and larger than another submission — earns nothing
from this component. There is no sense in which it bought anything. It can still earn from
the other 40%, which is the point of having two.

### Which weight function, and why

Being *on* the frontier is not the same as being worth something. Eight weight functions
were written and argued over in `scripts/pareto-weights.py`; they now live in
`validator/scoring/pareto.py` so the validator scores with the code that was argued over
rather than a reimplementation. Two of the eight fail in exactly the ways that script's
own docstring predicted:

- **hypervolume** hands `lazy` 81% of the weight on the real frontier. Its structure
  credits each point with the empty space to its left, and `lazy` at 0.52s sits in front
  of a 1.7s hole with `optimal` on the far side. Normalizing the axes redistributes it and
  flips the winner to `optimal` — and a scoring function whose answer inverts under a
  change of units is not measuring what it claims to.
- **neighbor-improvement** hands `template` 92%, because it anchors the fastest point
  against the 100% ratio ceiling and nothing real is near it: even a literals-only parser
  reaches 63.5%.

**local-global** is the default. For a point between faster/worse A and slower/better B,
normalize its time and compression ratio within their rectangle to t and r. The default
coefficient is `2 - t - r`: 1 on the straight trade-off, greater on the better side.
The local coefficient uses immediate neighbours (endpoints get 1); the global coefficient
uses the frontier extremes. Multiply the two, normalize across all frontier points, then
multiply by the Pareto emission share. A singleton receives the entire Pareto share.
Other methods, including elbow-sweetspot, remain selectable for comparisons.

Local-global does not use the external speed limit in its formula. Acceptance still
requires time no greater than 8 times the paired incumbent. Timing is the sum of per-file
medians of the paired LZ77 + encoding times for each measured repetition, excluding
warmups. Stage medians are kept for telemetry, but their sum is not the scored statistic. Output ratio is total compressed
bytes divided by total raw bytes. Compare only identical corpus-content sets and compatible
measurement contexts, even when displaying percentages.

Baseline allocations burn explicitly. With only baselines and no miner improvement,
all emission burns. These controls do not by themselves solve near-duplicate frontier
manipulation; novelty thresholds remain a separate policy decision.

## The 40%: recent improvement

An accepted submission is an **improvement** when it beats the record by at least
0.25%, relative.

- The record starts at the smaller of the **incumbent and active baseline sizes**, not at infinity. Beating nothing is not
  an advance, and a first submission worse than the baseline every miner is given has not
  moved anything.
- It then follows whichever is smaller, the best accepted submission so far or the
  incumbent. Promoting a new incumbent mid-round therefore raises the bar rather than
  handing a free improvement to whoever submits next.
- It is measured on **bytes**, the competition's headline metric. A submission that is
  merely faster at the same size has not moved the record — it may well be a new frontier
  point, and the other 60% is where it is paid for that.
- 0.25% is above measurement noise and below what any real algorithmic step buys.

The last **ten** improvements share the 40%, decaying geometrically at 0.6, newest first:

| rank | share of the 40% | of total emission |
|---|---|---|
| 1 (newest) | 40.2% | 16.10% |
| 2 | 24.1% | 9.66% |
| 3 | 14.5% | 5.80% |
| 4 | 8.7% | 3.48% |
| 5 | 5.2% | 2.09% |
| 10 (oldest) | 0.4% | 0.16% |

A hotkey holding several of the last ten accumulates their shares: shipping three of the
last ten advances is worth three slots, not one. Past ten, an improvement has been
superseded often enough that rewarding it is the frontier's job, not recency's.

If nothing has beaten the reference record yet, this share burns. There is no recent progress to
reward, and spreading it over the frontier would quietly turn 60/40 into something else.

## Cadence

Once per epoch, a margin of 12 blocks before the boundary, and only when the chain's
weights rate limit allows. Setting late means the vector lands just before consensus reads
it, so it reflects the newest scores; setting early wastes the window and risks the rate
limit blocking the one that would have mattered.

Every attempt — set, skipped, or refused by the chain — writes a `weight_sets` row with a
`score_snapshots` row per competitor beside it, in one transaction. `just db-weights`
prints the last few. A vector whose reasoning went missing is not an audit trail.

## Tuning

Every number above is an environment variable (`SCORING_*` in `.env.example`), including
the choice of weight function — all eight stay selectable, so a live round can be retuned
without a deploy. A misspelt method name stops the worker at startup rather than quietly
paying a round with the wrong function.

`just weights-preview --method diagonal-sweep-k1.0` shows what a different one would pay
before you set it.

## Database evidence and reproducibility

The scorer consumes published aggregations, not local JSONL files or legacy summary-only
submission rows. Old rows need compatible benchmark evidence and aggregation publication.
`SCORING_CORPORA` can select a JSON map of corpus names to content hashes. Without it,
all selected points must share one evaluation context; incompatible contexts stop scoring.

Aggregations retain exact run IDs, source hash, calculator version, environment/build
provenance and timing statistics. Per-file sample standard deviation describes repetition
spread. A deterministic paired per-file bootstrap provides percentile 95% intervals for
summed median times and their ratio. Intervals with fewer than ten measured rounds are
flagged sparse; fewer than two means no interval. They do not capture systematic bias or
between-run host drift and do not affect rewards.

`just weights-preview --out-dir data/benchmark-reports/baselines` writes an operator-only
aggregate report and plot. `--aggregation-id ID` may be repeated to inspect selected
stored aggregations for currently eligible submission identities. Reports include exact
inputs and scoring configuration; historical weight-set snapshots remain unchanged.

Current aggregation version is `compression-median-v3`, using schema-v4 measurements.
Encoding runs on every repetition, and hashing/decompression checks remain outside
both stage timers. Per-file LZ77, encoding and total timing statistics are retained;
bootstrap intervals apply to total compression time and the total-time ratio.
Legacy LZ77-only aggregations cannot enter the current frontier; they require new
measurements. No synthetic totals are backfilled from the old single encoding sample.
