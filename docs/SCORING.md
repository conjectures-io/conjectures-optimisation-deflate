# How emission is scored

The validator's weight is split first: the treasury (uid 121) takes 80% and this
competition 20% (`validator/scoring/split.py`, code constants on netuid 66). Everything below
describes how the competition's 20% is shared out; "burns" means *is unpaid* within that
share, and the unpaid part goes to the treasury, not the burn uid (see "Treasury and
competition budget" at the end). If scoring fails the treasury is paid everything for that
epoch rather than the epoch being skipped.

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

**local-global-improvement-space-log** is the default. For a point between faster/worse A and slower/better B,
normalize its time and compression ratio within their rectangle to t and r. The default
coefficient is `2 - t - r`: 1 on the straight trade-off, greater on the better side.
The local coefficient uses immediate neighbours (endpoints get 1); the global coefficient
uses the frontier extremes. Multiply both coefficients by the logarithmic improvement
space factor, then normalize across frontier points and multiply by the Pareto share.
For points sorted by increasing time, the factor is the mean of:

- `log(t_next / t_i) / log(t_max / t_min)`, zero for the slowest point;
- `log(r_previous / r_i) / log(r_max / r_min)`, zero for the worst compression ratio.

This splits a fixed improvement budget on each axis. Equal proportional gains receive
equal credit; a fixed absolute gain receives more credit at lower values. Local-global
coefficients themselves remain linear. Both axes must be positive and finite. A singleton receives the entire Pareto share.
Other methods, including elbow-sweetspot, remain selectable for comparisons.

Local-global does not use the external speed limit in its formula. Scoring eligibility requires balanced slowdown no greater than 10 times the paired incumbent
and balanced compressed/original size no greater than 40%. The Pareto time coordinate is now the arithmetic mean of per-file
candidate/incumbent median total-time ratios within each corpus, then the equal-weight
mean across corpora. Total time means paired LZ77 + encoding time, excluding warmups.
A coordinate of 1 means incumbent performance; lower is better. Nonempty files count
equally regardless of size. Empty files are excluded from both balanced metrics but
remain in absolute telemetry. Positive per-file median times are required.
The absolute sum of per-file medians remains telemetry only. The dimensionless Pareto coordinate has its own paired bootstrap
interval (`balanced_time_ratio`); it is not the ratio of summed times.
Recalculation reuses retained evidence; preview automatically applies the new formula. Stage medians are kept for telemetry, but their sum is not the scored statistic. The scored compression ratio is the arithmetic mean of per-file compressed/raw
ratios within each corpus, then the equally weighted mean across corpora. Empty
files are excluded from this ratio (an all-empty corpus is rejected), but their
bytes and timings remain in telemetry. Total compressed/raw bytes is retained
as byte-weighted telemetry. Recency improvements use the same balanced ratio. Compare only identical corpus-content sets and compatible
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
summed median times, their ratio, and the balanced per-file time-ratio coordinate. Intervals with fewer than ten measured rounds are
flagged sparse; fewer than two means no interval. These telemetry intervals do not capture systematic bias or
between-run host drift. Admission uses a separate candidate/reference comparison described below.

`just weights-preview --out-dir data/benchmark-reports/baselines` writes an operator-only
aggregate report and plot. `--aggregation-id ID` may be repeated to inspect selected
stored evidence for previously verified, accepted submission identities. Reports include exact
inputs and scoring configuration; historical weight-set snapshots remain unchanged.

Current aggregation version is `compression-relative-time-v5`, using schema-v4 measurements.
Encoding runs on every repetition, and hashing/decompression checks remain outside
both stage timers. Per-file LZ77, encoding and total timing statistics are retained;
bootstrap intervals apply to total compression time, the total-time ratio, and the
balanced per-file time ratio used on the Pareto axis. Historical snapshot `time_s`
columns retain absolute seconds; the relative coordinate is derived from the linked
aggregation evidence and is exported explicitly as `normalized_time_ratio` in previews.
Legacy LZ77-only aggregations cannot enter the current frontier; they require new
measurements. No synthetic totals are backfilled from the old single encoding sample.

Preview automatically recalculates from stored schema-v4 evidence with the current
formula, including after an aggregation version change. It uses the runs linked to
each submission's published aggregation (or explicit aggregation IDs), preserving
the original records. It validates corpus/source identities, measurement compatibility
and invalidation status. Successful historical static/Lean verification suffices
for this operator-only report; `verification_current` records whether the stamp still
matches. Neither verification nor benchmarks are executed by preview. The report
records both the original and recalculated calculator versions.

To update published evidence for live scoring after an aggregation version change,
reaggregate retained schema-v4 runs with
`just bench-aggregate --submission-id ID --corpus NAME:SHA256 --publish`
(repeat --corpus for each corpus, optionally select --run-id). This does not
rerun benchmarks. Old aggregations remain immutable and are excluded from live scoring.

The current verifier fingerprint includes aggregation/scoring source files, so this
update also requires refreshing static/Lean verification before publishing for live
scoring. This restriction does not apply to the read-only preview.
Incremental baseline seeding refreshes verification and reuses compatible benchmark
evidence; it does not require rerunning compatible measurements.


## Statistical speed admission

Aggregation publishes measurements; admission decides whether they may participate in
rewards. A candidate that appears faster with equal or worse compression must establish
its speed advantage against **one** point. An equal-compression point it would replace
is the reference; otherwise the reference is the immediate slower, better-compressing
neighbor on the hypothetical updated frontier. Exact duplicates and dominated candidates
do not qualify. A new best compression ratio has no such neighbor and requires no speed
test. Comparisons use full-precision balanced compression ratios, without a minimum
compression improvement.

The speed coordinate remains the equal-corpus mean of equal-file candidate/incumbent
median total-compression time ratios. Positive gain is
`100 * (1 - candidate_coordinate / reference_coordinate)`. Admission holds corpus files
and weights fixed and resamples repetitions within each nonempty file, recomputing both
complete coordinates per draw. It does not resample files or count per-file wins.
Content hashes and corpus manifests must match; duplicate contents retain their manifest
membership and existing weights. Three measured repetitions per file are the minimum;
normal benchmarks use eleven.

The reproducible comparison uses 2,000 bootstrap draws and a seed derived from immutable
run evidence. Within a run, submission/incumbent repetitions are paired only when recorded
execution-order indices establish interleaved round blocks. Separate runs are resampled
independently; shared run observations reuse draws. LZ77 and encoding remain paired in
each total-time observation. Quantiles use linear interpolation at `(n-1)*p`.

The **5th percentile gain must be strictly positive**: a one-sided nominal 95% confidence
rule. Plots show the central **90%** interval (5th–95th percentiles), whose lower endpoint
is that decision boundary. This is not a 95% probability that the algorithm is faster,
and does not control false acceptances across repeated submissions. Small-sample
bootstrap coverage is approximate. Cross-file dependence, host drift between runs and
corpus-composition uncertainty are not estimated. Fresh interleaved candidate/reference
confirmation benchmarks remain a future improvement.

Outcomes are `passed`, `not_required`, `inconclusive`, or `dominated`. Missing or invalid
evidence is an evaluation error; missing predecessors or changed contexts are pending.
Inconclusive, dominated, pending and invalid points receive zero allocation and do not
change frontier geometry or recency record history. Admitted baselines participate in
weighting and burn their allocations; registration and oldest-submission duplicate-hotkey
payment rules apply after allocation as before.

### Commands and replay

```sh
just db-migrate
just admission-run                         # admit newly published evidence
just admission-replay --preview            # inspect a changed context without writes
just admission-replay                      # explicitly publish revised decisions
just admission-replay --historical         # backfill historically verified evidence
just weights-preview                       # read-only recalculation and plots
```

`--historical` permits existing successful verification stamps and recalculates from
retained runs. It does not refresh verification, republish aggregations, or enable stale
evidence for live scoring. Both admission commands accept `--out PATH` for decision JSON;
relative paths are relative to `validator/`. `--preview` never writes decisions.

`submission_admission_checks` is append-only, including database-enforced immutability.
Each row stores candidate/reference aggregation IDs, policy, outcome and reason, plus
JSONB statistics, historical frontier coordinates/membership, ordered decision-prefix
keys and evidence hashes. `submissions.admission_check_id` selects the current decision;
score snapshots retain the exact decision ID used. Decisions are reused only when the
candidate, complete preceding context, policy and ordering agree. Ordinary weight
recalculation reads these decisions and never chooses a new reference. A changed context
requires explicit replay; there is no automatic admission of legacy rows. All older
checks remain available after replay. Publication serializes pointer and evidence access
in one transaction.

Baselines use the explicit `examples-v1` order in `scoring/admission.py`:
`template`, `hash-chains`, `hc-d4`, `hc-d64`, `lazy`, `mo-lazy`, `no-lz77`, `optimal`,
`optimal-iter`. Baseline seeding benchmarks the selected names, then explicitly replays
admission in this order. `--only` does not alter ordering; missing predecessors leave
later entries pending. `--overwrite` appends benchmark evidence and replays affected
successors while retaining earlier decisions. Adding/removing baseline names requires a
manifest/version change and replay. Miner batches use submission timestamp then ID.
Miner-only deployments are supported when no baseline set is active.

### Miner-facing explanations

Default output is `data/benchmark-reports/current/`. `scores.json` includes per-point
admission status, reason, evidence IDs, policy and full statistical metadata. It labels
read-only preview decisions separately from persisted results. `speed-admission.png`
shows measured gain and uncertainty against zero. `admission/submission-ID.png` shows
that interval, a zoomed historical Pareto comparison and per-file gains. Excluded points
are hollow and never join the admitted frontier line. The horizontal comparison range
is anchored to the reference, not a marginal timing interval for the candidate.

The per-file panel reports faster-on-X-of-Y files and ties. This is descriptive: a
legitimate aggregate win may include regressions, and aggregate gain is not the mean of
per-file gain percentages. File hashes, corpus identities and run IDs in JSON support
an API implementing the same views without requiring local benchmark files.

Admission detail plots use stacked gain, normalized-time and Pareto panels. Per-file
diagnostics are written separately as `admission/submission-<id>-files.png`.
The proposed browser API is documented in [FRONTEND_API.md](FRONTEND_API.md).


## Treasury and competition budget

The weight setter is the validator's only `set_weights` caller and sets the whole vector
(`validator/scoring/split.py`): the treasury takes 80% and the competition allocates up to
20% by score. On netuid 66 the treasury uid (121) and the 20% are code constants; a
`WEIGHT_TREASURY_UID` or `WEIGHT_COMPETITION_SHARE` that disagrees refuses to start. Off
mainnet both are configurable (`WEIGHT_TREASURY_UID` defaults to `WEIGHT_BURN_UID`,
`WEIGHT_COMPETITION_SHARE` to 0.20). `WEIGHT_COLLECTOR_UID` and `WEIGHT_COLLECTOR_HOTKEY`
are accepted as older names for `WEIGHT_TREASURY_UID` and `WEIGHT_TREASURY_HOTKEY`.

Setting `WEIGHT_TREASURY_HOTKEY` to the treasury's registered SS58 hotkey guards against uid
reassignment: an absent hotkey causes a recorded skip, with no fallback to a different
recipient. Off mainnet it also locates the treasury uid and follows it if it changes; on
netuid 66 it must sit at uid 121, or the epoch is skipped. A treasury uid absent from the
metagraph is likewise a recorded skip.

Scoring and speed admission still include baselines in the frontier. Miner scores are
multiplied by the competition's share without renormalization. Baseline, deregistered,
duplicate-hotkey and otherwise unpaid allocations go to the treasury. For example, a miner
allocated 25% of the competition budget receives 5% overall; the treasury receives 95% if
there are no other payable miners. An empty or baseline-only round, or one whose scoring
raises, sends 100% to the treasury. The burn uid is never eligible for miner payment.

`SCORING_PARETO_SHARE` and `SCORING_IMPROVEMENT_SHARE` remain fractions **within** the
competition budget (defaults 0.60/0.40). Set them to 1/0 for Pareto-only rewards. Score
snapshots and weights-preview report competition-local fractions; the weight-set audit
vector contains actual subnet fractions and its summary records the budget and treasury
allocation. Historical `burn` labels in score reports mean unpaid competition allocation;
normal weight setting routes it to the treasury. No schema migration is required.

`WEIGHT_DRY_RUN=1` remains the default. `WEIGHT_BURN_MODE=1` pauses the competition: its
share goes to `WEIGHT_BURN_UID` (to the treasury if that uid is absent) and the treasury's
share is paid as usual. Restart the weight setter after configuration changes. Run only one
weight-setting worker for a validator wallet, and do not also run conjectures-validator's
retired emissions worker: this worker constructs the complete subnet vector.


### Scoring boundaries and benchmark timeouts

`SCORING_MAX_TIME_RATIO=10` and `SCORING_MAX_RATIO_PCT=40` are inclusive reward
eligibility limits. Both use equal-corpus averages of per-file ratios. Points
outside either limit remain stored but are excluded before Pareto construction,
statistical neighbor selection, and both Pareto and improvement rewards. Admission
records contain outcome `excluded`, reason `outside-scoring-bounds`, and structured
`scoring_bounds` values, limits, and violations. Baselines use the same policy.

These replace the old 8x summed-time acceptance rule. Successful benchmarks and
aggregations are retained regardless of scoring bounds. `VERIFY_BENCH_TIMEOUT=300`
remains the wall-clock cap per build/measurement process; a measurement includes
one corpus and all repetitions. `VERIFY_TOTAL_TIMEOUT=2700` caps the worker gate.
The deprecated benchmark `--speed-floor` option is metadata only.

Apply migration 0010 with `just db-migrate`. Changed scoring bounds invalidate old
admission decisions: use `just admission-replay` for current verified evidence, or
`just admission-replay --historical` for an operator's historical baseline replay.
`just weights-preview` recalculates historical decisions without rebenchmarking.
Restart workers after changing environment settings. `SCORING_SPEED_FLOOR` remains
an alias for the scoring time limit; the new setting takes precedence.
