# How emission is scored

Two components, on every accepted submission the validator holds.

| share | what it pays for | why it exists |
|---|---|---|
| **60%** | position on the Pareto frontier, weighted by how much that position actually buys | the frontier is where the engineering is, and it stays paid for as long as it stands |
| **40%** | the last ten improvements on the record, decaying, newest most | a field that stops improving stops collecting this, so the competition keeps moving |

What neither claims burns. So does the share of a hotkey that has since deregistered:
redistributing it would quietly pay everyone else for someone else's work.

`just weights-preview` prints exactly what the scorer would pay right now, from the
store, touching neither the chain nor a wallet.

## The 60%: the frontier

One competitor is one hotkey, represented by their **best accepted submission** — fewest
bytes, earliest submission breaking a tie, the same order the leaderboard ranks by. A
miner cannot crowd the frontier by submitting many variants, and in any case each
acceptance costs a registration.

Each competitor is a point on two axes, both "lower is better":

- **time** — absolute parse seconds, as the harness measured them
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

**elbow-sweetspot** is the default. It scores each point by how much better its incoming
trade-off rate (ratio recovered per unit time, arriving from the previous frontier point)
is than its outgoing one (continuing to the next). A point only scores where the curve
genuinely bends — where arriving there paid off distinctly better than continuing past it
did. The diagonal-sweep family agrees with it on the real frontier, which is the other
reason to trust it.

On `corpus-stage1`:

| point | time (s) | ratio (%) | on frontier? | weight |
|---|---|---|---|---|
| template | 0.2282 | 36.949 | yes | 0.2416 |
| hc-d4 | 0.2406 | 34.348 | yes | **0.6991** |
| hc-sparse | 0.2928 | 38.316 | no | 0.0000 |
| hash-chains | 0.3156 | 33.128 | yes | 0.0428 |
| hc-d64 | 0.4261 | 32.635 | yes | 0.0000 |
| lazy | 0.5199 | 32.209 | yes | 0.0154 |
| btree | 1.2668 | 32.489 | no | 0.0000 |
| optimal | 2.2326 | 31.701 | yes | 0.0011 |

`hc-d4` is the knee: a 5% time increase over `template` buys 2.6 percentage points of
ratio, and after it returns diminish. `optimal` wins the ratio outright and scores almost
nothing, because it pays 4.3x the incumbent's time for the last half point. Both corpora
agree on `hc-d4`, which is what makes it an answer rather than an artefact.

Multiply those weights by 0.60 and that is the first component.

### The boundary

Every normalized method measures against the edge of the legal region — the worst a
submission may be and still be accepted. That is **8x the incumbent's measured time**, the
multiple the gate rejects past, derived per round from the incumbent's own time rather
than assumed. Against the library's 120s fallback every real candidate (0.2–2.2s)
collapses into the corner and the normalized methods degenerate into noise.

Worth knowing as a miner: on the current corpus every candidate sits at ≤0.55 of that
boundary. **The 8x speed floor is nowhere near binding.** There is room to spend time.

## The 40%: recent improvement

An accepted submission is an **improvement** when it beats the record by at least
0.25%, relative.

- The record starts at the **incumbent's size**, not at infinity. Beating nothing is not
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

If nothing has beaten the incumbent yet, this share burns. There is no recent progress to
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
