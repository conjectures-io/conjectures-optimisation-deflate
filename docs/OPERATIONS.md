# Running a validator

Four processes, one database, one wallet.

| process | what it does | needs |
|---|---|---|
| `submission-api` | serves `/submit`, `/submissions/{id}`, `/leaderboard` | Postgres |
| `gate-worker` | drains the queue through the six-stage gate | Postgres, the Lean/Charon/Aeneas toolchain, bubblewrap |
| `chain-watcher` | streams subnet registrations into the store | Postgres, the bittensor SDK |
| `weight-setter` | saves scores each cycle, then sets weights when permitted | Postgres, chain access; registered validator hotkey only for setting weights |

Without the chain watcher **nobody can submit at all**: a registration row is what admits
a hotkey, and the watcher is the only thing that writes one.

## From nothing to running

```bash
./setup.sh --chain              # packages, .venv, .env, toolchain, and SDK
$EDITOR .env                    # database and wallet settings
just db-up                      # Postgres 17 from compose.yaml
just db-migrate                 # the schema
just corpus-pull                # the scoring corpora

pm2 start pm2/service.config.js # all four processes, and the baseline seed
pm2 logs
```

The fifth entry, `deflate-baseline-seed`, is a one-shot: it seeds `miner/template` and
every example in `miner/examples` as operator baselines, the reference Pareto frontier
miners are scored against, then exits. The initial seed verifies and benchmarks examples on the configured corpora.
Follow it with `pm2 logs deflate-baseline-seed`.
`just up` starts it too. Set `BASELINE_SEED_ON_START=0` on a host that must not seed.

**Upgrading a host that ran the `lz77-*` (or `miniz-oxide-*`) names.** The competition was
renamed to `deflate`, and with it the PM2 apps. PM2 treats a new name as a new app, so
`pm2 start pm2/service.config.js` on such a host starts a second set beside the first -- two
weight setters for one hotkey. Delete the old ones first:

```bash
pm2 delete lz77-gate-worker lz77-chain-watcher lz77-weight-setter \
  lz77-baseline-seed lz77-submission-api   # whichever `pm2 ls` shows
just up
pm2 save
```

`just up`/`just down`/`just status` recognise the old names, so `just up` alone never
duplicates a process; it warns and leaves the old one running until it is deleted.

Or one at a time, in four shells: `just service`, `just service-worker`,
`just chain-watcher`, `just weight-setter`.

### Before the first real epoch

Run the weight setter with `WEIGHT_DRY_RUN=1`. It walks the whole path — polls the chain,
scores the round, builds the vector, writes the audit row — and stops short of submitting.
`just db-weights` then shows exactly what would have been set, and `just weights-preview`
shows the scoring on its own without touching the chain at all. Take the flag out of
`.env` when the numbers look right.

## The store

Postgres holds everything except the two submitted files per submission, which live under
`SERVICE_FILES` because the gate reads them from disk in another process.

```bash
just db-psql          # a shell on it
just db-weights       # the last few vectors, and the per-hotkey reasoning behind the newest
just weights-preview  # what the scorer would pay right now, no chain, no wallet
just db-reset         # drop the schema and rebuild it -- destroys every submission
```

`DATABASE_URL` points the whole validator at a
managed instance instead of the compose one; it overrides every `POSTGRES_*`.

Upgrading from the old SQLite service: `just db-import-sqlite` once, before starting
anything. It will not invent the numbers the old schema never stored — see the script's
`--help`.

## Serving through the conjectures platform

The public competition surface, `/v1/competitions/deflate/...` (what `miner/submit.py`
talks to), is served by conjectures-validator's API straight from this database. The gate,
the chain watcher and the weight setter stay here. The platform only queues submissions
and reads what they publish. To wire it up:

1. **Role.** Set `PLATFORM_API_PASSWORD` in `.env` and run `just db-grant-platform`. It
   creates `platform_api` and grants exactly `deploy/db/platform_api.sql`: queue a
   submission and its files, count the per-hotkey rate limit, read registrations, claims
   and the published scoring. Re-run it after every `just db-migrate`, because it resets
   the role to that file.
2. **Network**, when both stacks share a host: set
   `COMPOSE_FILE=compose.yaml:compose.platform.yaml` in `.env`, then run `just db-up`. The
   database joins the platform's network, and its host port binds to loopback only.
3. **Platform side**, in conjectures-validator's `.env`:

       COMPETITIONS_ENABLED=1
       COMPETITION_DATABASE_URL=postgresql+psycopg://platform_api:<password>@conjectures_lz77_db:5432/<POSTGRES_DB>
       COMPETITION_SLUG=deflate

   The platform refuses the whole surface (503 `COMPETITION_SCHEMA_UNAVAILABLE`) and fails
   `/readyz` until this database is at migration 0011 or later, so migrate first.

**After a verifier change**, the stored `verifier_fingerprint`s no longer match
`just verification-fingerprint`, and scoring drops those submissions from the frontier.
Re-stamp each accepted one before the next epoch: `just preverify-db ID`, then
`just verify-lean-db ID`.

**On a host that cannot reach the corpus repositories** (stage 2 is private), point
`CORPUS_STAGE1_REMOTE` and `CORPUS_STAGE2_REMOTE` at local mirrors, then run
`just corpus-pull`. The gate scores both corpora on every submission.

## One registration, one submission

A hotkey with no registration on the subnet cannot submit. A hotkey with one unclaimed
registration may have one submission in the queue at a time; the registration is spent
when the gate **accepts**, so a rejected proof is a free retry and a validator-side error
never charges anyone. To submit again after an acceptance, register again.

The rule is `entitlement_claims`' primary and unique keys, not application arithmetic, so
no amount of concurrency can spend one registration twice.

```sql
-- who has a slot left
SELECT r.ss58_hot, count(*) FROM registrations r
  LEFT JOIN entitlement_claims c ON c.registration_id = r.id
 WHERE c.registration_id IS NULL GROUP BY 1;

-- what each acceptance was paid for with
SELECT s.id, s.hotkey, c.registration_id, c.claimed_at
  FROM submissions s JOIN entitlement_claims c ON c.submission_id = s.id ORDER BY s.id;
```

## Scaling the gate

A submission takes the better part of an hour. Run one `gate-worker` per machine with a
toolchain, all pointed at the same `DATABASE_URL`: each claims a different submission with
`FOR UPDATE ... SKIP LOCKED`, and a worker that dies has its claim swept back onto the
queue after `SERVICE_STALE_CLAIM_SECONDS`. Give each one a distinct `SERVICE_WORKER_ID`
(the default carries the hostname and pid, which is enough on one box).

Run exactly **one** weight setter and **one** chain watcher. Neither is harmed by a
second, but neither gains anything from it either.

## Pausing a round

`WEIGHT_BURN_MODE=1` burns the competition's share and ignores the scores — a
deliberate, restart-toggled switch for a round that is paused or not yet open. Submissions
are still accepted and scored; no miner is paid out. The treasury's share (uid 121) is
paid either way: this weight setter is the validator's only `set_weights` caller, so it
sets the whole vector, not just the competition's part (`validator/scoring/split.py`).

To dial the whole competition down without pausing it, lower `SCORING_PARETO_SHARE` and
`SCORING_IMPROVEMENT_SHARE`. What neither claims goes to the treasury.

## Promoting a new incumbent

Copy the leader's `parse.rs` over `validator/incumbent/parse.rs` (keep the header) and
run `just repin`. Every later submission is scored against it, the speed floor moves with
it, and the improvement component re-floors on the new size rather than handing out a free
improvement to whoever submits next.

## The wallet

`BITTENSOR_WALLET_NAME` / `BITTENSOR_WALLET_HOTKEY` under `BITTENSOR_WALLET_PATH`
(`~/.bittensor/wallets` by default). The hotkey must be a registered validator on `NETUID`,
to submit weights. The worker first calculates and saves scoring evidence, then checks
registration and epoch timing. An unregistered hotkey produces a warning and a saved
skip reason; the next cycle still runs and rechecks registration. No separate scoring
worker or migration is needed.

The loop runs sequentially at `WEIGHT_POLL_SECONDS` (12 seconds by default). Each cycle
saves a `weight_sets` row and its `score_snapshots`/`api_snapshot` before attempting chain
submission. Waiting, dry-run and failed registration leave `accepted=false` with a reason.
Live miner eligibility still comes from the metagraph, so scoring requires chain access.

Registration block times come from an archive node (`BITTENSOR_ARCHIVE_NETWORK`), because
a registration block is usually older than a lite node's pruned-state window. The lookup
is memoised and happens only when there is a real registration to timestamp, so a quiet
subnet costs nothing.

## When something is wrong

| symptom | look at |
|---|---|
| miners get 402 "not registered" | is `chain-watcher` running? `SELECT count(*) FROM registrations;` |
| nothing is being verified | is `gate-worker` running, and does it have the toolchain? `just doctor` |
| the queue is stuck in `verifying` | a worker died; the next one's sweep reclaims it after `SERVICE_STALE_CLAIM_SECONDS` |
| the treasury gets everything | `WEIGHT_BURN_MODE` absent a burn uid, scoring failed (the `weight_sets` summary says), or nothing accepted yet: `just weights-preview` |
| the API is up but refusing everything | `/ready` reports the store; `/health` only reports the process |
| a miner disputes their weight | `just db-weights`, and `score_snapshots` for the epoch in question |
| a miner's weight is 0 with `bounty-cap` | it has received, or would pass, `ALPHA_TOTAL_SUBMISSION_BOUNTY`: `SELECT submission_id, sum(alpha_rao)/1e9 FROM bounty_accruals GROUP BY 1;` and `bounty_caps` |

Every API refusal carries a one-line reason and an `X-Request-Id`; the matching traceback
is in the API log under the same id.

## Observability (Axiom)

Set `AXIOM_TOKEN` and `AXIOM_DATASET` (and optionally `AXIOM_ENVIRON`, `AXIOM_URL`) in `.env`
and restart the four processes; with either unset nothing is sent and nothing changes. The
records use the conjectures platform's envelope exactly -- `_time` (UTC, stamped at emit),
`severity` (`debug`/`info`/`warning`/`error`/`critical`), `source`, `event_type`, `environ` --
so they can share the platform's dataset and dashboards. Every event also carries
`competition: "deflate"`, and the chain watcher's and weight setter's carry `netuid` and
`network`. Ingestion is batched on a background thread, flushed at exit, and drops (never
blocks or raises) when Axiom is slow or down. Module: `validator/observability/axiom.py`.

| source | event_type | fields |
|---|---|---|
| all four | `service_started` | a config summary (never secrets) |
| all four | `service_stopped` | `reason` |
| all four | `service_misconfigured` | `error`: the process refused to start |
| all four | `log_error` | any loguru or `logging` record at ERROR+, or an uncaught exception: `message`, `logger`, `module`, `function`, `line`, `exception` |
| `competition-gate-worker` | `submission_claimed` | `submission_id`, `hotkey`, `baseline_key`, `worker_id` |
| `competition-gate-worker` | `gate_verdict` | `submission_id`, `hotkey`, `baseline_key`, `state` (accepted/rejected/error), `stage`, `reason`, `bytes`, `vs_incumbent`, `time_ratio`, `exit_code`, `duration_seconds` |
| `competition-gate-worker` | `submission_requeued` | `submission_id` (or `count` for the stale-claim sweep), `reason` |
| `competition-gate-worker` | `gate_validator_error` | `submission_id`, `exit_code`, `error`: the gate itself is broken |
| `competition-chain-watcher` | `registrations_recorded` | `count`, `initial_load`, `block`, `uids` |
| `competition-chain-watcher` | `chain_read_failed` | `error`, `last_block` |
| `competition-weight-setter` | `weights_set`, `weights_planned` (dry run), `weights_skipped`, `weights_failed` | `block`, `dry_run`, `burn_mode`, `uids`/`weights` (nonzero entries), `treasury_uid`, `treasury_share`, `competition_share`, `burn_uid`, `burn_share`, `miners`, `summary`, `error` |
| `competition-weight-setter` | `bounty_recorded` | `epoch_block`, `credits`, `credited_alpha`, `miner_pool_alpha`: one epoch's emission credited to submissions |
| `competition-weight-setter` | `bounty_capped` | `submission_id`, `hotkey`, `earned_alpha`, `projected_alpha`, `bounty_alpha`: a submission reached its bounty |
| `competition-submission-api` | lifecycle and `log_error` only | |

## Seed and inspect the reference frontier

The validator seeds these on every start (`deflate-baseline-seed`, above). To seed by
hand, apply the additive migrations, then seed the downloaded corpora:

```bash
just db-migrate
just baseline-seed --corpus corpus-stage1 --corpus corpus-stage2
just weights-preview --out-dir data/benchmark-reports/baselines
```

Seeding includes `miner/template` and complete source/proof pairs in `miner/examples`.
It verifies the exact stored revision before native benchmarking. Identical completed
work is reused; interrupted work resumes. `--only lazy` restricts selection; `--overwrite`
forces new measurements and aggregation while retaining prior evidence. Matching static
and Lean verification is still reused. A changed verifier fingerprint requires rechecking.
Only one revision per baseline name is active. Over-speed-limit examples retain evidence
but are not activated. Baselines consume no miner registration and have no payable hotkey.
Neither seeding nor preview submits weights to the chain.

Aggregate independently with explicit corpus-content identities (available in benchmark_runs):

```bash
just bench-aggregate --submission-id 123 --corpus corpus-stage1:HASH --preview
just bench-aggregate --submission-id 123 --corpus corpus-stage1:HASH --publish
```

Repeat `--corpus` for multiple corpora. Repeat `--run-id` to select exactly one existing
run per corpus; otherwise the latest successful non-invalidated measured run is used.
Legacy runs without measurement timestamps require explicit IDs. Legacy evidence without
build/host provenance must be remeasured. Publication requires current successful static
and Lean verification and the ordinary speed floor; it does not grant a miner registration.
Use consistent host, CPU limits, repetitions, compiler and engine across the evaluation.
Stage 2 reports are operator-only and must not be published with per-file private evidence.

### Updating to total compression timing

Apply `just db-migrate` (revision `0006`), then rerun baseline seeding on the same
corpora and with the same CPU/resource settings used for subsequent submissions.
The v4 engine measures both LZ77 and encoding every round. The incremental seeder
replaces incompatible active measurements while retaining historical evidence.
Until rebenchmarked and published, old LZ77-only points are excluded from scoring.
Use `just weights-preview --out-dir "$PWD/data/benchmark-reports/current"` from the
repository root to inspect the resulting total-time Pareto and stage telemetry.
