# Validator startup configuration

Code defaults and `.env.example` define the initial operating settings. `just` loads
`.env`; PM2 also loads it through `pm2/service.config.js`. Setup creates `.env` only
when absent: existing overrides are preserved, so review old values when upgrading.
Credentials and existing local configuration are never reset by these defaults.

| Setting | Default |
| --- | --- |
| Scoring method | `local-global-improvement-space-log` |
| Pareto / recent improvement shares | 0.60 / 0.40 |
| Improvement window / threshold / decay | 10 / 0.0025 / 0.6 |
| Incumbent slowdown limit | 8× |
| Aggregated speed | Equal corpus/file mean of median total-time ratios to incumbent |
| Aggregated compression | Equal corpus/file mean of compressed/raw bytes |
| Admission | 2000 bootstrap draws; one-sided 95% lower gain bound strictly above zero |
| Benchmark repetitions / warmups | 11 / 1 |
| External reference compressors | Off |
| Benchmark timeout / memory / build memory | 300 s / 2048 MB / 4096 MB |
| Sandbox | bubblewrap; systemd user limits |
| Weight setting | Dry-run; `WEIGHT_DRY_RUN=0` explicitly enables chain writes. The only `set_weights` caller on the validator: in dry-run, nothing sets weights |
| Treasury / competition split | 80% to treasury uid 121 / 20% by score (code constants) |
| Burn UID / burn-only mode | 0 (burn mode only; unpaid competition allocation goes to the treasury) / off |
| Network / subnet | finney / 66 |
| API | 0.0.0.0:9200 |

The recency threshold applies to the separate recent-improvement component; it is
not a minimum compression gain for Pareto admission. Admission confidence and the
aggregation formulas are versioned code policy, not environment settings.
`weights-preview` uses the same scoring configuration and burn UID as the weight
setter; without a metagraph its payout eligibility remains provisional.

## Machine-specific prerequisites

- Run `./setup.sh --chain` for the verification toolchain and chain dependencies.
- Configure database credentials, run `just db-up` and `just db-migrate`, or point
  `DATABASE_URL` at a migrated external PostgreSQL database.
- API and gate must share `SERVICE_FILES` and database configuration.
- Configure the validator wallet and registration. Weight-setter dry-run still
  reads the chain and requires the validator identity; `just weights-preview` does not.
- Fetch required corpora with `just corpus-pull`. Private corpus access must be
  configured locally. Never put corpus generation secrets in public configuration.
- Use the systemd user session setup in the README so sandbox memory limits work.
  Choose `VERIFY_BENCH_CPUS` for the actual host; there is no portable fixed CPU ID.
- Keep `SERVICE_STALE_CLAIM_SECONDS` greater than `VERIFY_TOTAL_TIMEOUT` (defaults
  7200 and 2700 seconds). A separate scorer needs the required verification fingerprint.

## Gate corpora

The gate benchmarks `corpus-stage1` and `corpus-stage2` by default, checks each
corpus verdict, stores each raw run and publishes one combined aggregation only
when both pass. Both corpora must be installed and nonempty. `VERIFY_CORPUS` is an
explicit single-corpus override for local testing; leave it unset on the validator
for the two-corpus workflow. Ordinary `just bench` still uses its selected single
corpus. Previously stored one-corpus submissions need fresh compatible evidence;
this change does not upgrade old results or verification stamps automatically.

## Starting processes

After database startup and migrations, start `just service`, `just service-worker`,
`just chain-watcher` and `just weight-setter` separately, or use the existing
`pm2 start pm2/service.config.js` configuration. Combined commands are described below. Run one chain watcher and one weight setter.

## Optional background mode

Each application command accepts `--background`:

```bash
just service-worker --background
just chain-watcher --background
just weight-setter --background
# Optional local API:
just service --background
```

Without the flag, commands stay in the foreground. Background mode requires PM2
on PATH; otherwise the command fails with installation instructions. Install
Node.js/npm and then `npm install -g pm2` (setup does not install PM2 yet).
Services use `miniz-oxide-` prefixed names. Running PM2 entries produce a warning instead of a duplicate. A single stopped or
errored entry is restarted in place using its saved PM2 configuration; multiple
matching entries require operator cleanup. Old unprefixed entries from this checkout are
also recognized. Inspect with `pm2 list`, follow `pm2 logs <name>`, and stop with
`pm2 stop <name>`. Checks cover the current user's PM2 daemon, not independently
started foreground processes or other users' daemons. Stop those before switching.
Startup does not configure reboot persistence or start/migrate PostgreSQL.

Stop an individual PM2 service through the same recipes:

```bash
just service-worker --stop
just chain-watcher --stop
just weight-setter --stop
just service --stop
```

`--stop` and `--background` are mutually exclusive. A missing entry is a successful
no-op. Stopping keeps its PM2 registration; resume with the same command and `--background`.
This does not stop independently launched foreground processes or PostgreSQL.

## Stack lifecycle

```bash
just up                         # local DB, migrations, then three workers
just up --with-api              # also start the optional local submission API
just up --external-db           # skip Docker startup; migrate configured external DB
just status                     # PM2 process states and local Docker DB status
just logs                       # follow only this competition's application logs
just logs service-worker        # select by just recipe name
just logs db                    # local PostgreSQL logs
just logs --no-follow --lines 50 # print recent logs and exit
just service-worker --restart   # restart existing entry, or start if absent
just down                       # stop application processes, then local DB; preserve data
just down --keep-db             # stop applications only; use with external DB
```

All four service recipes accept mutually exclusive `--background`, `--stop` and
`--restart` flags. Restart/resume uses the entry's saved PM2 environment. `up` leaves
already-running workers alone; a startup failure leaves earlier successful starts
running and reports the failed step. `down` stops the optional API too, if present,
and leaves the database running if any application stop fails. PM2 controls shutdown
with its configured signal and timeout; it does not wait indefinitely for a running
verification. Interrupted verification claims use the existing stale-claim recovery.
Status reports process state, not proof that a worker is making progress. Application
log following uses PM2's log files and never includes unrelated PM2 services.
These commands do not install PM2, configure reboot persistence, or configure log rotation.

## Local submissions and status

Apply `just db-migrate` and restart the gate worker and weight setter after upgrading.
Restart the local API too if running, so its leaderboard uses the test exclusion. Then:

```bash
just submit-test miner/examples/lazy
just submit-baseline miner/examples/lazy my-lazy-baseline
just submission-status 42
just submission-status 42 --watch
```

Each source directory must contain `parse.rs` and `Parse.lean`. Successful enqueue
prints the submission ID and its exact watch command. Watch polls every two seconds
until Ctrl+C, reporting changed DB data. It works for miner, test and baseline IDs.
The default view shows milestone outcomes, aggregate measurements, admission and
the latest recorded score for matching evidence. Add `--verbose` for verification
timestamps, source identity, full statistics, admission details and the gate report. These are persisted
milestones, not live subprocess-stage telemetry; a null milestone does not identify
which stage failed. Inspect the gate report for failure details.

Test submissions have neither hotkey nor baseline key. They run through the gate
without spending registration slots, retain verification and benchmark/aggregation
results, and are excluded before admission, Pareto, recency, scoring and leaderboard
calculations. They do not publish a competitive speed-admission decision.

Operator baselines have no hotkey and a `local:NAME` baseline key. Names are unique;
reusing one fails instead of silently overwriting evidence. These baselines are
claimed by the gate, and accepted results participate in admission and scoring with
all allocated weight burned. The predefined example baseline manifest keeps its
fixed order; operator baselines join the ordinary submission chronology afterward.
Existing corpus-context compatibility requirements still apply: explicit single-corpus
overrides cannot compete against two-corpus baseline aggregations.

Files are stored before the queue transaction commits. Repeated test enqueue creates
new submission IDs, allowing repeated measurements. Migration 0008 permits ownerless
rows; downgrading refuses while such rows remain rather than deleting test evidence.
These are trusted local operator commands, not unauthenticated API endpoints.

Status distinguishes **gate passed** from competition admission. It resolves current
admission eligibility without computing new statistical tests or publishing decisions;
historical recorded decisions are retained under `--verbose`. Pending baseline evidence,
stale verification and incompatible scoring contexts are shown as pending, not success.
Identical Rust source IDs are diagnostic information, not a new rejection policy.
The optional baseline name defaults to the source directory name.

### Frozen baseline admission order

`examples-slow-to-fast-v2` uses the scored, incumbent-normalized speed order
observed on 2026-09-24: optimal-iter, optimal, mo-lazy, lazy, hc-d64, no-lz77,
hash-chains, hc-d4, template. This order is fixed, never dynamically sorted from
new timings. Admission compares each qualifying candidate to its selected slower
admitted neighbor; the initial point needs no comparison. Later candidates can
still dominate previously admitted points. Miner submissions remain chronological.

Replay stored evidence with `just admission-replay --historical`, then regenerate
plots with `just weights-preview`. Historical replay records decisions but does
not refresh verification or enable live scoring. Future order changes require a
version bump and explicit replay.


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
