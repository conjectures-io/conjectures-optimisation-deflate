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
| Weight setting | Dry-run; `WEIGHT_DRY_RUN=0` explicitly enables chain writes |
| Burn UID / burn-only mode | 0 / off |
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

## Remaining corpus integration

The automatic gate still measures the single default `corpus-stage1` (or
`VERIFY_CORPUS` override). Two-corpus baseline/scoring alignment is a separate pending
implementation task. `SCORING_CORPORA` can select exact corpus hashes but does not
make the gate benchmark both corpora. Do not treat startup defaults as resolving this.

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
Existing corpus-context compatibility requirements still apply: a one-corpus gate
result cannot automatically compete against two-corpus baseline aggregations.

Files are stored before the queue transaction commits. Repeated test enqueue creates
new submission IDs, allowing repeated measurements. Migration 0008 permits ownerless
rows; downgrading refuses while such rows remain rather than deleting test evidence.
These are trusted local operator commands, not unauthenticated API endpoints.
