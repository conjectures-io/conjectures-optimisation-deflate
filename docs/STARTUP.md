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
`pm2 start pm2/service.config.js` configuration. Combined just lifecycle commands
remain planned. Run one chain watcher and one weight setter.
