# Running a validator

Four processes, one database, one wallet.

| process | what it does | needs |
|---|---|---|
| `submission-api` | serves `/submit`, `/submissions/{id}`, `/leaderboard` | Postgres |
| `gate-worker` | drains the queue through the six-stage gate | Postgres, the Lean/Charon/Aeneas toolchain, bubblewrap |
| `chain-watcher` | streams subnet registrations into the store | Postgres, the bittensor SDK |
| `weight-setter` | scores the round and sets weights, once an epoch | Postgres, the bittensor SDK, a registered validator hotkey |

Without the chain watcher **nobody can submit at all**: a registration row is what admits
a hotkey, and the watcher is the only thing that writes one.

## From nothing to running

```bash
./setup.sh --chain              # packages, .venv, .env, the toolchain, and the SDK (~15 min, ~9 GB)
$EDITOR .env                    # POSTGRES_PASSWORD, BITTENSOR_WALLET_*, VERIFY_CORPUS
just db-up                      # Postgres 17 from compose.yaml
just db-migrate                 # the schema
just corpus-pull                # the scoring corpora

pm2 start pm2/service.config.js # all four processes
pm2 logs
```

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

Six tables: `registrations`, `submissions`, `entitlement_claims`, `weight_sets`,
`score_snapshots`, `rate_limit_windows`. `DATABASE_URL` points the whole validator at a
managed instance instead of the compose one; it overrides every `POSTGRES_*`.

Upgrading from the old SQLite service: `just db-import-sqlite` once, before starting
anything. It will not invent the numbers the old schema never stored — see the script's
`--help`.

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

`WEIGHT_BURN_MODE=1` emits everything to the burn uid and ignores the scores — a
deliberate, restart-toggled switch for a round that is paused or not yet open. Submissions
are still accepted and scored; nothing is paid out.

To dial the whole competition down without pausing it, lower `SCORING_PARETO_SHARE` and
`SCORING_IMPROVEMENT_SHARE`. What neither claims burns.

## Promoting a new incumbent

Copy the leader's `parse.rs` over `validator/incumbent/parse.rs` (keep the header) and
run `just repin`. Every later submission is scored against it, the speed floor moves with
it, and the improvement component re-floors on the new size rather than handing out a free
improvement to whoever submits next.

## The wallet

`BITTENSOR_WALLET_NAME` / `BITTENSOR_WALLET_HOTKEY` under `BITTENSOR_WALLET_PATH`
(`~/.bittensor/wallets` by default). The hotkey must be a registered validator on `NETUID`,
or the weight setter refuses to start — which is the correct failure, loudly at startup
rather than silently at the first epoch.

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
| weights are all burn | `WEIGHT_BURN_MODE`, or nothing accepted yet: `just weights-preview` |
| the API is up but refusing everything | `/ready` reports the store; `/health` only reports the process |
| a miner disputes their weight | `just db-weights`, and `score_snapshots` for the epoch in question |

Every API refusal carries a one-line reason and an `X-Request-Id`; the matching traceback
is in the API log under the same id.

## Seed and inspect the reference frontier

Apply the additive migrations, then seed the downloaded corpora:

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
