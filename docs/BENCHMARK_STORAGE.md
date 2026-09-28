# Benchmark storage

Benchmark evidence is stored in the tables introduced by migration 0002 and
subsequent migrations. See the migration files under `deploy/migrate/` for the
current schema.

| Table | Purpose |
| --- | --- |
| `benchmark_runs` | One candidate on one corpus, with paired incumbent and references; full raw JSONB |
| `benchmark_compression_results` | Per-file, per-method byte counts, content hashes and success/determinism |
| `benchmark_speed_samples` | Individual parse-time repetitions linked to compression results |
| `benchmark_aggregations` | Successful aggregate metrics for one algorithm |
| `benchmark_aggregation_inputs` | Exact runs used by an aggregation |

## Raw runs and structured results

Identify the candidate by SHA-256 of `parse.rs` (not the submission digest, which also
includes the proof), its method name, and the corpus name and content hash.
The corpus hash is SHA-256 of canonical JSON for the sorted list of
`[file_path, file_sha256, raw_bytes]` triples, independent of directory and record order.

`raw_data` is a JSONB array preserving original JSONL values, unknown fields and array
order, not textual formatting. It retains environment, settings, file format labels,
errors, encoding times and other evidence. Aggregation uses structured compression
results and speed samples; it does not depend on local JSONL files.

`benchmark_compression_results` has one row per `(run_id, file_index, method)`.
`file_index` is zero-based among that run's file records, not a stable corpus identifier.
Match input content across runs by `file_sha256`. Every result requires `file_path`,
`file_sha256`, nonnegative `raw_bytes`, and `succeeded`. Successful results also require
nonnegative `output_bytes` and a valid `output_sha256`; failures may omit them.
`tokens_sha256` retains the token-stream hash when available. Errors remain in JSONB.

`benchmark_speed_samples` has one row per repetition. A composite foreign key to the
compression result ensures the run, file and method exist. It stores `repetition`
(zero-based within that method's reps array), `phase`, `order_index` and `time_s`.
These are parse times for parser methods, matching the engine protocol; encoding time
is separate and remains in JSONB. Seconds use double precision to match engine output.
Keep warmups and reference methods; filter `phase = 'measured'` for statistics.

All three representations are inserted in one transaction. Treat evidence as immutable
in application code. The importer validates required sizes/hashes, method membership,
finite nonnegative timings, and expected sample counts for successful methods. Runs with
candidate or incumbent method failures have status `failed`; a failed optional reference
does not invalidate the candidate. Invalidation sets `invalidated_at` and
`invalidation_reason` without changing evidence.

### Determinism

The engine compares parser token hashes across repetitions. It compresses and records
output size/hash only on the first repetition, so it does not directly measure variation
in compressed size across repetitions. Equal tokens support repeatability for a fixed
encoder; different tokens do not necessarily imply a different compressed size.

`tokens_deterministic` is true when repeated token comparisons are available and agree,
false when the engine reports a token mismatch, and null when no reliable comparison is
available (external reference compressors, a single repetition, or an interrupted run).
A successful result cannot have `tokens_deterministic = false`. The original engine flag
is also retained in JSONB. These observations are not a proof about future executions.

## Queries

For one validated run and its candidate, calculate a pooled ratio from byte totals,
not an average of individual file ratios:

```sql
SELECT method,
       sum(raw_bytes) AS original_bytes,
       sum(output_bytes) AS compressed_bytes,
       sum(output_bytes)::numeric / nullif(sum(raw_bytes), 0) AS compression_ratio
FROM benchmark_compression_results
WHERE run_id = :run_id AND method = :candidate_method
GROUP BY method
HAVING bool_and(succeeded);
```

This returns no result if any stored file result for that method failed. The aggregation
service must additionally verify complete file coverage and run eligibility before using
these totals; row constraints do not guarantee that a writer inserted all expected rows.
Input bytes are repeated across methods, so always select or group by method before summing.

```sql
SELECT s.run_id, r.file_path, r.file_sha256, s.method,
       avg(s.time_s), stddev_samp(s.time_s), min(s.time_s), max(s.time_s)
FROM benchmark_speed_samples s
JOIN benchmark_compression_results r USING (run_id, file_index, method)
WHERE s.phase = 'measured'
GROUP BY s.run_id, r.file_path, r.file_sha256, s.method;
```

## Aggregation and reruns

The caller supplies required corpus versions and optional explicit run IDs.
Configuration lives in code or service configuration, not database plan tables.
For unspecified inputs, select the latest successful, non-invalidated run for the
candidate and exact corpus version, ordered by `created_at DESC, id DESC`.

Before calculating, validate candidate identity, required corpus coverage (one run per
corpus), complete file/method results, method success/determinism and compatible engine,
incumbent and benchmark settings. Missing or incompatible inputs cause an explicit failure.
An artifact cannot prove its producer included every corpus file; require the expected
corpus hash. Raw/projection consistency and immutable evidence remain application duties.

Save aggregation metrics and input links atomically. `calculator_version` identifies the
implementation/rules used. Metrics are `raw_bytes`, `incumbent_bytes`, `bytes`,
`incumbent_seconds` and `parse_seconds`; ratios are derived. Linked runs identify the corpora.
A rerun B2 can be combined with A1 while the old aggregate retains A1/B1. Invalidation
does not rewrite history; the operator/service must select replacement evidence and recalculate.

`submissions.aggregation_id` selects the current aggregate; `score_snapshots.aggregation_id`
preserves historical inputs. Score snapshots remain attached to weight publications.

## CLI ingestion

`just bench-db [bench arguments]` saves complete per-process artifacts locally and imports
them. `just bench-import FILE...` imports or retries without running Rust. Ordinary
`just bench` remains independent of the DB. Both DB commands use existing `.env` settings.
Neither command updates aggregates, scores or weights.

New artifacts carry `run_uuid` in the meta record. A nullable unique `run_key` prevents
concurrent duplicates: retrying returns the existing ID; different data under the same
UUID is rejected. Legacy single-candidate v3 files use a SHA-256 of canonical JSON records
as their key. Canonical JSON uses sorted object keys, compact separators, ASCII escaping,
UTF-8 encoding and no non-finite numbers. New executions get new UUIDs.

Each artifact is one transaction containing raw JSONB, compression results and speed samples.
A database failure leaves local artifacts for retry. Start time comes from the engine;
finish time remains unknown. Imports do not undo invalidation. Build failures or crashes
before the driver returns measurements retain existing diagnostics/workspaces without a DB run.

Multi-candidate merged legacy reports are rejected because they discarded paired reference
samples. `bench-db` preserves each underlying candidate process separately. Keep private
corpus data restricted; raw artifacts and tables include per-file evidence.

## Applying or reversing

From the repository root (`just` loads `.env`):

```sh
just db-migrate
just db-downgrade 0001
```

Downgrading deletes benchmark evidence and the two aggregation reference columns.
Existing submissions, registrations, scores and weight publications remain. Export any
benchmark evidence you need before downgrading.

For a database created with older migration files, review its actual schema and
the migration history before changing stored evidence.
