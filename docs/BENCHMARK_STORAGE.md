# Benchmark storage

Migration 0002 adds four tables, without plans, corpus registries or scoring configuration.

| Table | Purpose |
| --- | --- |
| benchmark_runs | One candidate on one corpus, with paired incumbent and references |
| benchmark_measurements | SQL timing projection of the raw output |
| benchmark_aggregations | Successful aggregate metrics for one algorithm |
| benchmark_aggregation_inputs | Exact runs used by an aggregation |

## Raw runs

Identify the candidate by SHA-256 of parse.rs (not the submission digest, which also
includes the proof), its method name, and the corpus name and content hash.
Ingestion must compute the corpus hash from a canonical manifest including file paths,
content hashes and sizes; a name alone is not a version identifier.

raw_data is a JSONB array of the original JSONL records, preserving values and array
order, not textual formatting. Keep metadata, settings, environment, source/library
hashes, file/output/token hashes and sizes, encoding times, determinism, errors,
warnings and repetitions. Recalculation needs no external JSONL files.

benchmark_measurements extracts run_id, file_index (zero-based among file records),
file_path, method, repetition (zero-based within that method's reps array), phase,
order_index and time_s. Seconds use double precision to match the engine's float output.
Keep warmups and reference methods; filter phase='measured' for statistics.
File-level data stays in JSONB, including errors from methods with no samples.

Insert JSONB and measurements in one transaction. Treat completed evidence as immutable
in application code. Runs have complete/failed status; this is a results store, not a
worker queue. Complete execution may still contain method errors; aggregation must
check those. Invalidation sets invalidated_at and invalidation_reason without changing
raw evidence.

Capture each candidate's underlying engine run separately. The JSONL exporter merges
multiple candidate processes and keeps only the first process's detailed incumbent/
reference samples. Single-candidate exports can be imported as-is; merged multi-candidate
exports cannot recover discarded paired measurements. Keep private corpus data restricted.

~~~sql
SELECT run_id, file_path, method,
       avg(time_s), stddev_samp(time_s), min(time_s), max(time_s)
FROM benchmark_measurements
WHERE phase = 'measured'
GROUP BY run_id, file_path, method;
~~~

## Aggregation and reruns

The caller supplies required corpus versions and optional explicit run IDs.
Configuration lives in code or service configuration, not database plan tables.
For unspecified inputs, select the latest successful, non-invalidated run for the
candidate and exact corpus version, ordered by created_at DESC, id DESC.

Before calculating, validate candidate identity, required corpus coverage (one run per
corpus), method success/determinism and compatible engine, incumbent and benchmark
settings. Missing or incompatible selected inputs cause an explicit failure.

Save the aggregation and all input links atomically after validation/calculation succeed.
calculator_version identifies the implementation/rules used, not a mutable "latest".
Metrics are raw_bytes, incumbent_bytes, bytes, incumbent_seconds and parse_seconds;
ratios are derived. Linked runs identify the corpora involved.

A rerun B2 can be combined with existing A1 while the old aggregate retains A1/B1.
Later invalidation does not automatically rewrite aggregates or scores; the operator/
service must select replacement evidence and recalculate.

submissions.aggregation_id selects the current aggregate; score_snapshots.aggregation_id
preserves the historical score's input. Both are nullable for existing workers.
Foreign keys/checks enforce references, timing values and basic shape. Compatibility,
projection consistency, completeness, source ownership and immutability are application
responsibilities. No database triggers implement a workflow.

This migration does not implement ingestion/aggregation or change existing workers'
JSON summary flow. Existing score snapshots remain attached to weight publications.

## Applying or reversing

From the repository root (just loads .env):

~~~sh
just db-migrate
just db-downgrade 0001
~~~

Downgrade drops benchmark evidence and the two aggregation reference columns.
Existing submissions, registrations, scores and weight publications remain.
Export any benchmark evidence you need before downgrading.

If the earlier experimental 0002 is applied, downgrade with that original migration
file BEFORE replacing it, then run just db-migrate. Both versions use the same ID;
upgrading an already-applied old 0002 does not replace its schema.
