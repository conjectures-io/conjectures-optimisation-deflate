# Validator guide

This guide is the entry point for operating the competition validator. The
[competition page](https://conjectures.io/competitions/deflate)
is the source for current published rules and official metrics.

## Start and operate

Use [startup](STARTUP.md) for host prerequisites, corpora, environment settings,
and process lifecycle. Use [operations](OPERATIONS.md) for database setup,
platform integration, wallet and chain behavior, monitoring, and recovery.

The service uses a database and separate gate, chain watcher, and weight setter
workers. `just up`, `just status`, `just logs`, and `just down` manage the local
stack. `just corpus-pull` fetches the public corpus and, where access is
available, the held-out corpus. Review `.env.example` and
`validator/corpora.toml` before starting a validator.

## Verification and scoring

[Verification](VERIFICATION.md) describes the submission gate, its private
workspaces, stage commands, and confinement. [Scoring](SCORING.md) describes
aggregation, admission, and weight calculations. [Benchmark storage](BENCHMARK_STORAGE.md)
covers persisted measurement evidence. Use `just weights-preview` to inspect
the current local calculation without setting chain weights.

For corpus distribution and local measurement commands, see
[benchmark and corpora](BENCHMARK.md).
