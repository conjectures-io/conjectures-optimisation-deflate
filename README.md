# LZ77 competition

Build a Rust LZ77 parser for DEFLATE and prove in Lean that its tokens decode to the
original input. The validator checks the proof, runs the parser in an isolated
workspace, and measures compression and speed. The competition page is the source
for current rules, rankings, and official metrics:
[DEFLATE competition](https://conjectures.io/competitions/deflate).
Local benchmark output and the example implementations are development aids; their
measurements can change with the corpus, incumbent, machine, and scoring policy.

## Get started

```bash
./setup.sh                 # install dependencies and the verification toolchain
just corpus-pull           # fetch the public benchmark corpus
VERIFY_CORPUS=corpus-stage1 just check miner/template  # local proof gate and benchmark
just --list                # see all available recipes
```

To develop a submission, copy `miner/template/` and edit its two files:
`parse.rs` implements the parser; `Parse.lean` proves the required decoding property.
Run `just bench my-submission` while tuning the parser and
`VERIFY_CORPUS=corpus-stage1 just check my-submission` before submitting. See the [miner guide](docs/MINER.md)
for the full workflow and the [verification guide](docs/VERIFICATION.md) for gate
stages and supported Rust.

## Documentation

| Topic | Guide |
| --- | --- |
| Build, prove, benchmark, and submit | [Miner guide](docs/MINER.md) and [proof manual](miner/MANUAL.md) |
| Set up and run a validator | [Validator guide](docs/VALIDATOR.md), [startup](docs/STARTUP.md), and [operations](docs/OPERATIONS.md) |
| Understand the gate | [Verification](docs/VERIFICATION.md) |
| Use and manage corpora and local benchmarks | [Benchmark and corpora](docs/BENCHMARK.md) |
| Understand reward calculation and admission | [Scoring](docs/SCORING.md) |
| Store and inspect benchmark evidence | [Benchmark storage](docs/BENCHMARK_STORAGE.md) |
| Review source provenance | [Corpus sources](docs/CORPUS-SOURCES.md) |

The repository contains the miner template and proven examples in `miner/`, the
verification and measurement implementation in `validator/`, and operator scripts
in `scripts/`. `justfile` is the command index. The public corpus is fetched into
`data/benchmark/corpus-stage1/`; the held-out corpus requires operator access.
