# Benchmarks and corpora

The public scoring corpus is `corpus-stage1`. A validator also uses a held-out
`corpus-stage2`; standalone `just bench` uses the configured public default.
Both are distributed as corpus bytes, so local measurements use a stable input
even when upstream source URLs change. `validator/corpora.toml` lists configured
corpora and their visibility. `just corpora` reports the local configuration.

## Measure a parser

```bash
just corpus-pull
just bench my-submission
just bench my-submission --corpus corpus-stage1
just bench-report
```

`just bench` is a local comparison against the configured incumbent, not an
official result. It does not establish proof acceptance or admission. For the
full local gate with only the public corpus, use
`VERIFY_CORPUS=corpus-stage1 just check my-submission`. For current official metrics,
see the [competition page](https://conjectures.io/competitions/deflate).

`just bench-db` and `just bench-import` persist measurement evidence; see
[benchmark storage](BENCHMARK_STORAGE.md). The validator's aggregation and
admission rules are in [scoring](SCORING.md).

## Corpus management

`just corpus-pull` fetches the public corpus and fetches the held-out corpus
when the checkout has access. The held-out bytes and per-file measurements must
remain private. A miner does not need the source pool to benchmark locally.

The source pool under `data/benchmark/sources/` is only needed to build a new
corpus. Its upstream inputs can drift, so a fresh download may not reproduce
published corpus bytes. The available commands in this checkout are:

```bash
scripts/fetch-corpus-sources.sh
just corpus-verify
.venv/bin/python scripts/make-benchmark-corpus.py --stage 1
.venv/bin/python scripts/make-benchmark-corpus.py --stage 2 --seed <private-seed>
```

Run `just corpus-verify` only after the source pool exists. A verification
failure can reflect upstream drift; the distributed corpus bytes remain the
reference. The `just corpus` recipe is a separate legacy builder for
`corpus-initial` and refuses to replace that directory without `--force`.

For source provenance and licences, see [Corpus sources](CORPUS-SOURCES.md).
