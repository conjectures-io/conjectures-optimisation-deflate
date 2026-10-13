# Competition wrap-up: real-world evaluation

Plan and decisions: [`docs/wrapup/PLAN.md`](../docs/wrapup/PLAN.md). Methodology and how to reproduce every result: [`docs/wrapup/METHODOLOGY.md`](../docs/wrapup/METHODOLOGY.md) (`scripts/reproduce.sh <stage>...`).

Nothing here is part of the gate. `validator/` (and its verifier fingerprint) is
untouched: `arena` includes the pinned `token.rs`, `loader.rs` and `deflate.rs`
from `validator/measure/src` by path, and its own encoder is tested to be
byte-identical to the pinned one.

## `verified-deflate/`: the library

The usable result: a Rust crate and a `vgzip` command that compress gzip, zlib, raw
DEFLATE and BGZF with three of the competition's proved parsers (#521, #85, #243 as
levels Balanced, High, Max). Output is standard DEFLATE. See
[`verified-deflate/README.md`](verified-deflate/README.md).

## `arena/`

A Rust crate and CLI:

| piece | what it does |
|---|---|
| `encoder` | the pinned encoder made incremental: same 16384-token blocks and bytes, plus sync/full flush. `Huffman::Fast` is the same package-merge without per-package clones (same lengths, about half the encode time) |
| `stream` | `compress_whole` (the competition's setting); `compress_independent` (chunks with no history: BGZF, ZIP entries, `pigz -i`); `HistoryCompressor` / `compress_stream`, which carries 32 KiB of history across chunks without changing the parser (`parse(history ‖ chunk ‖ lookahead)`, commit only the tokens past the history, trim a match that straddles it) |
| `container` | gzip, zlib, BGZF framing |
| `inflate_tokens` | an inflater that returns the token stream: another compressor's parse, for re-encoding with the shared encoder |
| `reference` | miniz_oxide, libdeflate, system zlib, zopfli; zlib streaming with sync flushes |
| `verify` | round trips through miniz_oxide, zlib and libdeflate |
| `parser` | builds a `parse.rs` the way the gate does (the `candidate` template, the pinned toolchain) and loads it through `slot_parse` |

```bash
cd wrapup/arena
cargo test --release
cargo build --release

# Build parsers (cached by source sha256 under --work).
target/release/arena build --validator ../../validator --work /tmp/crates path/to/parse.rs

# Benchmark: interleaved rounds as the gate does; JSONL out (meta line, then one row per file and method).
target/release/arena bench --corpus DIR --label c1 --mode whole \
  --method slot:incumbent=../../validator/incumbent/parse.rs --validator ../../validator --work /tmp/crates \
  --method ref:zlib-6 --method ref:libdeflate-12 --method retok:libdeflate-12 \
  --reps 11 --warmup 1 --out results.jsonl

# Compress a file with a parser (vgzip).
target/release/arena gz --method slot:p649=... --mode stream:1m --format gzip IN OUT.gz
```

Modes: `whole`, `stream:CHUNK[:FLUSH]`, `indep:CHUNK`, `bgzf`. Methods: `slot:NAME=PATH`
(`parse.rs` or a built `.so`), `builtin:NAME` (reference examples linked in, for local
checks), `ref:SPEC`, `retok:SPEC` (that reference's parse through the shared encoder).
