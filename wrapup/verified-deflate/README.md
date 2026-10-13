# verified-deflate

gzip, zlib and raw DEFLATE compression whose LZ77 parsers are **proved correct in
Lean**: for every possible input, the tokens the parser emits decode back to that
input. The parsers are three submissions from the conjectures.io DEFLATE competition
(28 September – 12 October 2026), chosen by an out-of-sample evaluation of all 648
accepted submissions ([docs/wrapup/FINDINGS.md](../../docs/wrapup/FINDINGS.md)).

The output is ordinary DEFLATE. gunzip, zlib, browsers, Python's `gzip`, `unzip` and
samtools read it unchanged; nothing new is needed to decompress.

## Use it

### Command line

```bash
cargo install --path wrapup/verified-deflate      # installs `vgzip`

vgzip -9 site.js                  # site.js -> site.js.gz (like gzip)
vgzip -k --best *.css *.html      # keep the originals
tar c logs/ | vgzip > logs.tar.gz # stdin to stdout
vgzip --bgzf -c calls.vcf > calls.vcf.gz   # BGZF for samtools/tabix
vgzip -d site.js.gz               # or use plain gunzip
```

Levels follow gzip: `-1`…`-3` (or `--fast`) Balanced, `-4`…`-6` High (default), `-7`…`-9`
(or `--best`) Max. `-c`, `-k`, `-f`, `-d`, `-v` behave like gzip's.

### Rust

```toml
[dependencies]
verified-deflate = { git = "https://github.com/conjectures-io/conjectures-optimisation-deflate", branch = "wrapup/real-world-eval" }
```

```rust
use std::io::Write;
use verified_deflate::{GzEncoder, Level};

let mut gz = GzEncoder::new(std::fs::File::create("out.gz")?, Level::Max);
std::io::copy(&mut std::fs::File::open("in.txt")?, &mut gz)?;
gz.finish()?;
```

Also `ZlibEncoder`, `DeflateEncoder` (raw), `bgzf::BgzfEncoder`, one-shot
`gzip(&data, level)` / `zlib` / `deflate` / `bgzf::compress`, and `Options` for the
chunk size and block mode. Writers flush like zlib's `Z_SYNC_FLUSH` on `flush()`, and
finish on drop (call `finish()` to see errors). The parsers themselves are public in
`verified_deflate::parsers` for anyone who wants raw LZ77 tokens.

Library dependencies: `crc32fast` and `adler2`. The CLI adds `flate2` for `-d`; build
the library alone with `default-features = false`.

## Levels

| level | parser | large files¹ | web assets² | logs³ | one core⁴ |
|---|---|---|---|---|---|
| `Balanced` | #521 (2026-10-08) | 4.3% smaller than zlib-6, 3.5% smaller than `gzip -9` | 1.5% smaller than zlib-6 | 2.5% *larger* than zlib-6 | ≈ 27 MB/s |
| `High` (default) | #85 (2026-09-29) | 4.5% / 3.7% | 2.1% | 14% smaller than zlib-6 | ≈ 15–16 MB/s |
| `Max` | #243 (2026-10-02) | 5.0% / 4.1%; smaller than 7-Zip's deflate | 2.5%: libdeflate-12's size, zopfli within 0.5% | 13% | ≈ 6 MB/s |

For comparison on the same machine: zlib-6 ≈ 39 MB/s, `gzip -9` ≈ 17 MB/s, zlib-ng-6 ≈ 80
MB/s, libdeflate-12 ≈ 5 MB/s, zopfli ≈ 0.2 MB/s.

¹ 824 MB: Silesia, enwik8, CPython and Linux tarballs, GitHub events; streamed in 1 MiB
chunks. ² 345 MB, 13,268 npm and documentation files. ³ 281 MB of journal, nginx and pm2
logs with a sync flush every 64 KiB. ⁴ AMD EPYC 9354 (VM), one pinned core.
Full tables and method: [FINDINGS.md](../../docs/wrapup/FINDINGS.md) §6,
[METHODOLOGY.md](../../docs/wrapup/METHODOLOGY.md). The library's output is tested to be
byte-identical to the benchmark harness that produced these numbers.

## Good for, not good for

Good for: precompressing static web assets (nginx `gzip_static`, CDNs), release tarballs,
backups and archives, rotated logs (`compresscmd` in logrotate), BGZF genomics files,
ZIP/JAR members: anywhere output size matters more than speed and data is compressed
once and read many times.

Not good for: on-the-fly HTTP compression or log shipping where throughput matters
(zlib-ng is 3–14× faster), PNG image data (oxipng and zopflipng are 4–6%
smaller), and many tiny messages each flushed separately (WebSocket-style): every flush
re-parses up to 32 KiB of history, so this is 7–45× slower than zlib there.

## What is proved and what is tested

- **Proved** (Lean 4, checked by the competition's gate): each parser terminates, never
  fails, keeps within its buffers, and its tokens decode back to the input, for every input
  (`LZ77.Obligation` in the competition's `validator/lean/Lz77/Interface.lean`).
- **Tested, not proved**: everything after the parse, i.e. the Huffman coding and block
  splitting (`encoder.rs`, the competition's shared encoder plus adaptive block splitting),
  the chunking that lets a one-shot parser stream (`stream.rs`), and the gzip/zlib/BGZF
  framing. The tests decode every output with miniz_oxide, zlib and libdeflate; the
  benchmark harness that shares this code verified about 2 GB of real data the same way,
  plus 4,767 randomised streaming cases.
- **Defence in depth**: the encoder rejects an illegal token or a token stream that does
  not cover the input, so even a violated contract surfaces as an `io::Error`, never as
  corrupt output.
- **Not claimed**: anything about compression ratio or speed beyond the measurements
  above. The proofs say nothing about either.

## Provenance

The parsers are the competition submissions, byte for byte (`parsers/p<id>/parse.rs`), with
the Lean proofs the gate accepted (`parsers/p<id>/Parse.lean`). The sha256 of each
`parse.rs` equals the `source_sha256` recorded by the competition's database and the
source served by `https://conjectures.io/v1/competitions/deflate/submissions/<id>/source`.

| level | submission | submitted (UTC) | `parse.rs` sha256 | `Parse.lean` sha256 |
|---|---|---|---|---|
| Balanced | #521 | 2026-10-08 10:17 | `32d1fd452496892d44b8c733c2432081a31a86b517278e4769b9c8a9e07b57ef` | `98028b572300bf0e9d4e28212bfb4e834a05b32f12fb780bc4df0b07d030f103` |
| High | #85 | 2026-09-29 08:23 | `97d60f0c53517c4584cbccfed5e5832afde600bf15b5ed8554377812462e51c3` | `a97f738b2939ac9a65f6228c63f53e66e90af73228dd0f32a510260daf65f12d` |
| Max | #243 | 2026-10-02 22:07 | `a83ed10bca126a6b49ea9ed0d43d85eecef064ba97c25e60cea11c02481ee9f2` | `bae536d63b8f87c5808971a2bb2f2c15188da306e878e6f03c07eec8207da388` |

To check a proof yourself, from the competition repository's root with its toolchain set
up (`./setup.sh`, about 15 minutes and 9 GB):

```bash
just check-proof wrapup/verified-deflate/parsers/p243
```

Why these three: they pass the robustness screen at every input size we tried (up to
268 MB in one buffer), #521 and #85 pass even its strictest version, and all three sources
are public. Two other strong submissions are left out on purpose: #355 degrades on single
buffers above 32 MB (harmless behind this library's chunking, but a trap for anyone using
its parser directly), and #657's source is still withheld by the competition.

## Behaviour

- **Streaming**: input is compressed in 1 MiB chunks; each chunk's parse sees the previous
  32 KiB, so the output is one continuous DEFLATE stream with full-window matches.
  Peak memory of `vgzip` is about 26 MiB (Balanced), 21 MiB (High) and 43 MiB (Max),
  the same for a 5 MB and a 108 MB input; most of it is the parsers' own tables.
- **Determinism**: the same input and options always give the same bytes, independent of
  how the input is split into `write` calls. gzip headers carry no name or time.
- **Panics**: none by design. The one-shot helpers write to a `Vec`, which cannot fail;
  an internal error there would be a bug.

## Licence

Not decided. The parsers are the competition miners' work and the competition's terms do
not yet say how they may be redistributed, so this crate is `publish = false` until that
is settled. The surrounding code (encoder, streaming, framing, CLI) is the competition
operator's.

## Development

```bash
cd wrapup/verified-deflate
cargo test --release       # includes byte-equality with the benchmark harness (../arena)
cargo build --release      # target/release/vgzip
```
