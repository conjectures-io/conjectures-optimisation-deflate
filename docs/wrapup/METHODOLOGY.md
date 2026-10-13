# Methodology and reproduction

How every number in [FINDINGS.md](FINDINGS.md) and the blog post was produced, and how to
produce it again. The design rationale is in [PLAN.md](PLAN.md); the selection rules, fixed
before the holdout was run, and every later deviation are in
[PREREGISTRATION.md](PREREGISTRATION.md).

## 1. Questions

1. Which accepted submissions are good *in general*, not only on the corpora they were
   scored on, and how do they spread across the size/speed trade-off?
2. How do those compare with the DEFLATE implementations in real use (zlib, zlib-ng,
   Cloudflare zlib, libdeflate, miniz_oxide, zopfli, 7-Zip, igzip, oxipng), in real jobs?

## 2. Host and timing

| | |
|---|---|
| Host | s66 (`nl-vmv3-heavy`), KVM VM, AMD EPYC 9354, 8 vCPU (1 thread per core), 31 GiB, Ubuntu 24.04.5, kernel 6.8.0 |
| Why this host | it ran the competition's dashboard reruns, so results line up with them; the user chose a single host (PLAN.md §8.4) |
| Pinning | every timed run on one core (`taskset -c 7`); nothing else heavy ran during timed runs (each run logs load and competing processes before and after in `<run>.jsonl.log`) |
| Order | interleaved rounds: every method once per round, file by file (the gate's scheme), so drift hits all methods alike |
| Statistic | median of the measured rounds per file and method, after warm-up rounds |
| Compiler | parsers: the gate's `candidate` crate template and pinned toolchain (`nightly-2026-08-18`, rustc 1.100.0-nightly 8fa1c96cf), `opt-level 3`, `lto fat`, `codegen-units 1`, `overflow-checks true`; the harness: same toolchain |
| What is timed | the whole compression call: parse + encode (+ adapter work); not file I/O, hashing or verification |

Sizes are deterministic; times move between runs (the fixed control set in every run
shows how much). One VM is a limitation: timing on another machine moved 32.7% of
competition pay (FINDINGS §2), so treat time ratios as this host's.

## 3. The harness (`wrapup/arena`)

**Parity with the gate.** The token format, the parser loader and the gate's encoder are
included from `validator/measure/src` by path, not copied. The harness's own encoder is
the same algorithm made incremental, and a test (`incremental_encoder_is_byte_identical_to_pinned`)
checks it produces the gate's bytes for every reference parser on every test input, in
any batching. On c1 the harness reproduces the reruns' byte counts exactly (incumbent
5,130,834 B, optimal-iter 5,011,989 B).

**Parsers** are each submission's `parse.rs`, unchanged, built as the gate builds it and
called through the same C ABI symbol (`slot_parse`). Builds are cached by source sha256.

**Encoders.**
- `Blocks::Fixed`: the gate's 16,384-token blocks. Used for the screen and the selection,
  so they rank parsers exactly as the competition's encoder would.
- `Blocks::Adaptive`: tokens gathered in 128K-token segments, cut recursively at
  1,024-token boundaries where an entropy estimate says the statistics change; a cut is
  kept only if the exact block cost (the same Huffman tables and block-type choice as the
  gate) drops. Used in the scenarios, as any production encoder would split blocks.
- `Huffman::Fast`: the gate's package-merge without per-package allocations; tested to give
  identical code lengths (3,000 random and adversarial frequency tables).

**Adapters** (`stream.rs`), so one-shot parsers can do streaming jobs without changes:
- *whole*: one call over the file (the competition's setting).
- *stream:CHUNK[:FLUSH]*: `parse(history ‖ pending)` with up to 32 KiB of history; commit
  the tokens that start inside the new data and before `CHUNK`; drop tokens inside the
  history; trim a match that starts in the history and crosses into the new data (same
  distance, the remainder if ≥ 3 bytes, otherwise literals); parse the last 4 KiB
  (lookahead) again next call, so no committed match is cut by the buffer end. Optional
  sync flush every FLUSH input bytes. Input arrives in 64 KiB writes.
- *indep:CHUNK*, *bgzf*: chunks with no history; BGZF uses htslib's 0xff00-byte blocks,
  halving a block whose output would not fit in 64 KiB, and the standard EOF block.
- *messages[:WBITS]*: one message per line, a sync flush after each, history capped at
  2^WBITS bytes; a match reaching further back is written as literals.
- *png*: the IDAT stream is inflated to the image's filtered scanlines, recompressed, and
  written back as one IDAT; filters are not changed.

**Verification.** Every output of every method in every run was decoded by miniz_oxide,
zlib and libdeflate (gzip/BGZF framing through zlib's multi-member decoder) and compared
with the input before it counted. A `parse` that panicked, over-reported tokens, or wrote
a token stream that does not cover the input is an error, not a result. The adapters are
also covered by 14 tests and a randomised stress test (`examples/stress.rs`: 4,767
cases of random data, chunk sizes, lookaheads, windows, flushes and block modes, all
clean).

**References**, linked in and called in memory like the parsers:

| reference | version |
|---|---|
| libdeflate (levels 1, 6, 9, 12) | 1.26 (libdeflater 1.26.1) |
| zlib (levels 1, 6, 9) | system zlib 1.3 (Ubuntu 24.04) through flate2 1.1.10 |
| zlib-ng (6, 9), Cloudflare zlib (6) | 2.2.2 (`--zlib-compat`) and the `gcc.amd64` branch, built from source, loaded by path with `RTLD_DEEPBIND` |
| miniz_oxide (1, 6, 9) | 0.8.9 |
| zopfli (15 iterations; PNG only) | zopfli crate 0.8.4 |
| libdeflate-12's / zlib-9's *parse* through the shared encoder (`retok:`) | an inflater that records tokens (`inflate_tokens.rs`), re-encoded with the arena's encoder |

**Command-line tools** (`ext-bench.py`), timed per process, so start-up (about 1 ms) is
included; their MB/s is total input over total time and is only meaningful on S2's large
files. gzip 1.12, pigz 2.8 (`-p 1`), igzip (ISA-L 2.31.0), 7-Zip 25.01 (`-tgzip -mx9`, which
writes the file name into each gzip header), zopfli 1.0.3 (`--i15`), zopflipng 1.0.3 (`-m`),
oxipng 9.1.2 (`-o 4`).

## 4. Data

| set | what | where | public? |
|---|---|---|---|
| c1, c2 | the competition's scored corpora, 28 files each, 15.93 MB | s66 competition checkout | c1 public, **c2 held out** |
| c3 | corpus 3 trial, 54 files, 17.9 MB, sources disjoint from c1/c2 | `conjectures-compression-dashboard-corpus-3` (private repo) | private |
| set A | 38 adversarial/edge inputs: tiny (1 B–4 KiB), zeros, random, periods 1–7, window traps (32,769/65,536/100,000), de Bruijn (k=32 n=4; k=16 n=4 ×16), Fibonacci, Thue–Morse, integer table, float noise, UTF-16LE, runs, and the first 1/4/16/64 MiB of enwik8 | `gen-setA.py`, seed 20261012 | regenerable |
| S1–S7 | scenario data, see below | `fetch-scenarios.sh`, sha256 of every prepared file in `data/MANIFEST.tsv` (17,622 files) | S1–S5, S7 public sources; **S6 private** |
| C4 | the fresh holdout: 905 files, 50.5 MiB, sampled from S1–S7 | `make-c4.py`, seed 420261012; manifest sha256 `870e0590…` | **private** (includes S6) |

Scenario sources (pinned versions; MANIFEST.tsv pins the bytes):
- **S1 web**: 24 npm packages at fixed versions (react, react-dom, three, d3, lodash,
  bootstrap, jquery, vue, chart.js, leaflet, bootstrap-icons, @angular/core, rxjs, moment,
  typescript, highlight.js, katex, mathjax, echarts, pdfjs-dist, ace-builds, font-awesome,
  bulma, alpinejs) plus the Python 3.13 HTML docs; only files a server precompresses
  (js, mjs, cjs, css, html, svg, json, map, xml, txt, d.ts). 13,268 files, 345 MB.
- **S2 large**: Silesia (12 files), enwik8, the CPython 3.13.0 tarball, the first 256 MiB of
  the Linux 6.6 tarball, the first 128 MiB of GH Archive 2024-01-01-15. 824 MB.
- **S3 genomics**: first 192 MiB of 1000 Genomes chr22 VCF and of SRR062634_1 FASTQ; the
  BAM records decoded from the first 48 MB of HG00096's BAM. 569 MB.
- **S4 PNG**: Kodak 24, 15 Fluent UI emoji (3D renders, `main` branch), the Python docs'
  PNGs. 18 MB.
- **S5 archive**: CPython 3.13.0 `Lib/`, the Guava 33.3.1 JAR's members. 58 MB.
- **S6 logs**: this host's journal (28 Sep–12 Oct), nginx access logs, the three largest
  pm2 logs. 281 MB. Never leaves s66.
- **S7 messages**: the first 20,000 GH Archive events (one JSON object per line). 58 MB.

Rerunning `fetch-scenarios.sh` later can produce different bytes where an upstream moves
(the emoji repository's `main`, the host's logs); compare with `MANIFEST.tsv`.

## 5. Candidates

- **Sources**: every accepted PROD submission, from the PROD export (§9.1); 658 sources,
  each checked against the database's `source_sha256`; the 595 also published by the API
  are byte-identical to it.
- **Behaviour groups** (`pool.py`): submissions with identical compressed sizes on every
  file of c1, c2 and c3 (rerun data, `reruns-operator/prod.json`) are one group,
  represented by its earliest member. 654 reruns → 647 groups.
- **Preliminary general frontier**: Pareto frontier over the average of c1, c2, c3 (rerun
  times) among groups with no file more than 20% worse than the incumbent: 32 groups.
- **Stage 1** (public sources): those 23 of the 32 with public sources, plus contrasts #112,
  #140, #196, #113, #85, #125, #87, plus the baselines incumbent, mo-lazy, optimal-iter.
- **Stage 1b** (PROD export): the other 9 general-frontier groups; the best c1 submissions
  #649, #644, #636, #655, #639; the fastest official frontier point #632; the withheld
  frontier points #405, #518, #562, #638 (never rerun, so checked on c1–c3 separately).

## 6. Metrics

- **Size** (and **time**): per file, the ratio to a reference method in the same run;
  aggregated as a hierarchical geometric mean: files within a source, sources within a
  category, categories equally weighted. Sources: on C4 the upstream (npm package, log
  file, …); elsewhere the first path component. 95% intervals: 2,000 bootstrap resamples
  of sources within categories (1,000 in the scenario tables).
- **Reference**: the incumbent for the screen and selection; zlib-6 in the scenarios
  (zlib-9 for PNG, libdeflate-6 for whole-buffer large files).
- **MB/s**: total input over total median time; per-file overheads included.
- **Overfit index**: `1 − gain(C4) / gain(c1+c2)`, gain = 1 − size ratio; negative means
  the submission does better off-corpus.
- **Pareto frontier** on (time, size), lower is better on both.
- **Rank stability**: Kendall τ of the size ranking with one category left out.

## 7. Screen and selection

The rules, as pre-registered, and why two were revised after the stage-1 screen are in
PREREGISTRATION.md. In short, a group fails if, on any file of c1, c2, c3, C4 or set A:
- its output is more than 20% and more than 32 bytes larger than the incumbent's (revised:
  and more than 1% of the input);
- it expands the input (revised: and is also worse than the incumbent);
- it errors, times out (300 s per file, enforced by a one-pass probe before each timed
  run), or is not deterministic;
- its time grows faster than linearly (log-log slope over 1–64 MiB above 1.15), or a
  set A file of at least 64 KiB takes more than 5× its C4 time ratio.

Selection: among passing groups, the C4 Pareto frontier; the fastest point, the smallest,
and the nearest frontier points to 1/4, 1/2 and 3/4 of the way between them in log time;
a near-tie with a neighbour (overlapping size interval, time within 10%) goes to the
earlier submission. Both screens are reported (`select-strict.txt`, `select-revised.txt`).

## 8. Scenarios

| scenario | mode | framing | reps | references | tools |
|---|---|---|---|---|---|
| S1 web | whole file | gzip (+18 B) | 3 | zlib 6/9, zlib-ng 9, libdeflate 6/9/12, miniz_oxide 9, retok libdeflate-12 | gzip -9, 7-Zip, zopfli (1 rep) |
| S2 large, streamed | `stream:1m` | gzip | 3 | zlib 6/9, zlib-ng 6/9, Cloudflare 6 | gzip -6/-9, pigz -6/-9, igzip -3, 7-Zip |
| S2 large, whole | whole buffer | gzip | 3 | libdeflate 6/9/12, miniz_oxide 9, retok libdeflate-12 | (same tools) |
| S3 genomics | `bgzf` | BGZF | 3 | libdeflate 1/6/12, zlib 6, zlib-ng 6 | – |
| S4 PNG | `png` | whole PNG | 3 | zlib 9, libdeflate 12, zopfli i15 | oxipng -o4, zopflipng -m (1 rep) |
| S5 archive | whole file | raw | 5 | zlib 6/9, zlib-ng 6, libdeflate 6/12, miniz_oxide 9 | – |
| S6 logs | `stream:1m:64k` | gzip | 3 | zlib 1/6, zlib-ng 1/6, Cloudflare 6 | – |
| S7 messages | `messages:15`, `messages:12` | raw | 3 | zlib 6, zlib-ng 6 (same window and flushes) | – |

Every scenario run has one warm-up round. Parsers use adaptive blocks; the zlib-family
references flush exactly as the parsers do (sync flush per 64 KiB or per message, and the
same window).

## 9. Reproducing

### 9.1 The PROD export (operator, on PROD)

```bash
D=$(date +%F)
docker exec conjectures_deflate_db pg_dump -U conjectures -Fc conjectures > /tmp/deflate-prod-$D.dump
docker exec conjectures_deflate_db psql -U conjectures conjectures -c "\copy (select s.id, s.hotkey, s.state, s.submitted_at, s.source_sha256, f.name, encode(f.content,'base64') as content_b64 from submissions s join submission_files f on f.submission_id = s.id where s.state = 'accepted') to stdout csv header" | gzip > /tmp/deflate-prod-sources-$D.csv.gz
scp /tmp/deflate-prod-$D.dump /tmp/deflate-prod-sources-$D.csv.gz dev:/incoming/
```

On s66, copy both from `/srv/backups/dbbackup/incoming/` to `/root/deflate-wrapup/prod-export/`.

### 9.2 Setting up s66 (or any x86-64 Linux host)

Needs: rustup with `nightly-2026-08-18`, gcc/g++, make, curl, xz, bzip2, unzip, Python 3.12,
gzip, pigz; the competition checkout with corpora c1/c2 and the corpus-3 checkout. Then:

```bash
mkdir -p /root/deflate-wrapup && cd /root/deflate-wrapup
# s66 cannot fetch from GitHub: ship a commit of this branch from a workstation
git archive --prefix=src/ <commit> | ssh s66 'cd /root/deflate-wrapup && tar -x'
src/wrapup/scripts/reproduce.sh build tools data setA c4 sources stats pool
```

Check that `data/c4/MANIFEST.tsv` hashes to `870e0590…` (the pre-registered C4). If the
scenario data has drifted it will not, and C4 is then a different (still fresh) holdout.

### 9.3 The runs, in order

```bash
src/wrapup/scripts/reproduce.sh bars stage1 stage1b withheld select scenarios report
```

| stage | results | arena revision used originally | wall time |
|---|---|---|---|
| bars | `results/01-bars` | 93c39f3 | 20 min |
| stage1 | `results/02-stage1` | ecd2679 | 40 min |
| stage1b | `results/03-stage1b` | cbd6c52 | 35 min (+ probe) |
| withheld | `results/05-select/withheld` | cbd6c52 | 5 min |
| select | `results/05-select/select-*.{txt,json}` | analysis scripts at aec8067 | 5 min |
| scenarios | `results/06-scenarios` | cbd6c52 (ext-bench c78560e) | 7 h 20 min |
| report | `results/07-report/scenarios.{md,json}` | aec8067 | 5 min |
| stats | `results/04-summary/competition-stats.json` | cbd6c52 | 5 min |

Later revisions change only analysis and reporting, so re-running at the branch head
reproduces every size exactly and every time within run-to-run noise.

### 9.4 What cannot be reproduced outside s66

- c2 is the held-out competition corpus; c3 lives in a private repository.
- S6 is s66's own logs, so C4 (which samples them) is private too.
- Off s66: run everything except S6, and build C4 without the logs category
  (`make-c4.py` skips a missing scenario). The numbers will differ; the method will not.

## 10. Known limitations

- One host, and a VM: time ratios are this host's (§2).
- The screen's thresholds are judgement calls; two were revised after the first screen,
  for reasons recorded before the final selection.
- Set A's scaling series is text only and stopped at 64 MiB; S2 then found two selected
  parsers degrading on larger single buffers of other content.
- Bootstrap intervals are unpaired (each method resampled on its own), so they are wide
  when categories differ a lot; paired comparisons would be tighter.
- The CLI tools' times include process start-up; compare their sizes everywhere, their
  speed only on S2.
- The black-box adapter cannot honour a window smaller than the one a parser was written
  for (S7 at 4 KiB); that result measures the adapter, not the parsers.
