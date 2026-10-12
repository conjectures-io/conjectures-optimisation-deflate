# DEFLATE competition wrap-up plan

Status: in progress, 2026-10-12. Decisions are in §8. Sources: PROD API and s66 reruns (`/var/www/competition-dashboard/reruns-operator/prod.json`, generated 2026-10-12 09:53 UTC), this repo's `results/` and `docs/`, the launch dossier (`../deflate-launch-dossier-2026-09-30`), and the competition repo `conjectures-optimisation-deflate` at origin/main 6bf303f.

The goal has three parts:
1. **Summarise the competition's results.**
2. **Choose the submissions that are best in general**, not only on the corpora they were scored on.
3. **Test those submissions in a few real-world scenarios** against existing DEFLATE implementations. This needs adapters that turn a one-shot parser into a streaming compressor.

---

## 1. Where things stand

### 1.1 What a submission is

- A submission is `parse(input: &[u8], out: &mut [u32]) -> usize`. It is a proved-correct LZ77 parser over the **whole buffer in one call**. It emits tokens: a literal is `t < 256`; a match is `2^24 + (dist-1)*256 + (len-3)`, with `dist ≤ 32768` and `3 ≤ len ≤ 258`.
- The harness `validator/measure` loads each parser via `dlopen` through one C-ABI symbol, `slot_parse(input, len, out, cap)`.
- It hands the parser a token buffer of 4 bytes per input byte.
- A **shared trusted encoder** turns the tokens into raw DEFLATE (`validator/measure/src/deflate.rs`). It cuts fixed blocks of 16,384 tokens, chooses stored, fixed or dynamic per block, and builds Huffman codes by package-merge. Block splitting is deliberately not part of the competition.
- **Score.** There are two axes:
  - the mean of per-file compressed %;
  - the mean of per-file time ratios against the incumbent (`lazy`, 32-deep chains).

  Both are measured on corpus-stage1 (public) and corpus-stage2 (held out). The two corpora come from the same distribution and each has 28 files of 12 KB to 1.5 MB. Only the Pareto frontier is paid.
- **Correctness is proved, not tested.** Every accepted parser's tokens decode back to its input. That is the one property no competing DEFLATE implementation can offer. It also means any adapter we write must not be the weak link.

### 1.2 Numbers (PROD, 2026-10-12)

| | |
|---|---|
| Submissions that passed the gate | 648 (638 miner + 10 baseline); latest id 659 |
| Official frontier | 104 points, 104 hotkeys |
| Rerun on c1/c2/c3 by s66 | 644; 634 byte-exact against the gate reports, 0 mismatches |
| Incumbent `lazy` | c1 5,130,834 B · c2 5,218,788 B · c3 5,771,125 B |
| Best c1 bytes today | #649, 4,863,494 B (−5.2%), t 6.8 |
| `optimal-iter` baseline | c1 5,011,989 B (−2.3%), t 9.2 |
| Fastest frontier | #632, t ≈ 0.43, 2.5–4.4% *larger* than the incumbent |

### 1.3 Overfitting: what the data already shows

**Spearman correlation of gain, c1 against c3, has fallen as the competition went on:**

| date | correlation |
|---|---|
| 09-29 (72 parsers) | 0.977 |
| 10-02 (174) | 0.961 |
| 10-12 (644) | **0.759** |

c1 against c2 stays at 0.998. That is expected, since c2 is a twin of c1 and cannot detect distribution tuning.

**Per-day retention ("kept" = c3 gain ÷ c1 gain).** The median dropped to 0.10 on 10-07 and to −0.50 on 10-08. The `public-corpus-gap` flag (c1 gain beats c2 gain by ≥ 0.5 pp) rose from about 15 a day to 37–44 a day from 10-06.

**The official frontier on c3.** Of its 104 points:
- 52 `collapses` (kept below 50%);
- 73 `pathological-file` (some c3 file at least 20% worse than the incumbent);
- 27 `generalises` (kept at least 90%).

**The recent submissions split three ways:**
- **High-ratio cluster** (#636, #644, #649, #639, #645, #655; 10-11 and 10-12). These *generalise* (117–126% kept), but they are converged micro-tunings. c1 has improved by about 4 KB since 10-02, while **c3 has not improved since 10-02**:
  - The best c3 mean_pct is #243 (and #241, #244, #239), all from 10-02 at t 3–5.
  - The best c3 bytes is #112, from 09-29.
- **Mid frontier** (t 0.5–3.3). Two families collapse:
  - an `app.dex` family (−68%; ids 383–566 and 647);
  - an evtx, pgpage and dbf family (−492%, −118%, −113%; e.g. #615, #624, #642, #650, #651).
- **Fast end** (#632, #612, #627, #626, #619; t ≈ 0.43). They blow up on window-trap and binary files:
  - `backward65536.bin` −9,802%;
  - `geo.protodata` −593%.

**Scoring sensitivity:**
- Scoring c3 as well would move **79.5%** of pay, and 69 frontier points would leave.
- Using s66 times instead of PROD times moves **32.7%** of pay. Time rankings at the fast end depend on hardware.

**Dossier headlines that don't hold up.** The 09-30 dossier's showcase parsers, #125 ("2.30× faster than miniz_oxide-9") and #82, both **collapse on c3** (−2.9% and −2.2%). Any external write-up must replace them.

**c3 is no longer a clean holdout.** Its per-submission aggregates have been public in `/reruns/prod.json` since about 10-02, so miners could use them as an oracle. That leaves c3 as a strong *diagnostic*, but the final selection needs a fresh, never-published corpus (C4, §3.2).

### 1.4 Gaps

1. **No reference measurements anywhere.** No miniz_oxide, zlib, zlib-ng or libdeflate numbers exist on s66 for c1, c2 or c3 (`rerun.py` runs with `--no-bars`). The only comparison is the dossier's laptop run on stage 1:
   - libdeflate-12: 33.70% at 6.9×;
   - miniz_oxide-9: 34.84% at 1.36×;
   - incumbent: 35.38%.

   Today's best miners are in the same range as libdeflate-12, on an encoder with no adaptive block splitting. This must be measured on one host.
2. **No large inputs.** The largest scored file is 1.5 MB, so nothing has measured scaling, memory (4 B per input byte for tokens), or streaming.
3. **Current frontier sources are only on PROD.** s66 deletes the PROD-pushed copies after measuring them (`imported.json` keeps only hashes). The 4 withheld ids (405, 518, 562, 638) never arrived.
4. **The encoder is not production-grade.**
   - Package-merge clones vectors per package.
   - The encoder is about 56% of #125's total time.
   - Fixed 16K-token blocks cost ratio against libdeflate and zopfli block splitting.
5. **Rights.** Neither the competition repo nor the miner manual says what licence miners grant on `parse.rs` or `Parse.lean`. This must be settled before winners are published or packaged.

---

## 2. Phase 0: freeze and snapshot (1–2 days; PROD steps are the operator's)

1. **Set a cutoff** (submission id and timestamp) for the evaluation. Decide whether submissions close or stay open; if they stay open, the evaluation is a snapshot. Announce it.
2. **PROD export (operator).**
   - Take a `pg_dump` of the deflate DB.
   - Export `submission_files` for *all* accepted submissions as `{id, hotkey, coldkey, submitted_at, sha256, parse.rs, Parse.lean}`.
   - Export the gate reports (`benchmark_*`, `gate_results`) and the `weight_sets` / `score_snapshots` history (for the pay and frontier timeline).
   - Store it encrypted in a private location (e.g. a new private repo `conjectures-deflate-wrapup`, or the s66 operator area with mode 0700). Do **not** reuse the inbox path, which deletes after measuring.
3. **Pin everything** in one manifest:
   - competition commit and verifier fingerprint;
   - corpus SHAs (c1, c2, c3);
   - rustc version;
   - the harness commit.
4. **Re-verify reproducibility.** Rebuild every exported parser and check its bytes against the gate report, reusing `rerun.py`'s verification. Reruns on c1, c2 and c3 already exist for 644 of 648; only the 4 withheld ids are left.

---

## 3. Phase 1: find the best in general (about 1 week)

The selection rules are **written and committed before C4 is run**: thresholds, tiers, metrics, and the C4 hash. Otherwise the selection itself overfits, through the "garden of forking paths".

### 3.1 Candidate pool and deduplication

- Take all accepted PROD miner submissions plus the 10 baselines, about 648 in total.
- **Group them by behaviour.** Two parsers whose token SHA-256 is identical on every file of c1+c3 are the same parser for our purposes. For example, #628, #629 and #640 have identical bytes on all three corpora.
- Keep the **earliest** id as each group's representative (for attribution) and list the members.
- Also cluster by source diff (many submissions are constant tweaks; #125 is #82 with 5 constants changed). That gives a family tree for the summary.

### 3.2 Evaluation corpora

| set | role | notes |
|---|---|---|
| c1 + c2 | in distribution | what miners optimised; already measured |
| c3 | out-of-distribution diagnostic | partly exposed; already measured. Fix before relying on it: replace the 4 grey-licence files and the `app.dex` head (which overstates the effect); keep the window traps as robustness probes, not scored |
| **A**: adversarial / edge set | robustness screen | see 3.3 |
| **C4**: fresh holdout | **primary generalisation metric** | built *after* the freeze, never published until results are out. It contains the real-world scenario data from §5 (web assets, large text, VCF/FASTQ, PNG IDAT streams, archive members, logs) plus natural whole files at natural sizes (Mahoney-style). Licence-clean sources only (see `research-file-type-sources.md`). Avoid sources already in the c1/c2 pool and anything flagged high-exposure (Gutenberg, loghub, Silesia as content). Silesia goes into the scenario runs as a standard reference, not into C4. |

### 3.3 Robustness screen (pass/fail, before ranking)

Measure on c1, c2, c3 and A. Set A covers:
- **tiny inputs:** 1 B, 10 B, 100 B, 1 KiB, 4 KiB;
- **degenerate inputs:** zeros, random, and period 1–4;
- **window traps:** periods 32,769 and 65,536;
- **binary layouts:** DEX-like integer tables and UTF-16;
- **string families:** Fibonacci and Thue–Morse strings;
- **adversarial hashing:** hash-collision patterns for a 3-byte or 4-byte hash;
- **scaling:** a 64 MiB concatenation.

A parser **fails** if any of these hold:
- any file is more than **10%** larger than the incumbent's output (the dashboard flag uses 20%), or larger than stored output plus 0.1%;
- superlinear time: the log-log slope of time against size from 1 to 64 MiB is above about 1.15, or the time on any A input is more than 5× its median time ratio;
- it crashes, times out, is non-deterministic, or its peak RSS is above budget.

Report the screen as a table of reasons. It is a result in its own right: "which tricks are unsafe".

### 3.4 Ranking

- **Gain.** Per file, `size_candidate / size_reference`, with the incumbent as reference. Aggregate as a hierarchical geometric mean: files → source → category, equal weight per category, so neither big files nor one over-represented format dominates.
- **Uncertainty.** A 95% bootstrap confidence interval, resampling sources within categories. Check stability by leaving out one category at a time (Kendall τ against the full ranking).
- **Time.** Measure on s66 only (see §8.4): the harness's interleaved order, 11 reps, 1 warmup, cores pinned, and the fixed control set in every run. Report each parser's time with the run-to-run noise of the control set, because hardware alone moves 32.7% of pay and one host cannot show that.
- **Tiers**, as time ratio against the incumbent on the same host. References are placed on the same axis (§4.4), so each tier also reads as "zlib-6 class", "libdeflate-9 class" and so on:
  - **Fast:** ≤ 1.0
  - **Balanced:** 1.0–3.0
  - **Max:** 3.0–12
- **Selection across the frontier** (§8.6). Pick about 4–6 points spread from the fast end to the max-ratio end of the C4 frontier, each the best candidate that passed the screen in its region. If confidence intervals overlap, prefer the earliest submission. Also publish the Pareto frontier on C4 and on c1+c2+c3+C4 combined, as the "general frontier".
- **Overfit index** per group: `1 − gain_C4 / gain_c1c2`. Show it next to the competition's own ranking. That is the chart that answers whether the recent solutions are overfitted.

**Expected outcome (a hypothesis to test, not a result):**
- the **Max** tier comes from the high-ratio cluster, either the 10-02 family (#243, #241, #239), #112, or the 10-11/10-12 cluster (#636, #639, #649);
- the **Balanced** tier comes from the generalising t 1.5–5 group (#196, #113, #85, #132, #102);
- the **Fast** tier may have no generalising miner at all. Any fast frontier parser that survives the screen would be notable.

---

## 4. Phase 2: real-world harness (about 1.5 weeks)

Build a new crate, `deflate-arena`, in a new repo or in this one. Leave `validator/measure` untouched: it is pinned by the verifier fingerprint. Copy `loader.rs`, `token.rs` and `deflate.rs` from it and keep a test proving the copied encoder is byte-identical to the original.

### 4.1 Parser loading

The arena reuses the `candidate/` crate template and `slot_parse` via `dlopen`, so any submission's source, unchanged, becomes a pluggable parser. It builds once per source SHA, as `rerun.py` does, reusing the existing crates under `/var/lib/competition-reruns/crates/`.

### 4.2 Encoders (back ends)

| id | what | why |
|---|---|---|
| **E0** | the competition encoder, made incremental: it accepts tokens in batches and keeps the bit writer state across calls | parity with the competition's numbers |
| **E0-fast** | same algorithm, with package-merge rewritten without per-package `Vec` clones (index-based boundary package-merge). **Required to produce byte-identical output to E0** on every corpus | the encoder is about 56% of a fast parser's time; without this, real-world speed is unfairly bad |
| E1 *(stretch)* | adaptive block splitting (libdeflate-style symbol-statistics heuristic), plus an option to try block-length candidates | shows how much ratio the competition left on the table by fixing blocks at 16,384 tokens |
| **TX**: token extraction | a raw inflate that records the token stream, i.e. `infgen`-style, about 300 lines of Rust | the **2×2 design**: decode zlib, libdeflate or miniz_oxide outputs back into tokens and re-encode them with E0. That compares **parse quality with the encoder held fixed**, the only fair way to say "this parser beats libdeflate's parser" |

### 4.3 Streaming adapter

Each mode's role and costs:

- **(a) history-prefix (the main one).**
  - **Mechanism.**
    - Keep `buf = history (≤ 32 KiB) ‖ pending input`.
    - Call `parse(buf)` and **commit only the tokens that start at or after `H = len(history)` and before `E − L`**. `E` is the end of `buf`; `L` is the held-back lookahead: 258 for greedy or lazy parsers, larger, e.g. 4 KiB, for DP parsers that plan ahead.
    - A token that starts in the history and runs past `H` is trimmed to a match of the same distance when at least 3 bytes remain after `H`; otherwise those bytes become literals.
    - Uncommitted bytes carry over.
  - **Why it is correct.** Every committed distance is at most the token's position in `buf`, which is within the bytes the decoder already has, and at most 32,768. The output is a valid DEFLATE continuation.
  - **Cost.** Parse work grows by `(32 KiB + L) / chunk`: about +25% at 128 KiB chunks, about +3% at 1 MiB.
  - **No source changes.** It works for any submission.
- **(b) independent chunks.** Each chunk is parsed alone, with no history, as in BGZF or `pigz -i`.
  - Cost: none. This is the exact semantics of BGZF and ZIP entries.
- **(c) `start` offset (not now).** The signature becomes `parse(buf, start, out)`.
  - Cost: every proof has to be redone, so this is a next-competition idea. Mention it in the summary as a recommendation.

**Flush.** The adapter supports:
- **`sync`**: commit everything with `final=true` for the parse, end the block, emit the empty stored block (`00 00 FF FF`);
- **`full`**: as `sync`, and also drop the history;
- **`finish`**.

**Containers.** Raw deflate, zlib (Adler-32) and gzip (CRC-32); `crc32fast` and `adler2` are already vendored. BGZF too (64 KiB members with the BC extra field), so the output works with `samtools`/`tabix`.

**Trust.** The adapter's trimming and commit logic is the only unproved code between a proved parser and the output. Protect it three ways:
1. **Property tests** (proptest): random chunk sizes, random flush points, several parsers (template, lazy, an optimal parser, a fast frontier parser). Round-trip each output through zlib, miniz_oxide and libdeflate.
2. **Fuzzing** with `cargo fuzz`.
3. **Optional proof.** The splice lemma is small: decoding a valid token list for `h ‖ x` from offset `|h|`, with the straddler trimmed, gives `x`. It could be proved in Lean against `Lz77/Spec.lean`, which would let the summary say "end-to-end verified streaming".

**Interfaces.**
- A CLI, `vgzip`: `-c`, `-k`, `-d` pass-through, `--parser <id|tier>`, `--chunk`, `--mode a|b`, `--flush-every`.
- A Rust `Write` implementation, `DeflateEncoder<W>`, so the parsers can be dropped into real programs (an HTTP server handler, a PNG writer).

### 4.4 References

Build every reference from a pinned version with the same compiler flags, one thread, in memory.

| implementation | levels | tier |
|---|---|---|
| zlib 1.3.x (system or vendored `libz-sys`) | 1 / 6 / 9 | all |
| zlib-ng 2.2.x | 1 / 6 / 9 | Fast, Balanced |
| zlib-rs (flate2 backend) | 1 / 6 / 9 | the Rust peer |
| miniz_oxide 0.8 | 1 / 6 / 9 | the Rust peer; the original target of the competition |
| libdeflate 1.2x | 1 / 6 / 9 / 12 | whole-buffer only |
| ISA-L igzip | 0–3 | Fast; x86 only |
| zopfli (15 iterations), ECT, 7-Zip deflate `-mx9` | – | Max / "precompression" |
| pigz `-p1` | -6 / -9 / -11 | streaming large-file reference |

**lzbench cross-check.** Add one lzbench codec wrapper that calls `vgzip`'s C ABI and run lzbench on Silesia. That gives numbers in a third-party harness people already trust.

---

## 5. Phase 3: real-world scenarios (about 1 week of runs and analysis)

Use the selected frontier points plus a handful of contrasts:
- the **best c1 submission**: #649;
- the **fastest frontier submission**: #632;
- a known **collapser**: #125.

The contrasts show what overfitting costs in practice.

| # | scenario | data (licence-clean, pinned) | adapter | competitors | metrics | likely fit |
|---|---|---|---|---|---|---|
| **S1** | **Static web precompression** (`gzip_static`, CDN) | about 200 release bundles from npm packages (MIT/Apache: react-dom, three.js, d3, lodash, bootstrap CSS, monaco), plus generated HTML docs (CPython / Rust docs), SVG icon sets; 1 KB–5 MB | whole buffer | zopfli, ECT, libdeflate-12, zlib-9, 7z `-mx9` | total and geometric-mean bytes; time per MB (zopfli is around 100× slower); decompression MB/s | **Max** tier: the headline candidate |
| **S2** | **Large-file gzip** (`gzip file`) | Silesia full files (6–51 MB), enwik8, a 200 MB tar of a source tree, a 100 MB CSV or SQL dump | (a), 1 MiB chunks; plus whole buffer as a control | gzip(zlib) -6/-9, `pigz -p1`, zlib-ng, igzip -3, libdeflate (whole file) | bytes, MB/s, **peak RSS**, decompression MB/s, chunk-size sensitivity | Balanced / Max; tests scaling the corpora never did |
| **S3** | **BGZF genomics** (`bgzip`) | 1000 Genomes VCF slice, FASTQ, SAM text (open data) | (b), 64 KiB independent blocks | htslib bgzip with libdeflate (levels 1/6/12) and with zlib | file size, MB/s, `tabix` index works | c3 VCF shows a **+20% median gain**, so this is potentially the strongest real-world win |
| **S4** | **PNG IDAT recompression** | Kodak 24 (as PNG), UI screenshots, open icon sets, a few photos | whole buffer on filtered scanlines. oxipng picks the filters once; only the deflater varies. Reassemble and run `pngcheck` | oxipng with libdeflate, zopflipng, ECT, zlib-9 | bytes per image, time | photo.ppm was a weak spot, so this tests the class detectors honestly |
| **S5** | **Archives / many small members** (ZIP/JAR, git objects) | ZIP of CPython `Lib/` (PSF), a JAR, loose objects of a mid-size git repo | (b), per entry | `zip -9`, 7z deflate `-mx9`, advzip `-4`, libdeflate-6/12, git's zlib | total bytes, **per-call latency at 1–64 KiB** | stresses tiny-file blow-ups and per-call fixed cost (the 32K-entry tables are zeroed on every call) |
| S6 | **Log streaming with flushes** | real logs (e.g. our own nginx and pm2 logs from s66 with secrets scrubbed, or loghub; note loghub's exposure), replayed in 4 KiB writes, sync flush every 64 KiB or 1 s | (a) with flushes | zlib -1/-6, zlib-ng -1/-6, miniz_oxide 1/6 streaming, igzip | MB/s per core, flush overhead, ratio | Fast tier; may well show the parsers do *not* win here, and that is a valid result |
| S7 | small messages with context takeover (WebSocket permessage-deflate) | JSON API messages of 100 B–4 KiB | (a) with sync flush per message | zlib with context takeover | bytes per message, latency, memory per connection | adapter overhead dominates; include only as a stress test |

All of S1–S7 are in scope (§8.7). Order: S1–S4 first, then S5–S7.

**Measurement rules for all scenarios:**
- One thread, pinned; median of 11 interleaved reps.
- Report size *including* container overhead.
- Run every output through an independent decoder (zlib and libdeflate inflate, and the real consumer: `gzip -t`, `samtools`, `pngcheck`, `unzip -t`, `git fsck`).
- Record peak RSS with `/usr/bin/time -v`.
- Measure decompression speed: shorter matches or more blocks slow inflate, so the parse is not neutral for decompression.

**The 2×2 table, run on S1 and S2.** For each of {submission tokens, libdeflate-12 tokens, zlib-9 tokens}, encode with {E0, E1, and the library's own encoder}. It answers two questions:
- Is the parse better?
- How much of the remaining gap to libdeflate or zopfli is block splitting?

---

## 6. Phase 4: the summary of results (2–3 days, after Phases 1–3)

The deliverable is an updated dossier: `deflate-final-dossier-<date>/`, built like the 09-30 one (`scripts/build.py` → charts, CSV, `key_figures.json`), plus a short public version. Contents:

1. **The competition at a glance.** Dates, submissions per day, miners and coldkeys, α paid and its concentration (the top 2 operators took 79% by 09-30), frontier size over time, and the gate and admission statistics.
2. **Progress curves.** Best c1 bytes and fastest time over time, with **c3 and C4 overlaid**. This is the chart that shows c1 improving after 10-02 while c3 stays flat.
3. **Generalisation.**
   - The Spearman trend (0.977 → 0.961 → 0.759).
   - Flags and kept-ratio per day.
   - The named mechanisms, with per-file evidence: content-class detectors; 4-byte hash with miss skipping on integer tables; tiny-file blow-ups; window-trap blow-ups; the evtx/pgpage family.
   - The "pay that would move" what-ifs: c3 79.5%, hardware 32.7%.
4. **The robustness screen.** Which groups failed, and why.
5. **The general winners per tier** with confidence intervals and the overfit index, compared against the competition's own frontier. Attribution goes to the earliest member of each group.
6. **Reference placement.** Where zlib, zlib-ng, miniz_oxide, libdeflate and zopfli sit on the same axes, on the same host, with the 2×2 parse-vs-encoder result.
7. **Real-world scenarios S1–S6.** One table and one Pareto chart each, plus an honest verdict ("wins / parity / loses, and why").
8. **Caveats:**
   - fixed encoder;
   - 32 KiB window (the window traps are unbeatable by design);
   - no SIMD;
   - DEFLATE only (no comparison with zstd or brotli beyond one context line);
   - s66 is a VM.
9. **Lessons for the next competition:**
   - rotate private corpora, and never publish their aggregates;
   - include tiny and large files;
   - add a do-no-harm per-file constraint to the score;
   - make the scoring hardware part of the spec;
   - consider a streaming signature (`parse(buf, start, out)`) and an encoder slot.
10. **Correct the 09-30 dossier.** Retire the #125 and #82 headline.

---

## 7. Work breakdown and order

| # | task | depends on | effort | who |
|---|---|---|---|---|
| 0.1 | cutoff decision, announcement | – | – | user |
| 0.2 | PROD export of sources, reports, weight history | 0.1 | 0.5 d | operator (PROD) |
| 0.3 | rebuild all parsers, verify bytes against gate reports | 0.2 | 0.5 d | us (s66) |
| 1.1 | behaviour groups and family tree | 0.3 | 1 d | us |
| 1.2 | set A, plus the c3 fixes (licence and DEX replacements) | – | 1 d | us |
| 1.3 | **pre-registration commit** (protocol, thresholds, C4 hash) | 1.2, 2.x data chosen | 0.5 d | us, user signs off |
| 1.4 | build C4 from the scenario data plus natural whole files | 0.1 | 2 d | us |
| 1.5 | robustness screen, s66 timing, ranking, frontier selection | 1.1–1.4, 2.1 | 2 d | us |
| 2.1 | `deflate-arena`: loader, incremental E0 plus E0-fast (byte-identical test), references, `--bars` on c1/c2/c3 | – | 3 d | us |
| 2.2 | streaming adapter (a)/(b), containers, flush; property tests and fuzzing | 2.1 | 3 d | us |
| 2.3 | TX token extractor and the 2×2 runner | 2.1 | 1.5 d | us |
| 2.4 | `vgzip` CLI, `Write` encoder, lzbench wrapper | 2.2 | 1.5 d | us |
| 2.5 | *(stretch)* E1 adaptive block splitting; Lean splice lemma | 2.2 | 2–4 d | us |
| 3.1 | S1–S4 runs and analysis | 1.5, 2.2–2.4 | 3 d | us |
| 3.2 | S5–S6 (and optionally S7) | 3.1 | 2 d | us |
| 4.1 | final dossier and public summary | all | 2–3 d | us |

Total: about 4 weeks for one engineer. Phases 1 and 2 can run in parallel after Phase 0. The `--bars` reference run (part of 2.1) is cheap, and it is worth doing first because it frames everything else.

**Compute.** s66 (8 vCPU, 31 GiB) is enough for parsing and scenario runs, but it hosts the DEV gate and is a VM, so time it during quiet periods. No second host (§8.4).

## 8. Decisions (2026-10-12)

1. **Cutoff.** Not a concern for this work. The evaluation uses whatever snapshot the PROD export contains.
2. **Rights to miner code.** Out of scope here.
3. **PROD export.** The user exports the PROD database and places it on s66 for research. Its location will be recorded here when it lands.
4. **Timing host.** s66 only, with no second host. It ran every earlier rerun, which keeps the numbers comparable. Noise controls, since s66 is a VM shared with the DEV gate and the rerun timer:
   - check for gate or rerun activity before each timing run, and record it;
   - pin cores with `taskset`;
   - run 11 interleaved reps;
   - repeat one fixed control set (incumbent, `mo-lazy`, `optimal-iter`, miniz_oxide-6, libdeflate-6) in every run, so drift between runs is visible;
   - report noise from repeated runs of the control set, in place of a second host.
5. **c3.** Leave publication on `/reruns/` unchanged. Use c3 as a diagnostic; C4 stays the private holdout.
6. **The outcome to report.** A **selection of a few solutions spread across the Pareto frontier**, not one winner and not a strict per-tier table. The tiers in §3.4 become the spacing guide: pick about 4–6 points from fast to max-ratio, each the best generalising candidate in its region of the C4 frontier.
7. **Scenarios.** All of S1–S7.
