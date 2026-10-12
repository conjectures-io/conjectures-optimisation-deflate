# DEFLATE competition: findings

Status: **in progress** (2026-10-12). Numbers below are final for what they cover; sections
marked *pending* are not. Method and decisions: [PLAN.md](PLAN.md),
[PREREGISTRATION.md](PREREGISTRATION.md). All timing is on s66 (AMD EPYC 9354, KVM,
8 vCPU), one pinned core, interleaved rounds. Sizes are deterministic.

## 1. The competition at a glance (PROD database, 2026-10-12)

| | |
|---|---|
| Duration | 2026-09-28 18:15 → 2026-10-12 (open) |
| Miner submissions | 661: 648 accepted, 11 rejected, 2 in flight; plus 10 operator baselines |
| Who | 625 hotkeys, **36 coldkeys** (one registration per accepted submission) |
| Accepted per day | 17, 92, 35, 49, 40, 48, 45, 41, 59, 54, 49, 45, 26, 26, 22 |
| α paid (submission bounty) | **7,681 α** to 480 hotkeys / 30 coldkeys; top-2 coldkeys **54%**, HHI 0.195 |
| Frontier size | 7 → 23 → 48 → 72 → 89 → **101** points (09-28 … 10-12) |
| Ever on the frontier | **533 of 648** accepted submissions |
| Official records | smallest output #644 (9,818,301 B on stage 1 + 2); fastest #613 (0.342× the incumbent) |
| Reproducibility | 634 of 634 rerun submissions byte-identical to their gate reports |

Behaviour groups (identical per-file sizes on c1+c2+c3): 654 rerun submissions form 647
groups, so near-duplicate resubmission is rare. The frontier grew because many distinct
parsers each held a thin slice of the time axis.

## 2. Overfitting: what the held-out corpora say

- c1 and c2 are twins (Spearman of gain 0.998 throughout). They cannot detect tuning to
  their shared distribution.
- c3 (out of distribution) can. The c1→c3 Spearman of gain fell **0.977 (09-29) → 0.961
  (10-02) → 0.759 (10-12)**.
- Per day, the median retention of the c1 gain on c3 dropped to 0.10 on 10-07 and to −0.50
  on 10-08. The `public-corpus-gap` flag went from about 15 to 37–44 a day from 10-06.
- The recent top-compression cluster (#636, #644, #649, #639, #645, #655) **does
  generalise** (117–126% kept on c3), but it is converged micro-tuning. c1 improved by
  about 4 KB after 10-02; c3 did not improve at all. The best c3 results are #243/#241/#239
  (10-02) and #112 (09-29).
- The recent mid and fast frontier is where overfitting sits. Families collapse on single
  c3 files: `app.dex` (−68%), `security.evtx` (−492%), `backward65536.bin` (−9,802%).
- Scoring c3 as well would have moved **79.5%** of pay. Timing on s66 instead of PROD
  moves 32.7%.
- **The 09-30 dossier's showcase parsers #125 and #82 collapse on c3** (−2.9%, −2.2%) and
  on C4. The dossier's headline needs replacing.

## 3. Where the existing libraries sit (same host, same harness)

Fixed 16384-token blocks (the competition's encoder) for the parsers; each library with
its own encoder. Hierarchical geometric means over c1, c2, c3 (categories equal), relative
to the incumbent:

| method | size | time | on the joint frontier |
|---|---|---|---|
| libdeflate-1 | 1.077 | 0.15 | yes |
| libdeflate-6 | 0.981 | 0.32 | yes |
| libdeflate-9 | 0.962 | 0.74 | yes |
| #196 | 0.943 | 1.51 | yes |
| #113 | 0.942 | 1.97 | yes |
| #243 | 0.936 | 3.74 | yes |
| libdeflate-12 | 0.930 | 5.42 | yes |
| #140 | 0.937 | 3.88 | no |
| #112 | 0.936 | 6.83 | no |
| zlib-9 | 0.977 | 1.64 | no |
| miniz_oxide-9 | 0.981 | 1.52 | no |
| zlib-6 | 0.991 | 0.82 | no |
| #125 (dossier) | 0.996 | 0.46 | no: libdeflate-6 is smaller and faster |

- **The fast end belongs to libdeflate.** libdeflate-6 is smaller *and* faster than every
  fast miner submission. The gap is the price of the provable Rust subset: byte-by-byte
  comparison loops, bounds checks, no word-at-a-time matching. Removing overflow checks
  (which the proof makes redundant) changes nothing measurable.
- **The middle belongs to the miners.** #196, #113 and #243 beat zlib-9 and miniz_oxide-9
  outright, and sit between libdeflate-9 and libdeflate-12.
- **libdeflate-12 has the smallest output, and it is not the parse.** Its parse through
  the competition's encoder is *larger* than the best miners' (c1: 4,891,390 B vs #243
  4,867,836 B). Its own encoder's adaptive block splitting is the difference. With adaptive
  blocks (the arena's `Blocks::Adaptive`), every parse gets 0.7–0.9% smaller, and
  libdeflate-12's parse through *our* encoder beats libdeflate-12 itself (4,847,034 vs
  4,849,505 B on c1).

## 4. The fresh holdout (C4) and the robustness screen (stage 1: public sources)

C4: 905 files, 50.5 MiB, seven categories sampled from real-world data no miner saw (web
assets, large files, genomics, PNG scanlines, archive members, this host's logs, JSON
messages). Set A: 38 adversarial and edge inputs, up to 64 MiB.

Per category on C4 (size vs incumbent), the best miners match libdeflate-12 nearly
everywhere except two categories:

| category | libdeflate-12 | #112 | #140 | #243 | #355 | libdeflate-9 | zlib-9 |
|---|---|---|---|---|---|---|---|
| archive | 0.978 | 0.976 | 0.978 | 0.977 | 0.978 | 0.994 | 0.996 |
| genomics | 0.870 | 0.871 | 0.877 | 0.891 | 0.907 | 0.926 | 0.919 |
| image | 0.891 | 0.892 | **0.974** | 0.934 | 0.961 | 0.955 | 0.957 |
| large | 0.927 | 0.927 | 0.930 | 0.929 | 0.930 | 0.956 | 0.982 |
| logs | **0.806** | 0.837 | 0.829 | 0.868 | 0.860 | 0.844 | 0.856 |
| messages | 0.941 | 0.943 | 0.947 | 0.946 | 0.945 | 0.967 | 0.972 |
| web | 0.977 | 0.977 | 0.979 | 0.978 | 0.979 | 0.993 | 0.995 |

Robustness failures found (real, not artefacts):

| failure | parsers |
|---|---|
| Compression collapses above ~16 MB (+71% on 64 MiB) | #140, #280, #473 |
| Superlinear time on repetitive input | #112 (76× on period-1), optimal-iter (72× on Fibonacci), #113 (27×), #252 (9×) |
| Misfires on fresh content | fast cluster #88/#34/#33/#57/#61/#23 (logs, −70–80%), #239 (Webster slice +25%), #120 (PNG scanlines +44%), #196, #148 |
| Known c3 collapses | #87, #125 (`app.dex`) |

The pre-registered screen, applied literally, passes 3 of 51 parsers (#55, #521, #85) and
fails the incumbent: two of its rules measure the shared encoder (it cannot store a block
with any match in it, so every parser expands random data) and degenerate inputs (1 MB →
1 KB, where a few KB is "+300%"), not the parsers. The revised screen (deviations 3–4,
recorded before the final selection) passes 18 of 51. Both are reported.

### The most recent submissions, on fresh data

Stage 1b ran every PROD-only candidate: the recent general-frontier groups, the five best
c1 submissions, the fastest official frontier point and the four withheld frontier points.

- **The official record-holders do not generalise.** #644 (smallest output on stage 1 +
  2, 10-11), with #636 and #635, is **0.996** of the incumbent on C4 (it keeps 7% of its
  c1+c2 gain; overfit index +0.93) and 11% *worse* than the incumbent on logs.
- **The 10-11/12 best-on-c1 cluster** (#649, #655, #645, #639) is 0.940 on C4: larger
  than #243 from 10-02 (0.931) at 12.5× the incumbent's time against 3.6×.
- **A >16 MB compression collapse runs through a lineage**: #140 (09-30), #280, #473,
  #644/#636/#635 and #649/#655/#645/#639 all lose 71% on the 64 MiB input. No competition
  file was larger than 1.5 MB, so the record-holders inherited a defect nobody could see.
- **The fast end of the official frontier is unusable off-corpus**: #632 (fastest, 10-11)
  is 33% larger than the incumbent on C4; the withheld #562 is 3.1× larger (18× on logs);
  all four withheld frontier points (#405, #518, #562, #638) fail on c3.

## 5. Selection across the frontier

Revised screen, pre-registered selection rule (fastest, smallest, three log-spaced
between; ties go to the earlier submission). Size and time are relative to the incumbent
on C4; overfit = 1 − gain(C4)/gain(c1+c2), negative means it does *better* off-corpus.

| point | submitted | size (95% CI) | time | overfit |
|---|---|---|---|---|
| #55 | 09-29 | 0.990 (0.982–0.999) | 0.61× | −0.07 |
| #232 | 10-02 | 0.955 (0.943–0.967) | 1.11× | +0.10 |
| #657 | 10-12 | 0.950 (0.944–0.956) | 1.44× | +0.05 |
| #355 | 10-05 | 0.936 (0.928–0.944) | 2.45× | −0.14 |
| #243 | 10-02 | 0.931 (0.918–0.943) | 3.57× | −0.22 |

The other frontier points that pass: #653, #521, #360, #296, #85, #444. Under the strict
screen only #55, #521, #85 pass; #85 (09-29) is within 0.0002 of #355's size at 1.88×.
The scenarios run the five above, #85 and #521, and three contrasts: #649 (best c1),
#632 (fastest official), #125 (the 09-30 dossier).

For context, on C4 libdeflate-12 is 0.911 at 7.3× and libdeflate-9 0.946 at 0.73×: with
the competition's fixed blocks, the selected points sit between them.

## 6. Real-world scenarios S1–S7

Parsers run with the arena's adaptive blocks (what a production encoder would use);
sizes are hierarchical geometric means per scenario, relative to zlib-6 unless noted;
"time" is the same mean of per-file time ratios, MB/s is total input over total time.

### S1 static web precompression (13,268 files, 345 MB; gzip framing)

| method | size | time | MB/s | total bytes |
|---|---|---|---|---|
| libdeflate-12 | 0.9747 | 5.83 | 4.8 | 71,264,203 |
| libdeflate-12's parse, our encoder | 0.9745 | – | – | 71,222,645 |
| #243 | 0.9753 | 6.32 | 6.4 | 71,254,175 |
| #355 | 0.9760 | 4.55 | 12.0 | 71,426,971 |
| #649 (best c1) | 0.9766 | 12.36 | 3.3 | 71,858,367 |
| #657 | 0.9789 | 3.19 | 22.3 | 71,754,818 |
| #85 | 0.9791 | 3.15 | 15.0 | 71,849,882 |
| #521 | 0.9854 | 2.37 | 26.5 | 71,988,911 |
| #232 | 0.9877 | 1.64 | 20.9 | 71,887,047 |
| libdeflate-9 | 0.9923 | 0.89 | 32.2 | 74,177,845 |
| zlib-9 | 0.9966 | 1.09 | 17.7 | 74,797,839 |
| libdeflate-6 | 0.9986 | 0.63 | 104.3 | 75,595,435 |
| miniz_oxide-9 | 0.9999 | 1.40 | 19.7 | 74,983,061 |
| zlib-6 | 1.0000 | 1.00 | 41.9 | 75,535,808 |
| incumbent | 1.0000 | 1.60 | 28.6 | 76,033,002 |
| #55 | 1.0024 | 1.45 | 46.8 | 75,584,785 |
| #125 (dossier) | 1.0030 | 1.39 | 50.4 | 75,263,507 |
| #632 (fastest official) | 1.4328 | 1.12 | 63.0 | 105,782,179 |

- #243 ties libdeflate-12 (smaller in total bytes, 0.06% larger per file) with higher
  throughput on large files; #355 gets within 0.13% of it at 2.5× the throughput.
- Web assets leave little: the best is 2.5% under zlib-6.
- Per-call cost shows on small files: #55 has more throughput than zlib-6 but is slower
  per file (zeroing its tables on every call).
- *Pending:* zopfli, 7-Zip and gzip -9 sizes.

*Pending:* S2–S7.

## 7. Lessons for the next competition

*Pending; collected so far:*
- A held-out twin of the public corpus detects nothing; rotate genuinely different
  private corpora, and do not publish their aggregates (c3's became an oracle).
- Include tiny files and files far larger than the corpus maximum: the 1.5 MB ceiling hid
  a >16 MB compression collapse and quadratic parsers.
- Add a do-no-harm per-file constraint to the score; average-only metrics paid parsers
  that lose 70% on one format.
- Fix the scoring hardware in the rules: s66 vs PROD timing moves a third of the pay.
- The fixed block size kept the competition about the parse, but it hides 0.7–0.9% that
  any production use gets back; a second slot for the encoder, or adaptive blocks in the
  shared encoder, would make the results directly comparable with libraries.
- The proof gives correctness, not compression or speed guarantees; robustness needs its
  own tests.
