# Selection pre-registration

Committed before any parser is run on C4. Changing anything below after the C4
results exist has to be recorded as a deviation, with the reason.

## Inputs

- **C4**: `make-c4.py` with seed `420261012`, from the scenario data fetched on s66 on
  2026-10-12 (`/root/deflate-wrapup/data/MANIFEST.tsv`). 905 files, 50.5 MiB, seven
  categories (web, large, genomics, image scanlines, archive members, logs, messages).
  `data/c4/MANIFEST.tsv` sha256 `870e0590a3f00aa85cded5080b5189974b51d4883c490680451032e918179a13`.
  Stays on s66; only aggregates leave it.
- **Set A**: `gen-setA.py` (seed 20261012), scaling series cut from enwik8. 38 files.
- **c1, c2, c3**: the competition's two corpora and the corpus 3 trial, as on s66.
- **Pool**: every accepted PROD submission, grouped by identical per-file sizes on c1+c2+c3
  (`pool.py`); a group is represented by its earliest member. Stage 1 runs the groups on
  the preliminary general frontier (c1+c2+c3, no file worse than −20%: 32 groups on
  2026-10-12), the five best c1 submissions (the "most recent" question), the contrasts
  #112 #140 #196 #113 #85 #125 #87, and the baselines incumbent, mo-lazy, optimal-iter.
  Groups whose source is only on PROD join when the PROD export arrives; nothing else
  about the protocol changes when they do.

## Measurement

- s66 only, `taskset` to one core, interleaved rounds (`arena bench`); whole-buffer mode;
  the competition's fixed 16384-token blocks (`--blocks fixed`, `--huffman fast`,
  byte-identical to the gate's encoder). C4: 5 reps + 1 warmup. Set A: 3 + 1.
- References in every run: libdeflate 1/6/9/12, zlib 6/9, miniz_oxide 9, zlib-ng 6/9.

## Robustness screen (pass/fail)

A group **fails** if, on any file of c1, c2, c3, C4 or set A:
1. its output is more than **20% larger** than the incumbent's, or larger than the input
   plus 0.1% plus 5 bytes per 64 KiB (worse than storing);
2. it crashes, times out (300 s per file), or is not deterministic;
3. its time grows superlinearly: log-log slope of median time over `scale-01m`..`scale-64m`
   above **1.15**, or any set A file with a time ratio above **5×** its C4 time ratio.

A group that passes but has a file more than **10% larger** than the incumbent's is
**flagged** (reported, and ranked after unflagged groups in a selection tie).

## Ranking

- Size: hierarchical geometric mean of bytes / incumbent bytes on C4 (file → source →
  category, categories equal), 95% bootstrap interval (2000 resamples of sources within
  categories). Time: the same for median total time.
- Overfit index per group: `1 − gain(C4) / gain(c1+c2)`, gain = 1 − size ratio.

## Selection: a few points across the frontier

Among groups that pass the screen, take the Pareto frontier on C4 (time, size). Select
**five** points:
1. the fastest frontier point;
2. the smallest-output frontier point;
3. three more: for each of the time targets at 1/4, 1/2 and 3/4 of the way between the
   two in log(time), the frontier point nearest in log(time).

A point whose size interval overlaps its frontier neighbour's and whose time is within
10% of it is replaced by whichever of the two was submitted first (then unflagged
first). Each selected point is reported with its group members, its overfit index and
its worst file.

## Then

The selected five, plus #649 (best c1 bytes), the fastest official frontier point, and
#125 (the 09-30 dossier's showcase), go through scenarios S1–S7.

## Deviations

1. **2026-10-12, after the stage-1 C4 run, before any set A result was read.** The size
   rule ("more than 20% larger than the incumbent on any file") counts a file only if the
   difference is also **more than 32 bytes**. C4 has files of a few bytes (TOML test data,
   empty-ish modules) where one byte is +100%: on those, every method "fails", libdeflate-12
   included, which says nothing about robustness.
2. **Same time.** The 5× time rule applies to set A files of **at least 64 KiB**. On the
   tiny inputs, time is dominated by per-call set-up (zeroing hash tables); that cost is
   real, but it is what scenarios S5 (archive members) and S7 (messages) measure, and it is
   reported there rather than used to disqualify.
