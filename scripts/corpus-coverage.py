#!/usr/bin/env python3
"""Does the corpus span the range of parse behaviour a real DEFLATE encoder meets?

    scripts/corpus-coverage.py <corpus.tsv> <reference.tsv> [...]

Both arguments are corpus-profile output (scripts/pareto-bench/src/bin/corpus-profile.rs).
The first is the benchmark; the rest are reference populations -- Silesia is the obvious
one, being the corpus every modern compressor reports against.

WHY NOT COUNT FORMATS

The obvious coverage metric is "we have N of the M popular file formats", and it is
close to meaningless here. An LZ77 parser does not see formats, it sees match
opportunities, and two files with different extensions can be identical to it. This
corpus produced a clean example: `weights-q8.bin` and `weights-q4k.bin` are different
quantization schemes from different code paths, and they profiled identically -- gap
1.00011 against 1.00002 -- until the shared tokenizer metadata was excluded. Two
formats, one behaviour, zero extra coverage. A format list is a communication tool.
It is not a measurement.

WHAT THIS MEASURES INSTEAD

Each file becomes a point in the space of things that actually decide how a parser
behaves on it, all of them from the profile:

    gap        optimal bytes / greedy bytes -- how much a better parse can win
    lit_frac   how much of the output is literals rather than matches
    mean_len   mean match length (log-scaled; it spans 3 to 240)
    near, far  the match distance distribution
    cap258     fraction of matches pinned at the 258-byte length cap

Axes are normalised against fixed plausible ranges, not the corpus's own spread --
otherwise any corpus trivially "spans" itself.

Two numbers come out, and they answer different questions:

    reach      for each REFERENCE file, the distance to the nearest corpus file.
               The worst one is the headline: it says no real-world file in the
               reference set behaves in a way nothing in the benchmark tests.
               This is the number that can fail, because the reference is external.

    spacing    for each corpus file, the distance to its nearest neighbour IN the
               corpus. Small means two parts measure the same thing and one of them
               is budget spent twice.

Neither is a percentage and neither should be read as one. "87% covered" would be a
made-up denominator; a worst-case distance with the file that produced it is not.
"""

import csv
import math
import sys

# axis -> (low, high) plausible range, and whether to log-scale first.
AXES = {
    "gap":      (0.50, 1.02, False),
    "lit_frac": (0.00, 1.00, False),
    "mean_len": (3.0, 260.0, True),
    "near":     (0.00, 1.00, False),
    "far":      (0.00, 1.00, False),
    "cap258":   (0.00, 1.00, True),
}


def vector(row):
    v = []
    for name, (lo, hi, logscale) in AXES.items():
        x = float(row[name])
        if logscale:
            lo_, hi_, x = math.log(lo + 1e-9), math.log(hi), math.log(max(x, lo) + 1e-9)
            v.append(min(1.0, max(0.0, (x - lo_) / (hi_ - lo_))))
        else:
            v.append(min(1.0, max(0.0, (x - lo) / (hi - lo))))
    return v


def dist(a, b):
    """Euclidean, then divided by sqrt(dims) so it reads as a per-axis average."""
    return math.sqrt(sum((x - y) ** 2 for x, y in zip(a, b)) / len(a))


def load(path):
    rows = list(csv.DictReader(open(path), delimiter="\t"))
    return [(r["file"], vector(r)) for r in rows]


def nearest(point, population, exclude=None):
    best, who = float("inf"), None
    for name, v in population:
        if name == exclude:
            continue
        d = dist(point, v)
        if d < best:
            best, who = d, name
    return best, who


def main():
    if len(sys.argv) < 3:
        sys.exit(__doc__)
    corpus = load(sys.argv[1])
    print(f"corpus: {len(corpus)} files, {len(AXES)} axes "
          f"({', '.join(AXES)})\n")

    print("REACH -- how far each reference file is from the nearest thing we test")
    worst = []
    for path in sys.argv[2:]:
        ref = load(path)
        rows = sorted(((nearest(v, corpus)[0], name, nearest(v, corpus)[1]) for name, v in ref),
                      reverse=True)
        print(f"\n  {path}  ({len(ref)} files)")
        for d, name, who in rows:
            flag = "   <-- nothing close" if d > 0.15 else ""
            print(f"    {name:<24} {d:.3f}  nearest: {who}{flag}")
        worst.append((rows[0][0], path, rows[0][1]))
        print(f"    {'worst':<24} {rows[0][0]:.3f} ({rows[0][1]})   "
              f"mean {sum(r[0] for r in rows) / len(rows):.3f}")

    print("\nSPACING -- corpus files with a near-duplicate inside the corpus")
    pairs = sorted((nearest(v, corpus, exclude=name)[0], name, nearest(v, corpus, exclude=name)[1])
                   for name, v in corpus)
    for d, name, who in pairs[:8]:
        flag = "   <-- measures the same thing" if d < 0.04 else ""
        print(f"    {name:<24} {d:.3f}  nearest: {who}{flag}")
    print(f"    {'...':<24}")
    print(f"    {'most distinct':<24} {pairs[-1][0]:.3f}  ({pairs[-1][1]})")

    print("\nverdict")
    for d, path, name in worst:
        ok = "covered" if d <= 0.15 else "GAP"
        print(f"  {path}: worst reach {d:.3f} on {name} -- {ok}")
    dup = [p for p in pairs if p[0] < 0.04]
    print(f"  {len(dup)} corpus file(s) within 0.04 of another"
          + (": " + ", ".join(n for _d, n, _w in dup) if dup else ""))


if __name__ == "__main__":
    main()
