#!/usr/bin/env python3
# /// script
# requires-python = ">=3.12"
# dependencies = [
#     "matplotlib>=3.11.2",
# ]
# ///
"""Compare the ways a Pareto frontier can be weighted, on synthetic shapes or a real run.

    .venv/bin/python scripts/pareto-weights.py                     synthetic scenarios
    .venv/bin/python scripts/pareto-weights.py --run <run.jsonl>   a real frontier

The eight weight functions themselves now live in `validator/scoring/pareto.py`, because
the validator scores real rounds with them and a second copy would drift. What is left
here is what a scoring spike is for: the synthetic scenarios they are judged on, the
report tables, and the figures.

With no arguments this runs a handful of synthetic scenarios (built from magnitudes seen
in the real silesia results but hand-shaped into specific situations: a lonely dominant
point, a dense cluster, an even staircase, a big elbow, a false elbow) through every
method, writing a summary table plus one figure (raw scatter, weight bars, same color per
point throughout) per (method, scenario) to data/spike/pareto/weights/<method>/ -- flat
within each method's directory, so the functions can be judged against each other across
situations they will eventually meet for real, without depending on any benchmark run.

With `--run`, the same methods are applied to a real pareto-bench run -- one scenario per
corpus, provable candidates only by default, into data/benchmark-reports/weights/. The
time boundary is then derived from the data rather than assumed, because this competition
does not enforce an absolute time: it rejects anything slower than --speed-floor times the
incumbent, so the boundary is that multiple of the incumbent's measured time on that
corpus. The library's 120s fallback against runs taking 0.2-2.2s would push every real
point into the corner and flatten every normalized method into noise.

A method that normalizes also gets a third panel: the same points run through that
normalization and drawn as a true square (both axes on the same scale), so how the
normalization reshapes the frontier is visible directly. A method that never normalizes
(hypervolume, neighbor-improvement) has nothing to show there, so the panel is dropped
rather than faked. Normalization comes in two kinds, picked per method in `NORMALIZERS`:

  boundary_normalizer   against the enforced limits a submission is rejected for missing,
                        never the spread of who happened to submit this round. Those same
                        boundaries stand in as literal neighbors at each end of the
                        frontier, so the fastest point is compared against the worst a
                        *legal* submission may be. Right for a method whose formula
                        reaches for that external limit.

  frontier_normalizer   against the frontier's own two extremes -- for local-global, which
                        only ever compares a point to others actually on the frontier and
                        has no external limit in its formula at all. Normalizing it
                        against a competition constant would just be noise.

Historical comparisons and the selected local-global default are described in
docs/SCORING.md.
"""

import argparse
import glob
import json
import os
import statistics
import sys

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt  # noqa: E402

REPO_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(REPO_ROOT, "validator"))

from scoring.pareto import (  # noqa: E402
    METHODS,
    Boundaries,
    Point,
    pareto_front,
)

OUT = os.path.join(REPO_ROOT, "data", "spike", "pareto", "weights")

# Which panel a method's normalized figure is drawn against -- None for one that never
# normalizes at all (no panel is drawn), "boundary" for a method anchored to the enforced
# limits, "frontier" for one that only compares a point to the frontier's own extremes.
NORMALIZERS = {
    "hypervolume": None,
    "hypervolume-normalized": "boundary",
    "neighbor-improvement": None,
    "elbow-sweetspot": "boundary",
    "diagonal-sweep-k1.0": "boundary",
    "diagonal-sweep-k0.33": "boundary",
    "diagonal-sweep-k3.0": "boundary",
    "local-global": "frontier",
}

# Not provable submissions: a literals-only floor and a production compressor. They are
# bounds on the plot, not candidates, and putting them on a frontier meant to rank
# submissions would be scoring things nobody can submit.
NON_CANDIDATES = {"no-lz77", "libdeflate-12"}
INCUMBENT = "lazy"

# The synthetic scenarios are judged against the library's own fallback boundaries; only
# --run derives real ones, from the incumbent's measured time.
DEFAULT_BOUNDS = Boundaries()


def boundaries_from_run(points, speed_floor):
    """The real edge of the legal region for one corpus, from the incumbent's own time.

    The gate rejects a submission slower than `speed_floor` times the incumbent, so that
    multiple of the incumbent's measured time is the boundary. Returns None when this
    corpus has no incumbent to derive it from, and the caller falls back.
    """
    incumbent = next((p for p in points if p.name == INCUMBENT), None)
    if incumbent is None or incumbent.time_s <= 0:
        return None
    return Boundaries.from_incumbent(incumbent.time_s, speed_floor)


def normalizer_for(method, front, bounds):
    # The `(time_s, ratio_pct) -> (nt, nr)` the figure's normalized panel is drawn with,
    # or None for a method that has no business with one.
    kind = NORMALIZERS[method]
    if kind is None:
        return None
    if kind == "frontier":
        return frontier_normalizer(front)
    return bounds.normalize


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument(
        "--run",
        nargs="?",
        const="",
        default=None,
        help="score a real pareto-bench run; bare flag takes the newest",
    )
    ap.add_argument(
        "--corpus", action="append", help="limit --run to these corpora (default: all in the file)"
    )
    ap.add_argument(
        "--speed-floor",
        type=float,
        default=8.0,
        help="the harness's rejection multiple of the incumbent (default 8)",
    )
    ap.add_argument(
        "--include-bounds",
        action="store_true",
        help="keep no-lz77 and libdeflate-12, which nobody can submit",
    )
    args = ap.parse_args()

    out_root = OUT
    if args.run is not None:
        run_path = args.run or newest_run()
        if not run_path or not os.path.exists(run_path):
            raise SystemExit("no run file found under data/benchmark-runs/")
        all_points = load_run(run_path, args.include_bounds)
        if args.corpus:
            all_points = {k: v for k, v in all_points.items() if k in args.corpus}
        if not all_points:
            raise SystemExit("no matching corpora in the run file")
        out_root = os.path.join(REPO_ROOT, "data", "benchmark-reports", "weights")
        print(f"scoring {os.path.relpath(run_path, REPO_ROOT)}: {', '.join(all_points)}")
    else:
        all_points = scenarios()

    for method, weight_fn in METHODS.items():
        method_dir = os.path.join(out_root, method)
        os.makedirs(method_dir, exist_ok=True)
        report = [f"# Pareto weight scoring -- {method}", ""]
        for scenario, points in all_points.items():
            bounds = DEFAULT_BOUNDS
            if args.run is not None:
                derived = boundaries_from_run(points, args.speed_floor)
                if derived:
                    bounds = derived
                    report.append(
                        f"Time boundary for `{scenario}`: {bounds.time_s:.3f}s "
                        f"({args.speed_floor:g}x the incumbent `{INCUMBENT}`).\n"
                    )
            front = pareto_front(points)
            weights = weight_fn(front, bounds)
            report.append(summary(scenario, points, front, weights))
            colors = {
                p.name: color_for(i) for i, p in enumerate(sorted(points, key=lambda p: p.time_s))
            }
            plot(
                points,
                front,
                weights,
                colors,
                scenario,
                os.path.join(method_dir, f"{scenario}.png"),
                normalizer_for(method, front, bounds),
            )
        with open(os.path.join(method_dir, "REPORT.md"), "w") as fh:
            fh.write("\n".join(report))
        print(f"wrote {os.path.relpath(method_dir, REPO_ROOT)}/ ({len(all_points)} scenario(s))")


def load_run(path, include_non_candidates=False):
    """{corpus: [Point, ...]} from a pareto-bench JSONL run.

    Ratio is deterministic, so it is taken as-is; time is the median of the measured
    reps, warmup discarded, summed over the corpus -- the same reduction
    `python -m bench.analyze` makes, so the two reports describe the same numbers.
    """
    per = {}
    for line in open(path):
        line = line.strip()
        if not line:
            continue
        rec = json.loads(line)
        if rec.get("kind") != "file":
            continue
        acc = per.setdefault(rec["corpus"], {})
        for method, m in rec["methods"].items():
            if method in NON_CANDIDATES and not include_non_candidates:
                continue
            times = [r.get("total_s") for r in m["reps"] if r["phase"] == "measured"]
            if not times or any(t is None for t in times):
                raise ValueError("full compression timings missing; rebenchmark legacy runs")
            a = acc.setdefault(method, [0, 0, 0.0])
            a[0] += rec["raw_bytes"]
            a[1] += m["output_bytes"]
            a[2] += statistics.median(times) if times else 0.0
    return {
        corpus: [Point(name, t, 100.0 * b / raw) for name, (raw, b, t) in sorted(acc.items())]
        for corpus, acc in sorted(per.items())
    }


def newest_run():
    runs = sorted(glob.glob(os.path.join(REPO_ROOT, "data", "benchmark-runs", "*.jsonl")))
    return runs[-1] if runs else None


def scenarios():
    # Every scenario is hand-built, but the magnitudes (times in the 0.04s-50s
    # range, ratios 10%-100%) match what results_full_silesia.json actually
    # contains -- these are stress tests of the scoring function's shape, not
    # a claim about what any real submission would score.
    return {
        "real-silesia-rust-only": real_silesia_rust_only(),
        "lonely-dominant": lonely_dominant(),
        "dense-cluster": dense_cluster(),
        "even-staircase": even_staircase(),
        "big-elbow": big_elbow(),
        "false-elbow": false_elbow(),
        "near-duplicates": near_duplicates(),
    }


def real_silesia_rust_only():
    # The actual aggregate numbers from REPORT-full-silesia.md's "Rust/provable
    # only" table -- a real-data baseline the synthetic scenarios are judged against.
    return [
        Point("template", 4.3331, 37.81),
        Point("hc-d4", 4.7004, 34.82),
        Point("hc-sparse", 6.3094, 39.07),
        Point("hash-chains", 5.6255, 33.44),
        Point("hc-d64", 6.9914, 32.87),
        Point("lazy", 10.3306, 32.42),
        Point("mo-lazy", 17.9113, 31.97),
        Point("btree", 27.2694, 32.68),
        Point("optimal", 46.5669, 31.94),
    ]


def lonely_dominant():
    # One point crushes everything: much faster AND much better ratio. It
    # should take ~all the weight; the rest are either dominated outright or
    # left clinging to a sliver at the slow/bad end.
    return [
        Point("champion", 1.0, 15.0),
        Point("a", 4.0, 35.0),
        Point("b", 8.0, 33.0),
        Point("c", 15.0, 32.0),
        Point("d", 30.0, 31.5),
        Point("e", 45.0, 31.0),
    ]


def dense_cluster():
    # Six near-identical points bunched at the fast end (a few ms apart, ratio
    # within a point of each other), then one lonely point way out at the slow
    # end with a meaningfully better ratio. The cluster should each get a thin
    # slice; the lonely slow point should dominate the total weight.
    return [
        Point("c1", 4.00, 38.0),
        Point("c2", 4.05, 37.6),
        Point("c3", 4.10, 37.3),
        Point("c4", 4.15, 37.1),
        Point("c5", 4.20, 37.0),
        Point("c6", 4.25, 36.9),
        Point("outlier", 40.0, 20.0),
    ]


def even_staircase():
    # A deliberately regular staircase: time doubles, ratio drops by an even
    # step, all the way down. Tests whether "evenly spaced" in the visual
    # sense also comes out close to evenly weighted (it should trend that
    # way, modulo the last step to the reference point being the widest).
    n = 7
    return [Point(f"s{i}", 2.0**i, 70.0 - 6.0 * i) for i in range(n)]


def big_elbow():
    # Mirrors the real mo-lazy/libdeflate-12 shape, exaggerated: a plateau
    # point sits at a modest time but eats almost the whole ratio range down
    # to what only a much, much slower point manages to shave off further.
    return [
        Point("fast", 3.0, 40.0),
        Point("mid", 6.0, 34.0),
        Point("elbow", 12.0, 24.0),
        Point("crawl", 90.0, 23.5),
    ]


def false_elbow():
    # big_elbow's inversion: "elbow" only looks like a middle bend because
    # it's positioned between mid and crawl -- it's barely better than mid on
    # ratio (34.0 -> 33.0) and only barely faster than crawl on time (8.0 vs
    # 10.0). crawl is where the real value sits: it recovers almost all the
    # remaining ratio (33.0 -> 24.0) for a trivial time cost over elbow (+2s,
    # not +78s like the original). A method that rewards "the middle point"
    # on shape alone, rather than what each point actually buys, should be
    # caught by this one favoring elbow over crawl.
    return [
        Point("fast", 3.0, 40.0),
        Point("mid", 6.0, 34.0),
        Point("elbow", 8.0, 33.0),
        Point("crawl", 10.0, 24.0),
    ]


def near_duplicates():
    # Pairs of points a hair's breadth apart in ratio at the same rough time.
    # Only a strict improvement stays on the frontier, so one of each pair
    # should be dominated outright (weight 0), not just down-weighted -- this
    # checks the frontier filter's tie-breaking, not just the area formula.
    return [
        Point("p1", 4.0, 38.000),
        Point("p1-dup", 4.0, 38.001),
        Point("p2", 9.0, 33.000),
        Point("p2-dup", 9.2, 33.0005),
        Point("p3", 20.0, 32.000),
    ]


def frontier_normalizer(front):
    # For plotting only methods that compare a point to the frontier's own
    # extremes (e.g. local_global_weights), never to an external boundary:
    # 0 is the hypothetical "as fast as the fastest, as good as the best"
    # corner, 1 is "as slow as the slowest, as bad as the worst" -- neither
    # actually achieved by any one point, both built from the two that bound
    # the frontier.
    ordered = sorted(front, key=lambda p: p.time_s)
    lo_t, hi_t = ordered[0].time_s, ordered[-1].time_s
    lo_r, hi_r = ordered[-1].ratio_pct, ordered[0].ratio_pct

    def norm(time_s, ratio_pct):
        nt = (time_s - lo_t) / (hi_t - lo_t) if hi_t > lo_t else 0.0
        nr = (ratio_pct - lo_r) / (hi_r - lo_r) if hi_r > lo_r else 0.0
        return nt, nr

    return norm


def summary(scenario, points, front, weights):
    frontier_names = {p.name for p in front}
    lines = [
        f"## {scenario}",
        "",
        "| point | time (s) | ratio (%) | on frontier? | weight |",
        "|---|---|---|---|---|",
    ]
    for p in sorted(points, key=lambda p: p.time_s):
        on_front = p.name in frontier_names
        w = weights.get(p.name, 0.0)
        mark = "**yes**" if on_front else "no"
        lines.append(f"| {p.name} | {p.time_s:.4f} | {p.ratio_pct:.3f} | {mark} | {w:.4f} |")
    lines.append("")
    return "\n".join(lines)


def color_for(i):
    palette = plt.get_cmap("tab20").colors
    return palette[i % len(palette)]


def plot(points, front, weights, colors, title, path, norm_fn):
    # One figure per scenario, sharing the same per-point color throughout.
    # `norm_fn` is `(time_s, ratio_pct) -> (nt, nr)` for a method that
    # normalizes, or None for one that never does -- a method that only ever
    # works in raw units has nothing meaningful to show in a normalized
    # panel, so that panel is dropped entirely rather than showing a
    # normalization the method itself doesn't use.
    if norm_fn is None:
        fig, (ax_scatter, ax_bars) = plt.subplots(1, 2, figsize=(13, 5))
    else:
        fig, (ax_scatter, ax_norm, ax_bars) = plt.subplots(1, 3, figsize=(19, 5))
        plot_scatter_normalized(ax_norm, points, front, colors, norm_fn)
    plot_scatter(ax_scatter, points, front, colors)
    plot_bars(ax_bars, points, weights, colors)
    fig.suptitle(title)
    fig.tight_layout()
    fig.savefig(path, dpi=140)
    plt.close(fig)


def plot_scatter(ax, points, front, colors):
    frontier_names = {p.name for p in front}
    for p in points:
        on_front = p.name in frontier_names
        ax.scatter(
            [p.time_s],
            [p.ratio_pct],
            color=colors[p.name],
            s=110 if on_front else 60,
            zorder=3,
            edgecolors="black" if on_front else "none",
            linewidths=1.2,
        )
        ax.annotate(
            p.name, (p.time_s, p.ratio_pct), textcoords="offset points", xytext=(6, 4), fontsize=8
        )
    ordered_front = sorted(front, key=lambda p: p.time_s)
    ax.plot(
        [p.time_s for p in ordered_front],
        [p.ratio_pct for p in ordered_front],
        "--",
        color="gray",
        zorder=1,
    )
    ax.set_xlabel("time, s")
    ax.set_ylabel("ratio, % of raw (lower is better)")
    ax.set_title("points (filled ring = on frontier)")
    ax.grid(True, alpha=0.3)


def plot_scatter_normalized(ax, points, front, colors, norm_fn):
    # The same points, run through whichever normalizer this method actually
    # uses (the enforced boundary, or the frontier's own two extremes), drawn
    # with a forced 1:1 aspect ratio -- a genuine square, both axes on the
    # same scale, so how the normalization actually reshapes the frontier is
    # visible directly rather than left to trust.
    frontier_names = {p.name for p in front}
    for p in points:
        nt, nr = norm_fn(p.time_s, p.ratio_pct)
        on_front = p.name in frontier_names
        ax.scatter(
            [nt],
            [nr],
            color=colors[p.name],
            s=110 if on_front else 60,
            zorder=3,
            edgecolors="black" if on_front else "none",
            linewidths=1.2,
        )
        ax.annotate(p.name, (nt, nr), textcoords="offset points", xytext=(6, 4), fontsize=8)
    ordered_front = sorted(front, key=lambda p: p.time_s)
    normalized_front = [norm_fn(p.time_s, p.ratio_pct) for p in ordered_front]
    ax.plot(
        [nt for nt, _ in normalized_front],
        [nr for _, nr in normalized_front],
        "--",
        color="gray",
        zorder=1,
    )
    ax.axvline(1.0, color="crimson", linestyle=":", linewidth=1, zorder=2)
    ax.axhline(1.0, color="crimson", linestyle=":", linewidth=1, zorder=2)
    ax.set_xlim(-0.05, 1.1)
    ax.set_ylim(-0.05, 1.1)
    ax.set_aspect("equal", adjustable="box")
    ax.set_xlabel("time, normalized")
    ax.set_ylabel("ratio, normalized")
    ax.set_title("normalized (dotted red = this method's boundary)")
    ax.grid(True, alpha=0.3)


def plot_bars(ax, points, weights, colors):
    ordered = sorted(points, key=lambda p: p.time_s)
    names = [p.name for p in ordered]
    values = [weights.get(n, 0.0) for n in names]
    bar_colors = [colors[n] for n in names]
    ax.bar(names, values, color=bar_colors, edgecolor="black", linewidth=0.6)
    ax.set_ylabel("weight (sums to 1 across the frontier)")
    ax.set_title("weight distribution")
    ax.set_ylim(bottom=0)
    ax.tick_params(axis="x", rotation=45)
    ax.grid(True, axis="y", alpha=0.3)


if __name__ == "__main__":
    main()


if __name__ == "__main__":
    main()
