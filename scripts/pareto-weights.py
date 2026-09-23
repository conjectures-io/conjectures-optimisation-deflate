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

Unselected experimental methods are registered only in this script; the selected
log improvement-space method uses the shared production implementation.
Use --method to select comparisons, --scenario to select synthetic
shapes, and --out-dir to choose an output directory. Synthetic runs also produce
EXPERIMENT.md, duplicate-study.json, duplicate-sensitivity.png and side-by-side
compare-*.png figures. Live scoring remains unchanged.

The eight established weight functions themselves now live in `validator/scoring/pareto.py`, because
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

Historical comparisons and the selected local-global-improvement-space-log default are described in
docs/SCORING.md.
"""

import argparse
import glob
import json
import math
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
    adjusted_local_global,
    improvement_factors,
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
    "local-global-total-gain": "frontier",
    "improvement-space": "frontier",
    "improvement-space-log": "frontier-log",
    "local-global-improvement-space": "frontier",
    "local-global-improvement-space-log": "frontier",
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
    if kind == "frontier-log":
        return frontier_normalizer(front, logarithmic=True)
    if kind == "frontier":
        return frontier_normalizer(front)
    return bounds.normalize


def improvement_space_weights(front, bounds=None, *, logarithmic=False):
    del bounds
    return improvement_factors(front, incremental=True, logarithmic=logarithmic)


# Unselected experiments stay here; the selected log method comes from METHODS.
SPIKE_METHODS = {
    **METHODS,
    "local-global-total-gain": adjusted_local_global,
    "improvement-space": improvement_space_weights,
    "improvement-space-log": lambda front, bounds: improvement_space_weights(
        front, bounds, logarithmic=True
    ),
    "local-global-improvement-space": lambda front, bounds: adjusted_local_global(
        front, bounds, incremental=True
    ),
}


def add_near_copies(points, target, count, epsilon):
    """True trade-offs, within epsilon of each original frontier-axis range.

    Preserve the original extremes: endpoint copies move inward. Interior copies
    straddle their source. Cap distance before either adjacent frontier point.
    All copies are credited to the source's hypothetical owner in the attack study.
    """
    ordered = pareto_front(points)
    index = next(i for i, p in enumerate(ordered) if p.name == target)
    anchor = ordered[index]
    if len(ordered) < 2 or count < 1 or not 0 < epsilon < 1:
        raise ValueError("copies require a nontrivial frontier, count >= 1 and 0 < epsilon < 1")
    dt = epsilon * (ordered[-1].time_s - ordered[0].time_s)
    dr = epsilon * (ordered[0].ratio_pct - ordered[-1].ratio_pct)
    for neighbor in ordered[max(0, index - 1) : index] + ordered[index + 1 : index + 2]:
        dt = min(dt, 0.4 * abs(neighbor.time_s - anchor.time_s))
        dr = min(dr, 0.4 * abs(neighbor.ratio_pct - anchor.ratio_pct))
    copies = []
    for i in range(count):
        if index == 0:
            offset = (i + 1) / count
        elif index == len(ordered) - 1:
            offset = -(i + 1) / count
        else:
            offset = (1 if i % 2 == 0 else -1) * (i // 2 + 1) / math.ceil(count / 2)
        copies.append(
            Point(
                f"{target}-copy{i + 1}",
                anchor.time_s + offset * dt,
                anchor.ratio_pct - offset * dr,
            )
        )
    return [*points, *copies], {target, *(p.name for p in copies)}


def duplicate_study(methods, out_root, *, scenario="big-elbow"):
    """Measure combined owner allocation, not just each copy's smaller bar."""
    base = scenarios()[scenario]
    targets = ["fast", "elbow", "crawl"]
    counts = [1, 4, 16]
    epsilons = [1e-2, 1e-3, 1e-4, 1e-5, 1e-6]
    results = []
    for target in targets:
        for count in counts:
            for epsilon in epsilons:
                points, owner = add_near_copies(base, target, count, epsilon)
                for method, weight_fn in methods.items():
                    before = weight_fn(pareto_front(base), DEFAULT_BOUNDS).get(target, 0.0)
                    weights = weight_fn(pareto_front(points), DEFAULT_BOUNDS)
                    after = sum(weights.get(name, 0.0) for name in owner)
                    results.append(
                        {
                            "method": method,
                            "target": target,
                            "copies": count,
                            "epsilon": epsilon,
                            "before": before,
                            "after": after,
                            "inflation": after / before if before else None,
                        }
                    )
    with open(os.path.join(out_root, "duplicate-study.json"), "w") as fh:
        json.dump(results, fh, indent=2, allow_nan=False)
    fig, axes = plt.subplots(3, 3, figsize=(18, 13), sharex=True, layout="constrained")
    for row, target in enumerate(targets):
        for column, count in enumerate(counts):
            ax = axes[row, column]
            for i, method in enumerate(methods):
                samples = [
                    r
                    for r in results
                    if r["method"] == method and r["target"] == target and r["copies"] == count
                ]
                ax.plot(
                    [r["epsilon"] for r in samples],
                    [r["inflation"] for r in samples],
                    ".-",
                    color=color_for(i),
                    label=method,
                )
            ax.axhline(1, color="black", linestyle=":", linewidth=1)
            ax.set_xscale("log")
            ax.invert_xaxis()
            ax.set(
                title=f"{target}: {count} added copies",
                xlabel="Copy distance cap / original axis range (smaller →)",
                ylabel="Combined owner share / original share",
            )
            ax.grid(alpha=0.2)
    handles, labels = axes[0, 0].get_legend_handles_labels()
    fig.legend(handles, labels, loc="outside lower center", ncols=3, fontsize=8)
    fig.suptitle(f"{scenario}: near-copy reward inflation; dotted line = no extra allocation")
    fig.savefig(os.path.join(out_root, "duplicate-sensitivity.png"), dpi=140)
    plt.close(fig)
    lines = [
        "# Improvement-space weighting experiment",
        "",
        "The production default is local-global-improvement-space-log; other methods are controls.",
        "",
        "All tests use deterministic synthetic points, without timing uncertainty.",
        "Owner means the combined anchor + copy allocation, regardless of hotkey.",
        "Copies remain non-dominated and do not move the original frontier extremes.",
        "",
        f"Test shape: {scenario}.",
        "",
        "The proposed factor is incremental improvement-space. Total gain is only a control.",
        "",
        "## Formulas",
        "",
        "- Total gain: Gt_i = (t_max - t_i) / sum_j(t_max - t_j); "
        "Gr_i = (r_max - r_i) / sum_j(r_max - r_j); F_i = (Gt_i + Gr_i) / 2.",
        "- Incremental space: Dt_i = (t_next - t_i) / (t_max - t_min); "
        "Dr_i = (r_previous - r_i) / (r_max - r_min); F_i = (Dt_i + Dr_i) / 2. "
        "Missing endpoint differences are zero.",
        "- Log incremental space: Dt_i = log(t_next / t_i) / log(t_max / t_min); "
        "Dr_i = log(r_previous / r_i) / log(r_max / r_min); F_i = (Dt_i + Dr_i) / 2. "
        "This changes the gain factor on both axes; local-global coefficients stay linear.",
        "- Adjusted local-global: normalize(local_i × global_i × F_i).",
        "- improvement-space alone uses F_i directly, to isolate the added factor.",
        "",
        "Singletons receive 1. Empty frontiers receive no weight. No compression "
        "threshold or external endpoint bonus is used. "
        "Log variants require positive finite values.",
        "",
        "## Near-copy limit (distance cap 0.0001% of each original axis range)",
        "",
        "| method | target | copies | before | group after | multiplier |",
        "|---|---|---:|---:|---:|---:|",
    ]
    for r in results:
        if r["epsilon"] == epsilons[-1]:
            multiplier = (
                f"{r['inflation']:.3f}x" if r["inflation"] is not None else "n/a (zero before)"
            )
            lines.append(
                f"| {r['method']} | {r['target']} | {r['copies']} | "
                f"{r['before']:.4%} | {r['after']:.4%} | {multiplier} |"
            )
    lines += [
        "",
        "## Interpretation",
        "",
        "Total-gain factors measure position, not uniqueness: arbitrarily close points "
        "receive almost identical factors. They cannot by themselves prevent duplication.",
        "Incremental space divides two fixed improvement budgets. Copies of one point "
        "approach the original combined allocation when this factor is used alone.",
        "Multiplying by local-global loses that exact conservation: inserting neighbors "
        "changes the local coefficients. Inspect the group multipliers, not only smaller "
        "individual copy weights.",
        "Space-based methods can favor a point adjacent to a large gap, including endpoints. "
        "The dense-cluster and endpoint scenarios expose this trade-off.",
        "Frontier-relative normalization remains sensitive to new extreme points; this "
        "study holds the original extremes fixed and does not claim universal strategy resistance.",
    ]
    with open(os.path.join(out_root, "EXPERIMENT.md"), "w") as fh:
        fh.write("\n".join(lines) + "\n")


def copy_audit(methods, out_root):
    """Try every frontier point in every original scenario, not only the good elbow."""
    rows = []
    for scenario, points in scenarios().items():
        if scenario.startswith("near-tradeoffs"):
            continue
        front = pareto_front(points)
        if len(front) < 2:
            continue
        for target in front:
            for count in (1, 4, 16):
                copied, owner = add_near_copies(points, target.name, count, 1e-6)
                for name, fn in methods.items():
                    before = fn(front, DEFAULT_BOUNDS).get(target.name, 0)
                    after = sum(
                        w
                        for key, w in fn(pareto_front(copied), DEFAULT_BOUNDS).items()
                        if key in owner
                    )
                    rows.append(
                        {
                            "scenario": scenario,
                            "method": name,
                            "target": target.name,
                            "copies": count,
                            "before": before,
                            "after": after,
                            "inflation": after / before if before else None,
                        }
                    )
    with open(os.path.join(out_root, "copy-audit.json"), "w") as fh:
        json.dump(rows, fh, indent=2, allow_nan=False)
    lines = [
        "# Copy audit across all original scenarios",
        "",
        "Each frontier point is tested with 1, 4 and 16 near-copies at a distance cap",
        "of 0.0001% of each original axis range. Original extremes stay fixed.",
        "These are sampled attacks, not a proof of strategy resistance.",
        "",
        "Multipliers below cover positive original allocations; zero-to-positive gains",
        "are listed separately.",
        "",
        "| Method | Worst multiplier | Scenario | Point | Copies | Before | Group after |",
        "|---|---:|---|---|---:|---:|---:|",
    ]
    for name in methods:
        samples = [r for r in rows if r["method"] == name and r["inflation"] is not None]
        worst = max(samples, key=lambda r: r["inflation"])
        lines.append(
            f"| {name} | {worst['inflation']:.4f}x | {worst['scenario']} | "
            f"{worst['target']} | {worst['copies']} | "
            f"{worst['before']:.4%} | {worst['after']:.4%} |"
        )
    newly_paid = [r for r in rows if r["before"] == 0 and r["after"] > 1e-12]
    if newly_paid:
        lines += ["", "## Zero-to-positive gains", ""]
        for r in newly_paid:
            lines.append(
                f"- {r['method']}, {r['scenario']}/{r['target']}, {r['copies']} copies: "
                f"0 → {r['after']:.6%}."
            )
    lines += [
        "",
        "The incremental factor alone conserves the combined allocation in the",
        "limit of vanishing copy distance. Multiplying it by local-global does not:",
        "even the direction of the distortion depends on the frontier shape.",
        "The false-elbow case is a counterexample to treating the combined method",
        "as duplicate-resistant. Wider spacing and new extremes need separate analysis.",
    ]
    with open(os.path.join(out_root, "COPY-AUDIT.md"), "w") as fh:
        fh.write("\n".join(lines) + "\n")


def focused_studies(methods, out_root):
    selected = {
        name: fn
        for name, fn in methods.items()
        if name
        in {
            "local-global",
            "improvement-space",
            "improvement-space-log",
            "local-global-improvement-space",
            "local-global-improvement-space-log",
        }
    }
    if not selected:
        return
    for scenario in ("big-elbow", "false-elbow"):
        directory = os.path.join(out_root, "improvement-space-study", scenario)
        os.makedirs(directory, exist_ok=True)
        duplicate_study(selected, directory, scenario=scenario)


def comparison_plot(scenario, points, methods, bounds, out_root):
    """Two Pareto panels above one full-width comparison of method weights."""
    front = pareto_front(points)
    ordered = sorted(points, key=lambda p: p.time_s)
    colors = {p.name: color_for(i) for i, p in enumerate(ordered)}
    fig, axes = plt.subplot_mosaic(
        [["raw", "normalized"], ["weights", "weights"]],
        figsize=(16, 12),
        layout="constrained",
    )
    raw_ax, norm_ax, bar_ax = axes["raw"], axes["normalized"], axes["weights"]
    plot_scatter(raw_ax, points, front, colors)
    plot_scatter_normalized(norm_ax, front, front, colors, frontier_normalizer(front))
    norm_ax.set(xlim=(0, 1), ylim=(0, 1), title="Frontier coordinates (comparison only)")
    bottom = [0.0] * len(methods)
    values = [fn(front, bounds) for fn in methods.values()]
    for p in ordered:
        heights = [w.get(p.name, 0.0) for w in values]
        bar_ax.bar(list(methods), heights, bottom=bottom, color=colors[p.name], label=p.name)
        bottom = [a + b for a, b in zip(bottom, heights, strict=True)]
    bar_ax.set(ylabel="Share of frontier allocation", ylim=(0, 1), title="All methods")
    bar_ax.tick_params(axis="x", labelsize=8)
    plt.setp(bar_ax.get_xticklabels(), rotation=35, ha="right")
    bar_ax.legend(fontsize=7, loc="upper left", bbox_to_anchor=(1, 1))
    fig.suptitle(scenario)
    fig.savefig(os.path.join(out_root, f"compare-{scenario}.png"), dpi=140)
    plt.close(fig)


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
    ap.add_argument("--method", action="append", choices=sorted(SPIKE_METHODS))
    ap.add_argument("--scenario", action="append", help="select synthetic scenarios")
    ap.add_argument("--out-dir", help="override the report directory")
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

    if args.scenario:
        all_points = {k: v for k, v in all_points.items() if k in args.scenario}
        if not all_points:
            ap.error("no matching scenarios")
    out_root = args.out_dir or out_root
    os.makedirs(out_root, exist_ok=True)
    methods = {name: SPIKE_METHODS[name] for name in (args.method or SPIKE_METHODS)}
    for scenario, points in all_points.items():
        bounds = (
            boundaries_from_run(points, args.speed_floor) if args.run is not None else None
        ) or DEFAULT_BOUNDS
        comparison_plot(scenario, points, methods, bounds, out_root)
    if args.run is None:
        duplicate_study(methods, out_root)
        copy_audit(methods, out_root)
        focused_studies(methods, out_root)
    for method, weight_fn in methods.items():
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
                method=method,
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
        "big-elbow-two-nearby": big_elbow_nearby(2),
        "big-elbow-three-nearby": big_elbow_nearby(3),
        "false-elbow": false_elbow(),
        "near-duplicates": near_duplicates(),
        "near-tradeoffs-middle": add_near_copies(big_elbow(), "elbow", 4, 1e-4)[0],
        "near-tradeoffs-fast": add_near_copies(big_elbow(), "fast", 4, 1e-4)[0],
        "near-tradeoffs-slow": add_near_copies(big_elbow(), "crawl", 4, 1e-4)[0],
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


def big_elbow_nearby(count):
    """Small real trade-offs at the knee, all surviving Pareto filtering.

    The pair retains the original plus a slightly smaller/slower alternative.
    The triple adds a slightly faster/larger alternative on the other side.
    Time changes by 12.5%; compressed/raw ratio changes by 1.25% relative.
    This keeps the cluster local while separating its markers on the full plot.
    """
    points = big_elbow()
    points.append(Point("elbow-smaller", 13.5, 23.7))
    if count == 3:
        points.append(Point("elbow-faster", 10.5, 24.3))
    return sorted(points, key=lambda p: p.time_s)


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


def frontier_normalizer(front, *, logarithmic=False):
    # For plotting only methods that compare a point to the frontier's own
    # extremes (e.g. local_global_weights), never to an external boundary:
    # 0 is the hypothetical "as fast as the fastest, as good as the best"
    # corner, 1 is "as slow as the slowest, as bad as the worst" -- neither
    # actually achieved by any one point, both built from the two that bound
    # the frontier.
    ordered = sorted(front, key=lambda p: p.time_s)
    lo_t, hi_t = ordered[0].time_s, ordered[-1].time_s
    lo_r, hi_r = ordered[-1].ratio_pct, ordered[0].ratio_pct
    if logarithmic:
        lo_t, hi_t, lo_r, hi_r = map(math.log, (lo_t, hi_t, lo_r, hi_r))

    def norm(time_s, ratio_pct):
        if logarithmic:
            time_s, ratio_pct = math.log(time_s), math.log(ratio_pct)
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


def point_label_offset(name):
    return {
        "elbow-faster": (-50, 18),
        "elbow": (6, -20),
        "elbow-smaller": (16, 8),
    }.get(name, (6, 4))


def color_for(i):
    palette = plt.get_cmap("tab20").colors
    return palette[i % len(palette)]


def plot(points, front, weights, colors, title, path, norm_fn, *, method=None):
    # One figure per scenario, sharing the same per-point color throughout.
    # `norm_fn` is `(time_s, ratio_pct) -> (nt, nr)` for a method that
    # normalizes, or None for one that never does -- a method that only ever
    # works in raw units has nothing meaningful to show in a normalized
    # panel, so that panel is dropped entirely rather than showing a
    # normalization the method itself doesn't use.
    if norm_fn is None:
        fig, (ax_scatter, ax_bars) = plt.subplots(2, 1, figsize=(12, 10))
    else:
        fig, axes = plt.subplot_mosaic(
            [["raw", "normalized"], ["weights", "weights"]], figsize=(14, 11)
        )
        ax_scatter, ax_norm, ax_bars = axes["raw"], axes["normalized"], axes["weights"]
        plot_scatter_normalized(ax_norm, points, front, colors, norm_fn)
        if method in {"improvement-space-log", "local-global-improvement-space-log"}:
            ax_norm.set_title(
                "Linear local-global coordinates; gain factor uses log gaps"
                if method == "local-global-improvement-space-log"
                else "Log axes normalized to frontier extremes"
            )
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
            p.name,
            (p.time_s, p.ratio_pct),
            textcoords="offset points",
            xytext=point_label_offset(p.name),
            fontsize=8,
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

    nearby = sorted(
        [p for p in points if p.name in {"elbow", "elbow-faster", "elbow-smaller"}],
        key=lambda p: p.time_s,
    )
    if len(nearby) > 1:
        inset = ax.inset_axes([0.52, 0.48, 0.43, 0.43])
        inset.plot(
            [p.time_s for p in nearby],
            [p.ratio_pct for p in nearby],
            "--",
            color="gray",
            linewidth=1,
        )
        for p in nearby:
            inset.scatter(p.time_s, p.ratio_pct, color=colors[p.name], edgecolors="black")
            inset.annotate(
                p.name,
                (p.time_s, p.ratio_pct),
                xytext=(0, 8),
                textcoords="offset points",
                ha="center",
                fontsize=7,
            )
        inset.margins(x=0.55, y=0.55)
        inset.set_title("Elbow detail", fontsize=9)
        inset.tick_params(labelsize=7)
        inset.ticklabel_format(useOffset=False)
        inset.grid(alpha=0.2)


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
        ax.annotate(
            p.name,
            (nt, nr),
            textcoords="offset points",
            xytext=point_label_offset(p.name),
            fontsize=8,
        )
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
