"""Operator-only database scoring preview and reproducible plots; never sets weights."""

from __future__ import annotations

import argparse
import dataclasses
import json
from pathlib import Path

import db
import scoring
from scoring.pareto import global_coefficients, local_coefficients


def main(argv: list[str] | None = None) -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--method")
    ap.add_argument("--aggregation-id", type=int, action="append")
    ap.add_argument("--out-dir", type=Path)
    ap.add_argument(
        "--metagraph",
        type=Path,
        help="JSON hotkey-to-uid mapping; absent means provisional payments",
    )
    ap.add_argument("--burn-uid", type=int, default=0)
    args = ap.parse_args(argv)
    config = scoring.ScoringConfig.from_env()
    if args.method:
        config = dataclasses.replace(config, method=args.method)
    eligible = None
    if args.metagraph:
        eligible = {
            key
            for key, uid in json.loads(args.metagraph.read_text()).items()
            if uid != args.burn_uid
        }
    store = db.connect()
    try:
        rows = store.scoring.preview_inputs(aggregation_ids=args.aggregation_id)
        from sqlalchemy import select

        from db.aggregation import (
            CALCULATOR_VERSION,
            compression_statistics,
            timing_statistics,
            validate_evidence,
        )
        from db.models import BenchmarkAggregation, BenchmarkAggregationInput, BenchmarkRun

        print(f"Recalculating preview from stored benchmark evidence: {len(rows)} submissions.")
        provenance = {}
        timings = {}
        with store.sessions() as session:
            for row in rows:
                aggregation = session.get(BenchmarkAggregation, row.aggregation_id)
                run_rows = list(
                    session.scalars(
                        select(BenchmarkRun)
                        .join(
                            BenchmarkAggregationInput,
                            BenchmarkAggregationInput.run_id == BenchmarkRun.id,
                        )
                        .where(BenchmarkAggregationInput.aggregation_id == aggregation.id)
                        .order_by(BenchmarkRun.id)
                    )
                )
                timings[str(row.submission_id)] = timing_observations(
                    [(validate_evidence(run), run.candidate_method) for run in run_rows]
                )
                provenance[str(row.submission_id)] = {
                    "source_sha256": aggregation.source_sha256,
                    "aggregation_id": aggregation.id,
                    "calculator_version": CALCULATOR_VERSION,
                    "source_calculator_version": aggregation.calculator_version,
                    "recalculated": True,
                    "verification_current": row.verification_current,
                    "run_ids": list(
                        session.scalars(
                            select(BenchmarkAggregationInput.run_id).where(
                                BenchmarkAggregationInput.aggregation_id == aggregation.id
                            )
                        )
                    ),
                    "timing": {
                        k: v for k, v in timing_statistics(run_rows).items() if k != "files"
                    },
                    "compression": compression_statistics(run_rows),
                }
    finally:
        store.close()
    if any(row.verification_current is False for row in rows):
        print(
            "Historical verification used for preview; current live-scoring eligibility "
            "is not implied."
        )
    result = scoring.score(rows, rows, config, eligible_hotkeys=eligible)
    print(f"method={config.method} points={len(rows)} frontier={len(result.frontier.frontier)}")
    if eligible is None:
        print("Registration eligibility unknown: miner payments below are provisional.")
    points = result.frontier.points
    front = sorted((points[key] for key in result.frontier.frontier), key=lambda p: p.time_s)
    local = local_coefficients(front, 2.0, 0.0) if front else {}
    glob = global_coefficients(front, 2.0, 0.0) if front else {}
    output = []
    telemetry = {row.submission_id: row.byte_weighted_ratio_pct for row in rows}
    previous = None
    for s in sorted(result.scores, key=lambda s: s.time_s):
        key = str(s.submission_id)
        label = s.baseline_key or s.hotkey or key
        row = dataclasses.asdict(s) | {
            "ratio_pct": s.ratio_pct,
            "byte_weighted_ratio_pct": telemetry[s.submission_id],
            "label": label,
            "local": local.get(key),
            "global": glob.get(key),
        }
        if s.on_frontier:
            if previous is not None:
                row["time_change_pct"] = 100 * (s.time_s / previous.time_s - 1)
                row["size_change_pct"] = (
                    100 * (s.ratio_pct / previous.ratio_pct - 1) if previous.ratio_pct else None
                )
            previous = s
        output.append(row)
        print(
            f"{s.submission_id:>5} {label:<18} {s.time_s:>9.5f}s {s.ratio_pct:>7.3f}% "
            f"frontier={s.on_frontier} pareto={s.pareto_weight:.5f} "
            f"recency={s.improvement_weight:.5f} payable={s.payable_weight:.5f} "
            f"{s.burn_reason or ''}"
        )
    print(f"burn={result.burn_weight:.5f}")
    if args.out_dir:
        args.out_dir.mkdir(parents=True, exist_ok=True)
        payload = {
            "config": dataclasses.asdict(config),
            "sources": provenance,
            "timing_repetition_totals": timings,
            "points": output,
            "context": rows[0].context if rows else None,
            "registration_eligibility_known": result.eligibility_known,
            "preview_recalculated": True,
            "burn": result.burn_weight,
        }
        (args.out_dir / "scores.json").write_text(json.dumps(payload, indent=2, allow_nan=False))
        plot(result, args.out_dir, provenance, timings)


def timing_observations(runs):
    """Sum the nth measured repetition over every selected file and corpus.

    These are aligned repetition totals, not independently executed corpus passes:
    the engine measures all repetitions of each file before moving to the next.
    """
    files = [
        [rep for rep in file.methods[method].reps if rep.phase == "measured"]
        for run, method in runs
        for file in run.files
    ]
    if not files:
        return []
    if not files[0] or any(len(reps) != len(files[0]) for reps in files):
        raise ValueError("timing plots require equal nonzero repetition counts for every file")
    if any(rep.total_s is None for reps in files for rep in reps):
        raise ValueError("timing plots require complete total compression measurements")
    return [
        {
            "lz77_s": sum(rep.time_s for rep in repetition),
            "total_s": sum(rep.total_s for rep in repetition),
        }
        for repetition in zip(*files, strict=True)
    ]


def normalize_frontier(ordered):
    """Global local-global coordinates; a degenerate axis maps to zero."""
    front = [s for s in ordered if s.on_frontier]
    if not front:
        return {}
    t0, t1 = min(s.time_s for s in front), max(s.time_s for s in front)
    r0, r1 = min(s.ratio_pct for s in front), max(s.ratio_pct for s in front)
    return {
        s.submission_id: (
            (s.time_s - t0) / (t1 - t0) if t1 > t0 else 0.0,
            (s.ratio_pct - r0) / (r1 - r0) if r1 > r0 else 0.0,
        )
        for s in front
    }


def plot(result, directory, provenance=None, timings=None):
    import matplotlib

    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    from matplotlib.patches import Patch

    provenance, timings = provenance or {}, timings or {}
    ordered = sorted(result.scores, key=lambda s: (s.time_s, s.submission_id))
    # Assign by identity, not speed rank, so every panel shares the same mapping.
    identities = sorted(s.submission_id for s in ordered)
    cmap = plt.get_cmap("tab20" if len(identities) <= 20 else "turbo")
    colors = {
        key: cmap(i if len(identities) <= 20 else i / max(1, len(identities) - 1))
        for i, key in enumerate(identities)
    }
    labels = [s.baseline_key or f"{s.hotkey}:{s.submission_id}" for s in ordered]
    front = [s for s in ordered if s.on_frontier]
    normalized = normalize_frontier(ordered)

    def save(fig, name):
        fig.savefig(directory / name, dpi=160)
        plt.close(fig)

    def pareto(ax, *, normalize=False, uncertainty=False):
        selected = front if normalize else ordered
        coordinates = (
            normalized if normalize else {s.submission_id: (s.time_s, s.ratio_pct) for s in ordered}
        )
        for index, s in enumerate(selected):
            x, y = coordinates[s.submission_id]
            color = colors[s.submission_id]
            if uncertainty:
                stats = provenance.get(str(s.submission_id), {}).get("timing", {})
                interval = (stats.get("intervals") or {}).get("compression_seconds")
                if interval:
                    # Draw endpoints directly: a percentile interval need not contain the estimate.
                    ax.hlines(y, interval[0], interval[1], color=color, linewidth=2)
                    ax.plot(interval, [y, y], "|", color=color, markersize=8)
            ax.scatter(
                x,
                y,
                color=color,
                marker="s" if s.baseline_key else "o",
                zorder=3,
                clip_on=not normalize,
            )
            ax.annotate(
                s.baseline_key or f"{s.hotkey}:{s.submission_id}",
                (x, y),
                xytext=(4 if x < 0.9 or not normalize else -4, 8 if index % 2 == 0 else -14),
                ha="left" if x < 0.9 or not normalize else "right",
                textcoords="offset points",
                fontsize=8,
            )
        ax.plot(
            [coordinates[s.submission_id][0] for s in front],
            [coordinates[s.submission_id][1] for s in front],
            "--",
            color="gray",
        )
        if normalize:
            ax.plot([0, 1], [1, 0], ":", color="lightgray")
            ax.set(
                xlim=(0, 1),
                ylim=(0, 1),
                xlabel="Normalized compression time",
                ylabel="Normalized compressed size",
                title="Frontier normalized to its extremes",
            )
            ax.set_aspect("equal", adjustable="box")
        else:
            ax.margins(x=0.15, y=0.15)
            ax.set(
                xlabel="Sum of per-file median compression seconds",
                ylabel="Mean file compression ratio, equal corpus weights (%)",
                title="Compression Pareto",
            )
        ax.grid(alpha=0.15)
        if not selected:
            ax.text(0.5, 0.5, "No current scoring evidence", transform=ax.transAxes, ha="center")

    fig, axes = plt.subplots(1, 3, figsize=(20, 6), layout="constrained")
    pareto(axes[0])
    paid = [s.payable_weight for s in ordered]
    burned = [max(0.0, s.combined_weight - s.payable_weight) for s in ordered]
    bar_colors = [colors[s.submission_id] for s in ordered]
    axes[1].bar(range(len(ordered)), paid, color=bar_colors)
    axes[1].bar(
        range(len(ordered)),
        burned,
        bottom=paid,
        color=bar_colors,
        hatch="///",
        edgecolor="black",
        linewidth=0.4,
    )
    axes[1].set_xticks(range(len(ordered)), labels, rotation=60, ha="right")
    axes[1].legend(
        handles=[
            Patch(
                facecolor="white",
                edgecolor="black",
                label="Payable (provisional without metagraph)",
            ),
            Patch(facecolor="white", edgecolor="black", hatch="///", label="Burned allocation"),
        ],
        fontsize=8,
    )
    axes[1].set(ylabel="Share of total emission", title="Submission allocations")
    pareto(axes[2], normalize=True)
    save(fig, "pareto.png")

    fig, ax = plt.subplots(figsize=(10, 6), layout="constrained")
    pareto(ax, uncertainty=True)
    ax.set_title("Compression Pareto with 95% bootstrap timing intervals")
    fig.supxlabel(
        "Within recorded runs only; excludes host drift and systematic bias. "
        "Missing intervals are omitted.",
        fontsize=9,
    )
    save(fig, "pareto-uncertainty.png")

    import statistics

    fig, axes = plt.subplots(2, 2, figsize=(15, 10), layout="constrained")
    for column, (field, title) in enumerate(
        (("total_s", "Total compression"), ("lz77_s", "LZ77 stage"))
    ):
        for index, s in enumerate(ordered):
            values = [sample[field] for sample in timings.get(str(s.submission_id), [])]
            if not values:
                continue
            median = statistics.median(values)
            std = statistics.stdev(values) if len(values) > 1 else None
            for row in (0, 1):
                ax = axes[row, column]
                plotted = (
                    values
                    if row == 0
                    else [100 * (v / median - 1) for v in values]
                    if median > 0
                    else []
                )
                if not plotted:
                    continue
                boxes = ax.boxplot(
                    [plotted],
                    positions=[index],
                    widths=0.6,
                    patch_artist=True,
                    medianprops={"color": "black"},
                    flierprops={
                        "marker": ".",
                        "markersize": 3,
                        "markeredgecolor": colors[s.submission_id],
                    },
                )
                boxes["boxes"][0].set_facecolor(colors[s.submission_id])
                ax.scatter(
                    [index] * len(plotted),
                    plotted,
                    s=12,
                    color=colors[s.submission_id],
                    edgecolors="black",
                    linewidths=0.3,
                    zorder=3,
                )
            std_label = f"{std:.3g}s" if std is not None else "n/a"
            axes[0, column].annotate(
                f"n={len(values)}; SD={std_label}",
                (index, max(values)),
                xytext=(0, 10),
                textcoords="offset points",
                ha="center",
                fontsize=7,
            )
        for row in (0, 1):
            ax = axes[row, column]
            ax.set_xticks(range(len(ordered)), labels, rotation=60, ha="right")
            ax.set(
                title=title if row == 0 else f"{title}: relative variability",
                ylabel="Seconds over fixed corpus files"
                if row == 0
                else "Deviation from algorithm median (%)",
            )
            ax.margins(y=0.2)
            ax.grid(axis="y", alpha=0.2)
            if row == 1:
                ax.axhline(0, color="gray", linestyle="--", linewidth=0.8)
            if not any(timings.values()):
                ax.text(0.5, 0.5, "No measured timing samples", transform=ax.transAxes, ha="center")
    fig.suptitle("Timing repeatability on fixed data (warmups excluded)")
    fig.supxlabel(
        "Each dot sums the same repetition index across all selected files/corpora. "
        "Boxes: quartiles; whiskers: 1.5×IQR.\n"
        "Repetitions are file-local, not independent whole-corpus runs; "
        "between-invocation variability is not measured here.",
        fontsize=9,
    )
    save(fig, "compression-times.png")

    fig, ax = plt.subplots(figsize=(9, 7), layout="constrained")
    extent = 0.0
    for s, label in zip(ordered, labels, strict=True):
        stats = provenance.get(str(s.submission_id), {}).get("timing", {})
        lz77 = stats.get("totals", {}).get("candidate", {}).get("lz77_s")
        if lz77 is not None:
            ax.scatter(
                lz77,
                s.time_s,
                color=colors[s.submission_id],
                label=label,
                marker="s" if s.baseline_key else "o",
            )
            ax.annotate(
                label, (lz77, s.time_s), xytext=(4, 5), textcoords="offset points", fontsize=8
            )
            extent = max(extent, s.time_s, lz77)
    if extent:
        ax.plot([0, extent], [0, extent], "--", color="gray", label="Total = LZ77")
        ax.legend(fontsize=8)
    else:
        ax.text(0.5, 0.5, "No aggregate stage timings", transform=ax.transAxes, ha="center")
    ax.set(
        xlabel="LZ77 seconds (sum of per-file medians)",
        ylabel="Total compression seconds (sum of per-file medians)",
        title="Total compression time vs LZ77 stage",
        xlim=(0, None),
        ylim=(0, None),
    )
    ax.grid(alpha=0.2)
    save(fig, "compression-vs-lz77.png")


if __name__ == "__main__":
    main()
