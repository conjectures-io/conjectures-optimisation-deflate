"""Human explanations and visualizations from the stored admission contract."""

from __future__ import annotations

import textwrap
from collections.abc import Sequence
from pathlib import Path
from typing import TypedDict, cast

from db.admission import PointPayload
from db.admission_statistics import AdmissionComparison
from scoring.combine import HotkeyScore


class AdmissionDetail(TypedDict):
    """The stored admission contract (db.admission.evaluate's `detail`), as read back
    here for reporting. Every outcome sets these three -- see AdmissionDetailExtra for
    the rest, which only a fully evaluated point (not pending/invalid_evidence) has.
    """

    outcome: str
    reason_code: str
    candidate: PointPayload


class AdmissionDetailExtra(AdmissionDetail, total=False):
    error: str
    reference: PointPayload | None
    frontier_before: list[PointPayload]
    statistics: AdmissionComparison | None
    preview: bool
    admission_check_id: int | None
    decision_key: str


def explanation(detail: AdmissionDetailExtra) -> str:
    status = detail["outcome"]
    stats = detail.get("statistics")
    if stats:
        gain, lower = stats["gain_pct"], stats["lower_pct"]
        reference = detail.get("reference")
        assert reference is not None
        delta = detail["candidate"]["compression_pct"] - reference["compression_pct"]
        compression = (
            "equal compression"
            if delta == 0
            else f"compression ratio {delta:.4g} percentage points worse"
        )
        measured = f"measured {abs(gain):.3f}% {'faster' if gain >= 0 else 'slower'}"
        uncertainty = (
            f"lower confidence bound is {lower:.3f}% faster"
            if lower > 0
            else f"uncertainty allows {abs(lower):.3f}% slower or equal speed"
        )
        return (
            f"{status}: {measured} than {reference['label']}; {uncertainty}; "
            f"{compression}. {'Qualifies.' if status == 'passed' else 'Does not qualify.'}"
        )
    return {
        "not_required": "No slower, better-compressing neighbor: speed test not required.",
        "dominated": "An admitted point is at least as fast and compresses at least as well.",
        "pending": "Awaiting admission or explicit replay of preceding evidence.",
        "invalid_evidence": "Admission could not be evaluated: "
        + detail.get("error", "invalid evidence"),
    }.get(status, status)


def comparison_range(detail: AdmissionDetailExtra) -> tuple[float, float] | None:
    stats = detail.get("statistics")
    if not stats:
        return None
    reference = detail.get("reference")
    assert reference is not None
    anchor = reference["time_ratio"]
    return anchor * (1 - stats["upper_pct"] / 100), anchor * (1 - stats["lower_pct"] / 100)


def _detail(score: HotkeyScore) -> AdmissionDetailExtra:
    # Callers only reach this on scores selected for having a truthy `.admission`.
    assert score.admission is not None
    return cast(AdmissionDetailExtra, cast(object, score.admission))


def plot_admission(scores: Sequence[HotkeyScore], directory: Path) -> None:
    import matplotlib

    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    from matplotlib.axes import Axes

    # A current report must not retain plots for comparisons that no longer apply.
    detail_dir = directory / "admission"
    for old_plot in detail_dir.glob("submission-*.png"):
        old_plot.unlink()
    (directory / "speed-admission.png").unlink(missing_ok=True)
    selected = [s for s in scores if s.admission]
    selected.sort(key=lambda s: s.submission_id)
    if not selected:
        return
    cmap = plt.get_cmap("tab20" if len(selected) <= 20 else "turbo")
    colors = {
        s.submission_id: cmap(i if len(selected) <= 20 else i / (len(selected) - 1))
        for i, s in enumerate(selected)
    }
    fig, ax = plt.subplots(figsize=(12, max(4, len(selected) * 0.55)), layout="constrained")
    labels: list[str] = []
    for i, score in enumerate(selected):
        detail = _detail(score)
        labels.append(f"{detail['candidate']['label']} — {detail['outcome']}")
        stats = detail.get("statistics")
        color = colors[score.submission_id]
        if stats:
            ax.hlines(i, stats["lower_pct"], stats["upper_pct"], color=color, linewidth=3)
            ax.plot([stats["lower_pct"], stats["upper_pct"]], [i, i], "|", color=color)
            ax.scatter(stats["gain_pct"], i, color=color, zorder=3)
        else:
            ax.text(0.02, i, "No speed interval", transform=ax.get_yaxis_transform(), fontsize=8)
    ax.axvline(0, color="black", linestyle="--", linewidth=1)
    ax.set_yticks(range(len(selected)), labels)
    ax.set_ylim(len(selected) - 0.5, -0.5)
    ax.set(
        xlabel="Speed gain over the selected reference (%) — positive is faster",
        title="Statistical speed admission"
        + (" (read-only preview)" if any(_detail(s).get("preview") for s in selected) else ""),
    )
    ax.grid(axis="x", alpha=0.2)
    fig.supxlabel(
        "Dots: measured gains. Lines: central 90% intervals (5th–95th percentiles).\n"
        "Pass requires a strictly positive one-sided 95% lower bound. Excludes host drift.",
        fontsize=9,
    )
    fig.savefig(directory / "speed-admission.png", dpi=150)
    plt.close(fig)
    detail_dir.mkdir(exist_ok=True)
    for score in selected:
        detail = _detail(score)
        stats = detail.get("statistics")
        if not stats:
            continue
        # plt.subplots' stub can't size a 3-row unpack, so it types the tuple Any;
        # pre-declaring each axes' real type gets everything past this line typed
        # properly (same as the single-axes plot above).
        gain_ax: Axes
        time_ax: Axes
        pareto_ax: Axes
        fig, (gain_ax, time_ax, pareto_ax) = plt.subplots(
            3, 1, figsize=(11, 12), height_ratios=[1, 1, 2], layout="constrained"
        )
        color = colors[score.submission_id]
        gain_ax.axvline(0, color="black", linestyle="--")
        gain_ax.hlines(0, stats["lower_pct"], stats["upper_pct"], color=color, linewidth=3)
        gain_ax.scatter(stats["gain_pct"], 0, color=color)
        gain_ax.set(
            yticks=[],
            ylim=(-0.6, 0.6),
            xlabel="Gain over reference (%) — positive is faster",
            title=f"{detail['outcome'].upper()}: measured {stats['gain_pct']:+.3f}% gain\n"
            f"95% lower bound: {stats['lower_pct']:+.3f}% (must exceed 0%)",
        )
        gain_ax.text(
            0.98,
            0.85,
            f"90% interval: [{stats['lower_pct']:+.3f}%, {stats['upper_pct']:+.3f}%]",
            transform=gain_ax.transAxes,
            ha="right",
            fontsize=10,
        )
        gain_ax.grid(axis="x", alpha=0.25)
        before = detail.get("frontier_before")
        reference = detail.get("reference")
        assert before is not None and reference is not None
        candidate = detail["candidate"]
        pareto_ax.plot(
            [p["time_ratio"] for p in before],
            [p["compression_pct"] for p in before],
            "--",
            color="gray",
            label="Previously admitted frontier",
        )
        pareto_ax.scatter(
            [p["time_ratio"] for p in before],
            [p["compression_pct"] for p in before],
            color="gray",
            s=20,
        )
        pareto_ax.scatter(
            reference["time_ratio"],
            reference["compression_pct"],
            marker="s",
            color="black",
            label="Reference: " + reference["label"],
        )
        pareto_ax.scatter(
            candidate["time_ratio"],
            candidate["compression_pct"],
            facecolors=color if detail["outcome"] == "passed" else "none",
            edgecolors=color,
            s=80,
            label="Candidate: " + candidate["label"],
        )
        interval = comparison_range(detail)
        # comparison_range returns None only when detail lacks "statistics", which this
        # branch (stats truthy, same detail) already ruled out.
        assert interval is not None
        time_ax.scatter(reference["time_ratio"], 1, marker="s", color="black", zorder=3)
        time_ax.scatter(candidate["time_ratio"], 0, color=color, zorder=3)
        time_ax.hlines(0, *interval, color=color, linewidth=3)
        time_ax.plot(interval, [0, 0], "|", color=color, markersize=12)
        for value, y in [(reference["time_ratio"], 1), (candidate["time_ratio"], 0)]:
            time_ax.annotate(
                f"{value:.6f}×", (value, y), xytext=(0, 12), textcoords="offset points", ha="center"
            )
        time_ax.set(
            yticks=[0, 1],
            yticklabels=["Candidate", "Reference"],
            ylim=(-0.5, 1.6),
            xlabel="Mean file time / incumbent — lower is faster",
            title="Scored time comparison (normalized, not elapsed seconds)",
        )
        time_ax.grid(axis="x", alpha=0.25)
        time_ax.margins(x=0.15)
        pareto_ax.hlines(
            candidate["compression_pct"],
            *interval,
            color=color,
            linewidth=2,
            label="Relative comparison range (reference anchored)",
        )
        xs = [candidate["time_ratio"], reference["time_ratio"], *interval]
        ys = [candidate["compression_pct"], reference["compression_pct"]]
        dx, dy = max(max(xs) - min(xs), max(xs) * 0.02), max(max(ys) - min(ys), 0.01)
        pareto_ax.set(
            xlim=(max(0, min(xs) - dx * 0.2), max(xs) + dx * 0.2),
            ylim=(min(ys) - dy * 0.2, max(ys) + dy * 0.2),
            xlabel="Mean file time / incumbent",
            ylabel="Balanced compression ratio (%)",
            title="Historical comparison (zoomed)",
        )
        pareto_ax.legend(fontsize=7)
        fig.suptitle(textwrap.fill(explanation(detail), 105), fontsize=11)
        fig.supxlabel(
            "Intervals: central 90%; admission uses one-sided 95% lower bound.\n"
            "Time ranges anchor the reference at its measured value; "
            "they are comparison intervals.\n"
            "Uncertainty covers measured repetitions, not host drift. "
            "Per-file diagnostics: separate image.",
            fontsize=9,
        )
        fig.savefig(detail_dir / f"submission-{score.submission_id}.png", dpi=150)
        plt.close(fig)

        # Long file labels must not squeeze the aggregate comparison panels.
        fig, file_ax = plt.subplots(
            figsize=(11, max(5, len(stats["files"]) * 0.24)), layout="constrained"
        )
        files = stats["files"]
        file_ax.axvline(0, color="black", linestyle="--")
        file_ax.scatter([f["gain_pct"] for f in files], range(len(files)), color=color, s=18)
        file_ax.set_yticks(
            range(len(files)), [f"{f['corpus']}/{f['file']}" for f in files], fontsize=8
        )
        file_ax.invert_yaxis()
        file_ax.set(
            xlabel="Per-file gain in incumbent-normalized time (%)",
            title=f"Faster on {stats['file_wins']}/{len(files)} files; {stats['file_ties']} ties",
        )
        file_ax.grid(axis="x", alpha=0.25)
        fig.suptitle(f"{candidate['label']} vs {reference['label']} — per-file diagnostics")
        fig.supxlabel("File wins are diagnostic; aggregate gain is not their mean.", fontsize=9)
        fig.savefig(detail_dir / f"submission-{score.submission_id}-files.png", dpi=150)
        plt.close(fig)
