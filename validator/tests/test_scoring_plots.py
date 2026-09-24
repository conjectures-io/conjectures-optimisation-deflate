"""Plot coordinates and sample selection must preserve scoring semantics."""

from types import SimpleNamespace as NS
from typing import cast

from bench.results import Run
from workers.report import ScoredPoint, ScoringResult, normalize_frontier, plot, timing_observations

# SimpleNamespace carries no static attribute information regardless of what its
# constructor was called with, so every fake built with it is cast to whatever
# protocol/type the function under test actually needs -- the same shape these
# functions already read dynamically (via getattr, or at runtime), just asserted
# once here instead of failing type-checking as bare Any.


def as_points(objs: list[NS]) -> list[ScoredPoint]:
    return cast("list[ScoredPoint]", objs)


def as_runs(pairs: list[tuple[NS, str]]) -> list[tuple[Run, str]]:
    return cast("list[tuple[Run, str]]", pairs)


def as_result(ns: NS) -> ScoringResult:
    return cast(ScoringResult, cast(object, ns))


def point(key, time, ratio, frontier=True):
    return NS(
        submission_id=key,
        time_s=time,
        ratio_pct=ratio,
        on_frontier=frontier,
        baseline_key=f"algorithm-{key}",
        hotkey=None,
        payable_weight=0.0,
        combined_weight=0.5 if frontier else 0.0,
    )


def test_normalization_uses_frontier_extremes():
    points = [point(1, 2, 60), point(2, 4, 30), point(3, 6, 20), point(4, 100, 90, False)]
    assert normalize_frontier(as_points(points)) == {1: (0, 1), 2: (0.5, 0.25), 3: (1, 0)}
    assert normalize_frontier(as_points([points[0]])) == {1: (0, 0)}
    assert normalize_frontier([]) == {}


def test_observations_exclude_warmup_and_preserve_pairs():
    reps = [
        NS(phase="warmup", time_s=100, total_s=200),
        NS(phase="measured", time_s=2, total_s=3),
        NS(phase="measured", time_s=4, total_s=9),
    ]
    run = NS(files=[NS(methods={"candidate": NS(reps=reps)})])
    assert timing_observations(as_runs([(run, "candidate")])) == [
        {"lz77_s": 2, "total_s": 3},
        {"lz77_s": 4, "total_s": 9},
    ]


def test_plot_panels_colors_and_intervals(tmp_path, monkeypatch):
    import matplotlib

    matplotlib.use("Agg")
    import matplotlib.figure
    import numpy as np

    figures = {}
    original = matplotlib.figure.Figure.savefig

    def capture(self, filename, **kwargs):
        figures[filename.name] = self
        return original(self, filename, **kwargs)

    monkeypatch.setattr(matplotlib.figure.Figure, "savefig", capture)
    points = [point(1, 2, 60), point(2, 4, 30), point(3, 6, 20), point(4, 8, 70, False)]
    provenance = {
        str(p.submission_id): {
            "timing": {
                "intervals": {"compression_seconds": [p.time_s * 0.9, p.time_s * 1.1]},
                "totals": {"candidate": {"lz77_s": p.time_s / 2}},
            }
        }
        for p in points
    }
    timings = {
        str(p.submission_id): [{"lz77_s": 0.1, "total_s": 0.2}, {"lz77_s": 0.2, "total_s": 0.4}]
        for p in points
    }
    plot(
        as_result(NS(scores=points)),
        tmp_path,
        cast("dict[str, dict[str, object]]", provenance),
        timings,
    )
    assert len(figures) == 4
    assert all(ax.get_xscale() == "linear" for fig in figures.values() for ax in fig.axes)
    raw, bars, normalized = figures["pareto.png"].axes
    assert normalized.get_xlim() == normalized.get_ylim() == (0, 1)
    box = normalized.get_window_extent()
    assert abs(box.width - box.height) < 1e-6
    assert "unclaimed" not in [tick.get_text() for tick in bars.get_xticklabels()]
    for index in range(3):
        color = raw.collections[index].get_facecolor()[0]
        np.testing.assert_allclose(color, normalized.collections[index].get_facecolor()[0])
        np.testing.assert_allclose(color, bars.patches[index].get_facecolor())
        np.testing.assert_allclose(
            color, figures["compression-times.png"].axes[0].patches[index].get_facecolor()
        )
    assert len(figures["pareto-uncertainty.png"].axes) == 2
    assert len(figures["pareto-uncertainty.png"].axes[0].collections) == 4
    assert len(figures["compression-vs-lz77.png"].axes[0].collections) == 4
    plot(as_result(NS(scores=[])), tmp_path)


def test_repetition_totals_hold_file_mix_constant():
    import pytest

    def file(values):
        return NS(
            methods={
                "candidate": NS(
                    reps=[NS(phase="measured", time_s=v, total_s=2 * v) for v in values]
                )
            }
        )

    # Very different file sizes must not produce a wide box when timings are stable.
    run = NS(files=[file([1, 1, 1]), file([100, 100, 100])])
    assert (
        timing_observations(as_runs([(run, "candidate")])) == [{"lz77_s": 101, "total_s": 202}] * 3
    )
    extra = NS(files=[file([3, 4, 5])])
    assert timing_observations(as_runs([(run, "candidate"), (extra, "candidate")])) == [
        {"lz77_s": 104, "total_s": 208},
        {"lz77_s": 105, "total_s": 210},
        {"lz77_s": 106, "total_s": 212},
    ]
    with pytest.raises(ValueError, match="equal nonzero"):
        timing_observations(as_runs([(NS(files=[file([1]), file([2, 3])]), "candidate")]))


def test_relative_axis_and_intervals_preserve_absolute_telemetry(tmp_path, monkeypatch):
    import matplotlib.figure

    figures = {}
    original = matplotlib.figure.Figure.savefig

    def capture(self, filename, **kwargs):
        figures[filename.name] = self
        return original(self, filename, **kwargs)

    monkeypatch.setattr(matplotlib.figure.Figure, "savefig", capture)
    p = point(1, 20, 30)
    p.normalized_time_ratio = 0.5
    provenance = {
        "1": {
            "timing": {
                "intervals": {"balanced_time_ratio": [0.4, 0.6], "compression_seconds": [19, 21]},
                "totals": {"candidate": {"lz77_s": 10}},
            }
        }
    }
    plot(as_result(NS(scores=[p])), tmp_path, cast("dict[str, dict[str, object]]", provenance))
    raw = figures["pareto.png"].axes[0]
    assert raw.collections[0].get_offsets()[0][0] == 0.5
    assert "incumbent" in raw.get_xlabel()
    uncertain = figures["pareto-uncertainty.png"].axes[0]
    segment = uncertain.collections[0].get_segments()[0]
    assert list(segment[:, 0]) == [0.4, 0.6]
    telemetry = figures["compression-vs-lz77.png"].axes[0]
    assert list(telemetry.collections[0].get_offsets()[0]) == [10, 20]
