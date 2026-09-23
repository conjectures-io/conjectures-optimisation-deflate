"""Plot coordinates and sample selection must preserve scoring semantics."""

from types import SimpleNamespace as NS

from workers.report import normalize_frontier, plot, timing_observations


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
    assert normalize_frontier(points) == {1: (0, 1), 2: (0.5, 0.25), 3: (1, 0)}
    assert normalize_frontier([points[0]]) == {1: (0, 0)}
    assert normalize_frontier([]) == {}


def test_observations_exclude_warmup_and_preserve_pairs():
    reps = [
        NS(phase="warmup", time_s=100, total_s=200),
        NS(phase="measured", time_s=2, total_s=3),
        NS(phase="measured", time_s=4, total_s=9),
    ]
    run = NS(files=[NS(methods={"candidate": NS(reps=reps)})])
    assert timing_observations([(run, "candidate")]) == [
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
    plot(NS(scores=points), tmp_path, provenance, timings)
    assert len(figures) == 4
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
    assert len(figures["pareto-uncertainty.png"].axes[0].collections) == 8
    assert len(figures["compression-vs-lz77.png"].axes[0].collections) == 4
    plot(NS(scores=[]), tmp_path)
