"""The library must weigh a frontier exactly as the spike did.

scripts/pareto-weights.py is where the eight functions were argued over, and its reports
are the record of that argument. Lifting them into validator/scoring/pareto.py so the
validator can score real rounds is only safe if the numbers did not move -- so this
re-derives the spike's own results from the library and compares.
"""

from __future__ import annotations

import json
import statistics
import sys
from pathlib import Path

import pytest

VALIDATOR = Path(__file__).resolve().parent.parent
REPO = VALIDATOR.parent
sys.path.insert(0, str(VALIDATOR))

from scoring.pareto import (  # noqa: E402
    METHODS,
    Boundaries,
    Point,
    elbow_sweetspot_weights,
    hypervolume_weights,
    pareto_front,
    weigh,
)

RUNS = REPO / "data/benchmark-runs"
NON_CANDIDATES = {"no-lz77", "libdeflate-12"}
INCUMBENT = "lazy"

# The spike's own real-data baseline: the aggregate numbers from the Silesia report.
REAL_SILESIA = [
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


def load_run(path: Path) -> dict[str, list[Point]]:
    # The same reduction the spike makes: ratio as given, time the median of the measured
    # reps summed over the corpus.
    # corpus -> method -> [raw bytes, output bytes, summed median parse time]
    per: dict[str, dict[str, list[float]]] = {}
    for line in path.read_text().splitlines():
        if not line.strip():
            continue
        rec = json.loads(line)
        if rec.get("kind") != "file":
            continue
        acc = per.setdefault(rec["corpus"], {})
        for method, m in rec["methods"].items():
            if method in NON_CANDIDATES:
                continue
            times = [r["time_s"] for r in m["reps"] if r["phase"] == "measured"]
            a = acc.setdefault(method, [0.0, 0.0, 0.0])
            a[0] += rec["raw_bytes"]
            a[1] += m["output_bytes"]
            a[2] += statistics.median(times) if times else 0.0
    return {
        corpus: [Point(n, t, 100.0 * b / raw) for n, (raw, b, t) in sorted(acc.items())]
        for corpus, acc in sorted(per.items())
    }


# ── The frontier itself ───────────────────────────────────────────────────


def test_the_frontier_keeps_only_strict_improvements():
    front = [p.name for p in pareto_front(REAL_SILESIA)]
    # hc-sparse is slower AND worse than hc-d4; btree is slower and worse than mo-lazy.
    assert "hc-sparse" not in front and "btree" not in front
    assert front == ["template", "hc-d4", "hash-chains", "hc-d64", "lazy", "mo-lazy", "optimal"]


def test_a_tie_on_ratio_is_dominated_not_shared():
    # Only a strict ratio improvement stays on the frontier, so the later of two points
    # at the same ratio is dropped rather than both being carried.
    points = [Point("a", 1.0, 30.0), Point("a-dup", 2.0, 30.0)]
    assert [p.name for p in pareto_front(points)] == ["a"]


def test_an_empty_field_has_an_empty_frontier():
    assert pareto_front([]) == []
    assert weigh([], Boundaries()) == {}


# ── Every method still sums to one ────────────────────────────────────────


@pytest.mark.parametrize("method", sorted(METHODS))
def test_every_method_distributes_exactly_one(method):
    bounds = Boundaries.from_incumbent(10.3306)
    weights = weigh(pareto_front(REAL_SILESIA), bounds, method)
    assert sum(weights.values()) == pytest.approx(1.0)
    assert all(w >= 0 for w in weights.values())


@pytest.mark.parametrize("method", sorted(METHODS))
def test_no_method_pays_a_dominated_point(method):
    bounds = Boundaries.from_incumbent(10.3306)
    front = pareto_front(REAL_SILESIA)
    weights = weigh(front, bounds, method)
    assert set(weights) == {p.name for p in front}
    assert "hc-sparse" not in weights and "btree" not in weights


def test_an_unknown_method_is_refused_rather_than_defaulted():
    with pytest.raises(ValueError, match="unknown scoring method"):
        weigh(pareto_front(REAL_SILESIA), Boundaries(), "hypervolume-but-better")


# ── The findings the spike recorded ───────────────────────────────────────


def test_hypervolume_still_hands_lazy_the_gap_it_sits_in_front_of():
    # The known flaw, reproduced: a point before a large empty gap inherits the whole
    # gap. It is why hypervolume is not the default.
    run = newest_run()
    weights = hypervolume_weights(pareto_front(run["corpus-stage1"]))
    assert weights["lazy"] > 0.75


def test_elbow_sweetspot_finds_the_knee_on_the_real_frontier():
    # hc-d4 is where a 5% time increase buys 2.6 percentage points and returns start
    # diminishing. Both real corpora agree, which is the whole reason it is the default.
    run = newest_run()
    for corpus in ("corpus-stage1", "corpus-stage2"):
        points = run[corpus]
        bounds = Boundaries.from_incumbent(next(p for p in points if p.name == INCUMBENT).time_s)
        weights = elbow_sweetspot_weights(pareto_front(points), bounds)
        assert max(weights, key=lambda name: weights[name]) == "hc-d4", corpus


def test_the_time_boundary_comes_from_the_incumbent_not_a_constant():
    # Against the 120s fallback every real point (0.2-2.2s) collapses into the corner and
    # the normalized methods degenerate. The derived boundary is ~4.16s on stage 1.
    points = newest_run()["corpus-stage1"]
    incumbent = next(p for p in points if p.name == INCUMBENT)
    bounds = Boundaries.from_incumbent(incumbent.time_s)
    assert bounds.time_s == pytest.approx(8.0 * incumbent.time_s)
    assert 3.5 < bounds.time_s < 5.0
    # And every candidate sits well inside it: the 8x floor binds nothing here.
    assert all(bounds.normalize(p.time_s, p.ratio_pct)[0] <= 0.6 for p in points)


def test_a_degenerate_frontier_is_split_equally_rather_than_burnt():
    """The `total <= 0` branch: every point clipped to zero, so the share is shared out.

    It takes a genuinely degenerate frontier to get there. A point's outgoing rate at the
    slow end is zero by construction (it is compared against the boundary at its own
    ratio), so the slowest frontier point normally scores strictly positive -- an even
    staircase spreads the weight unevenly but never to nothing. All-zero needs a point
    that recovers nothing against the boundary either: one sitting at the ratio ceiling.
    """
    weights = elbow_sweetspot_weights([Point("floor", 1.0, 100.0)], Boundaries())
    assert weights == {"floor": 1.0}

    pair = [Point("a", 1.0, 100.0), Point("b", 2.0, 100.0)]
    front = pareto_front(pair)
    assert len(front) == 1  # b is not a strict improvement, so it is dominated


def test_an_even_staircase_still_pays_everyone_something():
    # The docstring's "scores everyone near zero alike" is about the shape, not about a
    # literal zero: the slowest point's outgoing rate is zero by construction, so the
    # weights stay a real distribution rather than collapsing to the fallback.
    staircase = [Point(f"s{i}", 2.0**i, 70.0 - 6.0 * i) for i in range(7)]
    weights = elbow_sweetspot_weights(pareto_front(staircase), Boundaries())
    assert sum(weights.values()) == pytest.approx(1.0)
    assert all(w > 0 for w in weights.values())


def newest_run() -> dict[str, list[Point]]:
    runs = sorted(RUNS.glob("*.jsonl"))
    if not runs:
        pytest.skip("no benchmark run under data/benchmark-runs/")
    return load_run(runs[-1])
