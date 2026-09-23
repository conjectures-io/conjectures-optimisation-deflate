"""The benchmark analysis on a synthetic run: gate arithmetic, front, stability, run comparison."""

from __future__ import annotations

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from bench import analyze as an  # noqa: E402 - after sys.path
from bench.analyze import FileRec, Meta, MethodRec, Rep  # noqa: E402
from bench.compare import compare  # noqa: E402


def rec(
    output_bytes: int,
    times: list[float],
    sha: str = "t",
    deterministic: bool = True,
    external: bool = False,
) -> MethodRec:
    # One method's record on one file: one warmup rep, then `times` as measured reps.
    reps = [Rep(phase="warmup", order_index=0, time_s=9.9)]
    reps += [Rep(phase="measured", order_index=i + 1, time_s=t) for i, t in enumerate(times)]
    return MethodRec(
        output_bytes=output_bytes,
        tokens_sha256=sha,
        output_sha256=f"o-{output_bytes}",
        deterministic=deterministic,
        external=external,
        encode_s=0.01,
        reps=reps,
    )


def run(scale: float = 1.0) -> tuple[Meta, list[FileRec]]:
    # Two files, four methods; `scale` multiplies every time so compare can see drift.
    def f(name: str, fmt: str, sha: str, inc: int, fast: int, slow: int, ext: int) -> FileRec:
        return FileRec(
            kind="file",
            corpus="c",
            file=name,
            format=fmt,
            raw_bytes=1000,
            sha256=sha,
            methods={
                "incumbent": rec(inc, [0.10 * scale, 0.11 * scale]),
                "fast-worse": rec(fast, [0.05 * scale, 0.05 * scale]),
                "slow-better": rec(slow, [0.90 * scale, 0.95 * scale]),
                "libdeflate-12": rec(ext, [0.30 * scale, 0.31 * scale], external=True),
            },
        )

    meta: Meta = {
        "kind": "meta",
        "corpus": "c",
        "speed_floor": 8.0,
        "methods": {"incumbent": {"source_sha256": "abc"}},
        "cpu_model": "cpu",
        "rustc_version": "rustc",
    }
    files = [
        f("a.txt", "text", "s1", 500, 600, 450, 400),
        f("b.bin", "binary", "s2", 900, 950, 890, 850),
    ]
    return meta, files


def test_pooled_bytes_and_median_time_match_the_gate_arithmetic():
    _, files = run()
    pb = an.pooled_bytes(files)
    pt = an.pooled_median_time(an.per_file_median_time(an.flatten(files)))
    assert pb["incumbent"] == 1400 and pb["slow-better"] == 1340 and pb["fast-worse"] == 1550
    assert round(pt["incumbent"], 2) == 0.21 and pt["slow-better"] == 1.85  # warmups excluded
    assert round(pt["slow-better"] / pt["incumbent"], 2) == 8.81  # over the 8x floor


def test_front_excludes_the_external_reference_and_dominated_methods():
    _, files = run()
    pb = an.pooled_bytes(files)
    pt = an.pooled_median_time(an.per_file_median_time(an.flatten(files)))
    assert an.pareto_front(pb, pt, {"libdeflate-12"}) == ["slow-better", "incumbent", "fast-worse"]


def test_stability_flags_noise_and_nondeterminism():
    _, files = run()
    files[0]["methods"]["fast-worse"]["reps"][2]["time_s"] = 0.08
    files[1]["methods"]["slow-better"]["deterministic"] = False
    s = an.stability(files, an.per_file_spread(an.flatten(files)))
    assert round(s["fast-worse"][0], 6) == 1.6 and s["fast-worse"][1] == 1
    assert s["slow-better"][2] is False and s["incumbent"][2] is True


def test_compare_accepts_the_same_run_and_rejects_changed_bytes_or_slow_drift():
    a, b = run(), run()
    assert compare(a, b) == []
    b[1][0]["methods"]["fast-worse"]["output_bytes"] = 601
    b[1][0]["methods"]["fast-worse"]["tokens_sha256"] = "u"
    assert any("different tokens" in p for p in compare(a, b))
    assert any("pooled median parse time" in p for p in compare(a, run(scale=1.5)))


def test_report_names_the_verdict_the_gate_would_give():
    meta, files = run()
    text = an.report(meta, files, "/x/run.jsonl")
    assert "| slow-better | 1,340 | 0.9571x | 8.81x | over the floor |" in text
    assert "| fast-worse | 1,550 | 1.1071x | 0.48x | no improvement |" in text
    assert "| libdeflate-12 | 1,250 | 0.8929x | 2.90x | reference |" in text
    assert "`slow-better`, `incumbent`, `fast-worse`" in text
