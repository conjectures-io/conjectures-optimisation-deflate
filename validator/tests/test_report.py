"""The half of the benchmark that is policy rather than measurement: the speed
floor, the correctness rule, and what may be said about a held-out corpus.

Synthetic measurements, no engine, no compiler -- these run anywhere in
milliseconds, which is the point of keeping the decision out of Rust.
"""

from __future__ import annotations

import sys
from pathlib import Path

VALIDATOR = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(VALIDATOR))
from bench import report, verdict  # noqa: E402
from bench.corpora import Corpus  # noqa: E402
from bench.driver import Measurement  # noqa: E402
from bench.results import (  # noqa: E402
    FileResult,
    Meta,
    MethodMeta,
    MethodResult,
    Rep,
    Run,
    incumbent_agreement,
)

PUBLIC = Corpus(name="open", path=Path("/corpus"), public=True, formats={"a.txt": "text"})
HELD_OUT = Corpus(name="held-out", path=Path("/corpus"), public=False, formats={})


def method(name: str, out_bytes: int, times: list[float], **over: object) -> MethodResult:
    reps = [Rep(phase="warmup", order_index=0, time_s=9.9, encode_s=0.0, total_s=9.9)]
    reps += [Rep("measured", i + 1, t, encode_s=0.0, total_s=t) for i, t in enumerate(times)]
    fields: dict[str, object] = {
        "external": False,
        "output_bytes": out_bytes,
        "output_sha256": f"o-{out_bytes}",
        "tokens": 10,
        "tokens_sha256": "t",
        "deterministic": True,
        "encode_s": 0.01,
        "errors": (),
        "reps": tuple(reps),
    }
    return MethodResult(name=name, **(fields | over))  # pyright: ignore[reportArgumentType]


def run_of(candidate: str, methods: dict[str, MethodResult], files: int = 2) -> Run:
    meta = Meta(
        schema_version=4,
        started_at_unix=0.0,
        corpus="open",
        corpus_dir="/corpus",
        os="linux",
        arch="x86_64",
        rustc_version="rustc 1.90.0",
        cpu_model=None,
        cpu_governor=None,
        warmup_rounds=1,
        measured_rounds=2,
        speed_floor=8.0,
        methods={
            n: MethodMeta(external=False, crate_dir=None, source_sha256=f"s-{n}", lib_sha256=None)
            for n in ["incumbent", candidate]
        },
    )
    return Run(
        meta=meta,
        files=tuple(FileResult(f"f{i}.txt", "text", 1000, f"h{i}", methods) for i in range(files)),
    )


def measurement(corpus: Corpus, *runs: Run) -> Measurement:
    return Measurement(corpus=corpus, runs=runs, workspace=Path("/gone"), kept=False)


def simple(candidate: str, inc: int, cand: int, inc_t: float, cand_t: float) -> Run:
    return run_of(
        candidate,
        {
            "incumbent": method("incumbent", inc, [inc_t, inc_t + 0.01]),
            candidate: method(candidate, cand, [cand_t, cand_t + 0.01]),
        },
    )


def test_slow_benchmarks_preserve_results_for_scoring():
    v = verdict.judge(simple("c", 500, 400, 0.10, 0.90), "c")
    assert v.accepted and v.slowdown > 8
    assert verdict.judge(simple("c", 500, 400, 0.10, 100), "c", 8.0).accepted


def test_a_correct_parser_inside_the_floor_is_accepted_even_when_larger():
    v = verdict.judge(simple("c", 500, 600, 0.10, 0.10), "c")
    assert v.accepted and not v.improved and "20.000% larger" in v.reason


def test_smaller_is_accepted_and_improved():
    v = verdict.judge(simple("c", 500, 450, 0.10, 0.10), "c")
    assert v.accepted and v.improved and "10.000% smaller" in v.reason
    assert v.line().startswith("ACCEPTED — ")


def test_a_correctness_failure_beats_every_other_verdict():
    run = run_of(
        "c",
        {
            "incumbent": method("incumbent", 500, [0.1, 0.1]),
            "c": method("c", 400, [0.1, 0.1], errors=("parse panicked",)),
        },
    )
    v = verdict.judge(run, "c")
    assert not v.accepted and "2 correctness failure(s)" in v.reason
    assert all("parse panicked" in f for f in v.failures)


def test_a_broken_incumbent_invalidates_the_run_rather_than_the_candidate():
    run = run_of(
        "c",
        {
            "incumbent": method("incumbent", 500, [0.1, 0.1], deterministic=False),
            "c": method("c", 400, [0.1, 0.1]),
        },
    )
    assert "the incumbent failed" in verdict.judge(run, "c").reason


def test_a_held_out_corpus_reports_totals_and_no_per_file_numbers():
    m = measurement(HELD_OUT, simple("c", 500, 450, 0.1, 0.1))
    summary = report.summary(m)
    assert "files" not in summary
    assert summary["corpus"] == {"name": "held-out", "public": False}
    methods = summary["methods"]
    assert isinstance(methods, dict) and methods["c"]["output_bytes"] == 900
    text = report.table(m)
    assert "held out; totals only" in text and "f0.txt" not in text


def test_a_public_corpus_reports_every_file():
    summary = report.summary(measurement(PUBLIC, simple("c", 500, 450, 0.1, 0.1)))
    files = summary["files"]
    assert isinstance(files, list) and len(files) == 2
    assert files[0]["methods"]["c"]["output_bytes"] == 450
    assert "f0.txt" in report.table(measurement(PUBLIC, simple("c", 500, 450, 0.1, 0.1)))


def test_several_candidates_merge_into_one_record_per_file():
    m = measurement(PUBLIC, simple("a", 500, 450, 0.1, 0.1), simple("b", 500, 400, 0.1, 0.2))
    merged = report.merge(m)
    assert len(merged) == 2
    assert sorted(merged[0].methods) == ["a", "b", "incumbent"]
    assert m.candidates() == ("a", "b")
    assert report.summary(m)["candidates"] == ["a", "b"]


def test_an_incumbent_that_disagrees_with_itself_is_a_warning_about_the_host():
    slow = simple("b", 500, 400, 0.5, 0.2)
    m = measurement(PUBLIC, simple("a", 500, 450, 0.1, 0.1), slow)
    assert any("varied" in w for w in m.warnings())
    assert incumbent_agreement([]) == ()


def test_an_incumbent_that_compresses_differently_is_a_hard_warning():
    a = simple("a", 500, 450, 0.1, 0.1)
    b = run_of(
        "b",
        {
            "incumbent": method("incumbent", 501, [0.1, 0.11]),
            "b": method("b", 400, [0.1, 0.11]),
        },
    )
    assert any("compressed it differently" in w for w in measurement(PUBLIC, a, b).warnings())
