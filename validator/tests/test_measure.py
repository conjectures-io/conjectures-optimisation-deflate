"""What the benchmark's isolation is worth: nothing writable while measuring,
concurrent runs that cannot touch each other, and a misbehaving parser that is
named rather than merely fatal.

These build real cdylibs and run the real engine, so they are `slow` and skip
when the engine has not been built (`just build`).

    pytest validator/tests/test_measure.py
"""

from __future__ import annotations

import dataclasses
import shutil
import sys
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

import pytest

VALIDATOR = Path(__file__).resolve().parent.parent
REPO = VALIDATOR.parent
PARSERS = Path(__file__).resolve().parent / "parsers"

#: Two real submissions, run at the same time against the same incumbent.
EXAMPLES = {
    "template": "miner/template/parse.rs",
    "hash-chains": "miner/examples/hash-chains/parse.rs",
}

sys.path.insert(0, str(VALIDATOR))
import bench  # noqa: E402 - after sys.path so the sibling package resolves
from bench import corpora, results  # noqa: E402
from sandbox import bwrap  # noqa: E402

pytestmark = pytest.mark.slow


def config(keep: bench.Keep = bench.Keep.NEVER) -> bench.Config:
    # Two reps: these tests are about isolation and attribution, not timing.
    return dataclasses.replace(
        bench.Config.from_env(VALIDATOR), reps=2, warmup=1, bars=False, keep=keep
    )


@pytest.fixture(scope="module")
def corpus() -> corpora.Corpus:
    if not config().engine.exists():
        pytest.skip("the measurement engine is not built - run `just build`")
    return corpora.default(VALIDATOR)


def touch(sandbox: bwrap.Sandbox, target: Path) -> bwrap.Result:
    return bwrap.run(sandbox, ["touch", str(target)], cwd=None, timeout=60)


def test_measuring_can_write_nothing_at_all(tmp_path: Path, corpus: corpora.Corpus):
    # Every path the engine can see, including one reached through a symlink:
    # ro_binds are read-only by construction, but a shared path that resolved
    # through the rw set would not be, and that is the mistake worth catching.
    workspace = tmp_path / "run"
    workspace.mkdir()
    link = tmp_path / "corpus-link"
    link.symlink_to(corpus.path, target_is_directory=True)
    sandbox = bench.measure_sandbox(config(), workspace, corpus)
    if not sandbox.enabled:
        pytest.skip("VERIFY_SANDBOX=off")
    for target in (corpus.path, link, workspace, VALIDATOR, REPO):
        assert touch(sandbox, target / "written-by-the-candidate").returncode != 0, (
            f"{target} was writable while measuring"
        )
        assert not (target / "written-by-the-candidate").exists()


def test_building_may_write_its_own_workspace_and_nothing_else(
    tmp_path: Path, corpus: corpora.Corpus
):
    workspace = tmp_path / "run"
    workspace.mkdir()
    sandbox = bench.build_sandbox(config(), workspace)
    if not sandbox.enabled:
        pytest.skip("VERIFY_SANDBOX=off")
    assert touch(sandbox, workspace / "target-goes-here").returncode == 0
    for target in (corpus.path, VALIDATOR, REPO):
        assert touch(sandbox, target / "written-by-the-build").returncode != 0
        assert not (target / "written-by-the-build").exists()


def test_concurrent_runs_do_not_collide(corpus: corpora.Corpus):
    # Separate workspaces, separate target/, separate engine processes -- and
    # the incumbent, measured independently in each, must agree byte for byte.
    cfg = config()

    def measure(name: str) -> bench.Measurement:
        return bench.run(cfg, {name: REPO / EXAMPLES[name]}, corpus)

    with ThreadPoolExecutor(max_workers=2) as pool:
        done = list(pool.map(measure, EXAMPLES))

    a, b = done
    for measurement in done:
        assert measurement.only().meta.schema_version == 4
        for file in measurement.only().files:
            for method in file.methods.values():
                assert len(method.reps) == 3
                for rep in method.reps:
                    assert rep.encode_s is not None and rep.encode_s > 0
                    assert rep.total_s == pytest.approx(rep.time_s + rep.encode_s)
    assert a.workspace != b.workspace
    assert not a.workspace.exists() and not b.workspace.exists()
    for f, g in zip(a.only().files, b.only().files):
        assert f.methods["incumbent"].output_sha256 == g.methods["incumbent"].output_sha256
    byte_disagreement = [
        w for w in results.incumbent_agreement([a.only(), b.only()]) if "compressed" in w
    ]
    assert byte_disagreement == []


def test_each_parser_call_gets_a_clean_output_buffer(tmp_path: Path):
    if not config().engine.exists():
        pytest.skip("the measurement engine is not built - run `just build`")
    # The incumbent runs immediately before this parser on every round. Its first
    # token is a nonzero literal, so a shared, uncleared buffer makes this panic.
    corpus_dir = tmp_path / "corpus"
    corpus_dir.mkdir()
    (corpus_dir / "text.txt").write_bytes(b"A clean output buffer matters.\n" * 8)
    source = tmp_path / "clean_buffer.rs"
    source.write_text(
        "pub fn parse(input: &[u8], out: &mut [u32]) -> usize {\n"
        "    assert!(out.iter().all(|&token| token == 0));\n"
        "    for (i, &byte) in input.iter().enumerate() { out[i] = byte as u32; }\n"
        "    input.len()\n"
        "}\n"
    )
    local_corpus = corpora.Corpus("clean-buffer", corpus_dir, True, {})
    run = bench.run(config(), {"clean-buffer": source}, local_corpus).only()
    assert not run.failures("clean-buffer")
    assert len(run.files[0].methods["clean-buffer"].reps) == 3


def test_a_panicking_parser_is_a_correctness_failure_not_a_crash(corpus: corpora.Corpus):
    m = bench.run(config(), {"panics": PARSERS / "panics.rs"}, corpus)
    run = m.only()
    failures = run.failures("panics")
    assert failures, "a panicking parser produced no failure"
    assert all("panicked" in f for f in failures)
    # The incumbent shared the process and was measured anyway.
    assert run.totals("incumbent").output_bytes > 0
    assert not run.failures("incumbent")


def test_a_stack_overflow_kills_only_its_own_process_and_is_named(corpus: corpora.Corpus):
    with pytest.raises(bench.Crashed) as e:
        bench.run(config(bench.Keep.AUTO), {"overflows": PARSERS / "overflows.rs"}, corpus)
    assert e.value.method == "overflows"
    # A crashed run keeps its workspace on purpose: it is what you look at after.
    assert e.value.workspace.is_dir()
    shutil.rmtree(e.value.workspace)


def test_a_parser_that_does_not_compile_is_named(tmp_path: Path, corpus: corpora.Corpus):
    broken = tmp_path / "parse.rs"
    broken.write_text("pub fn parse(input: &[u8], out: &mut [u32]) -> usize { nope }\n")
    with pytest.raises(bench.BuildFailed) as e:
        bench.run(config(), {"broken": broken}, corpus)
    assert e.value.method == "broken"
    assert "cannot find value `nope`" in e.value.detail


def test_full_compression_timings_include_every_round_and_external_references(tmp_path: Path):
    cfg = dataclasses.replace(config(), bars=True)
    if not cfg.engine.exists():
        pytest.skip("run just build first")
    (tmp_path / "text.txt").write_bytes(b"repeatable compression timing example\n" * 1000)
    corpus = corpora.Corpus("timing-smoke", tmp_path, True, {})
    measured = bench.run(cfg, {"template": REPO / EXAMPLES["template"]}, corpus)
    run = measured.only()
    assert run.meta.schema_version == 4
    assert not run.failures("template")
    for result in run.files[0].methods.values():
        assert result.ok and len(result.measured_total) == 2
        assert len(result.reps) == 3
        for rep in result.reps:
            assert rep.total_s is not None and rep.total_s > 0
            if result.external:
                assert rep.encode_s is None and rep.total_s == rep.time_s
            else:
                assert rep.encode_s is not None and rep.encode_s > 0
                assert rep.total_s == pytest.approx(rep.time_s + rep.encode_s)
    from bench.report import summary

    methods = summary(measured)["methods"]
    assert isinstance(methods, dict)
    assert methods["miniz_oxide-1"]["parse_s"] is None
    assert methods["miniz_oxide-1"]["total_s"] > 0
