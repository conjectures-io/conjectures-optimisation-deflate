"""The gate must evaluate every configured competition corpus before passing."""

import json

import pytest
from test_bench_storage import evidence

import bench
from bench.corpora import gate_corpora
from bench.driver import Measurement
from bench.errors import Misconfigured
from bench.results import parse
from service.worker import scored
from verifier import verify
from verifier.workspace import Workspace


def registry(tmp_path):
    validator = tmp_path / "validator"
    validator.mkdir()
    entries = []
    for name in ("corpus-stage1", "corpus-stage2"):
        path = tmp_path / name
        path.mkdir()
        (path / "input").write_bytes(b"data")
        entries.append(
            f'[[corpus]]\nname="{name}"\npath="{name}"\npublic={str(name.endswith("1")).lower()}'
        )
    (validator / "corpora.toml").write_text("\n".join(entries))
    return validator


def test_selection_and_explicit_override(tmp_path, monkeypatch):
    root = registry(tmp_path)
    monkeypatch.delenv("VERIFY_CORPUS", raising=False)
    assert [c.name for c in gate_corpora(root)] == ["corpus-stage1", "corpus-stage2"]
    monkeypatch.setenv("VERIFY_CORPUS", "corpus-stage1")
    assert len(gate_corpora(root)) == 1
    monkeypatch.delenv("VERIFY_CORPUS")
    (tmp_path / "corpus-stage2/input").unlink()
    with pytest.raises(Misconfigured, match="empty"):
        gate_corpora(root)


@pytest.mark.parametrize("reject_second", [False, True])
def test_gate_checks_both_and_combines_worker_totals(tmp_path, monkeypatch, reject_second):
    root = registry(tmp_path)
    monkeypatch.delenv("VERIFY_CORPUS", raising=False)
    workspace = Workspace(verify.ROOT, tmp_path / "work")
    monkeypatch.setattr(verify, "ROOT", root)
    workspace.snapshot("parse.rs", b"source", "slot/generated/parse.rs")
    monkeypatch.setattr(verify, "active_workspace", workspace)
    monkeypatch.setattr(verify, "work_root", workspace.path)
    calls = []

    def run(config, candidates, corpus, **kwargs):
        calls.append(corpus.name)
        raw = evidence("submission")
        raw[0]["methods"]["submission"]["source_sha256"] = workspace.hashes["parse.rs"]
        if reject_second and corpus.name.endswith("2"):
            raw[1]["methods"]["submission"]["errors"] = ["hidden-file-failure"]
        measured = parse("\n".join(json.dumps(r) for r in raw), corpus)
        return Measurement(corpus, (measured,), workspace.path, False)

    monkeypatch.setattr(bench, "run", run)
    results = tmp_path / "results.json"
    assert verify.stage_score(results) == int(reject_second)
    assert calls == ["corpus-stage1", "corpus-stage2"]
    payload = json.loads(results.read_text())
    assert payload["raw_bytes"] == 200
    assert payload["accepted"] is not reject_second
    if not reject_second:
        assert scored(results)["bytes"] == 100
        assert scored(results)["compression_seconds"] == pytest.approx(0.4)
    workspace.finish(0, "never")
