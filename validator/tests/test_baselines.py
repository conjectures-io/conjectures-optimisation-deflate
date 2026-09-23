"""Incremental baseline orchestration over real database storage, with tools stubbed."""

import hashlib
import json
import subprocess
from types import SimpleNamespace

from sqlalchemy import func, select
from test_bench_storage import evidence

from bench import baselines
from bench.corpora import Corpus
from bench.driver import Config, Measurement
from bench.results import parse
from db.models import BenchmarkAggregation, BenchmarkRun, Submission
from service.settings import Settings
from verifier.identity import required_fingerprint


def test_seed_resume_add_corpus_and_overwrite(store, tmp_path, monkeypatch):
    root = tmp_path / "validator"
    root.mkdir()
    monkeypatch.setattr(baselines, "ROOT", root)
    settings = Settings(files=tmp_path / "submissions")
    monkeypatch.setattr(baselines, "load", lambda: settings)
    code = tmp_path / "example"
    code.mkdir()
    (code / "parse.rs").write_text("source")
    (code / "Parse.lean").write_text("proof")
    datasets = []
    for name in ("first", "second"):
        path = tmp_path / name
        path.mkdir()
        (path / "a.txt").write_bytes(name.encode())
        datasets.append(Corpus(name, path, False, {}))
    prov = {"engine_sha256": "1" * 64, "template_sha256": "2" * 64, "host_sha256": "3" * 64}

    def provenance(config: Config):
        return prov

    monkeypatch.setattr(baselines, "provenance", provenance)
    verified, measured = [], []

    def verify(command, **kwargs):
        sid = int(command[command.index("--submission-id") + 1])
        stage = command[-1]
        verified.append(stage)
        if stage == "static":
            token, _ = store.verification.begin(
                sid,
                (code / "parse.rs").read_bytes(),
                (code / "Parse.lean").read_bytes(),
                required_fingerprint(),
            )
        else:
            token = store.submissions.get(sid).verification_attempt
        store.verification.publish(sid, token, stage)
        return SimpleNamespace(returncode=0)

    monkeypatch.setattr(subprocess, "run", verify)

    def measure(config, candidates, corpus, **kwargs):
        measured.append(corpus.name)
        raw = evidence("example")
        raw[0]["corpus"] = corpus.name
        raw[0]["measured_rounds"] = 2
        raw[0]["benchmark_provenance"] = prov
        raw[0]["methods"]["example"]["source_sha256"] = hashlib.sha256(
            (code / "parse.rs").read_bytes()
        ).hexdigest()
        payload = (corpus.path / "a.txt").read_bytes()
        raw[1]["raw_bytes"] = len(payload)
        raw[1]["sha256"] = hashlib.sha256(payload).hexdigest()
        for method in raw[1]["methods"].values():
            method["reps"].append(
                {
                    "phase": "measured",
                    "time_s": 0.3,
                    "order_index": 2,
                    "encode_s": 0.0,
                    "total_s": 0.3,
                }
            )
        run = parse("\n".join(json.dumps(x) for x in raw), corpus)
        return Measurement(corpus, (run,), tmp_path, False)

    monkeypatch.setattr(baselines, "run", measure)
    config = Config(root, tmp_path, reps=2, warmup=0)
    baselines.seed_one(store.engine, "example", code, datasets[:1], config)
    baselines.seed_one(store.engine, "example", code, datasets[:1], config)
    assert verified == ["static", "lean"] and measured == ["first"]
    baselines.seed_one(store.engine, "example", code, datasets, config)
    assert measured == ["first", "second"]
    baselines.seed_one(store.engine, "example", code, datasets, config, True)
    assert measured == ["first", "second", "first", "second"]
    assert verified == ["static", "lean"]
    with store.sessions() as session:
        assert session.scalar(select(func.count()).select_from(BenchmarkRun)) == 4
        assert session.scalar(select(func.count()).select_from(BenchmarkAggregation)) == 3
        row = session.scalar(select(Submission))
        assert row.baseline_active and row.hotkey is None and row.state == "accepted"
    points = store.scoring.scoring_inputs()
    assert len(points) == 1 and points[0].baseline_key == "example"
    (code / "parse.rs").write_text("new source")
    baselines.seed_one(store.engine, "example", code, datasets, config)
    with store.sessions() as session:
        assert session.scalar(select(func.count()).select_from(Submission)) == 2
        assert (
            session.scalar(
                select(func.count()).select_from(Submission).where(Submission.baseline_active)
            )
            == 1
        )

    # Reports are reconstructed from DB evidence even after all local JSONL is removed.
    for path in (tmp_path / "data/benchmark-runs/baselines").glob("*.jsonl"):
        path.unlink()
    import db
    from workers.report import main as report

    def connect() -> db.Store:
        return store

    monkeypatch.setattr(db, "connect", connect)
    report(["--out-dir", str(tmp_path / "report")])
    for name in (
        "pareto.png",
        "pareto-uncertainty.png",
        "compression-times.png",
        "compression-vs-lz77.png",
    ):
        assert (tmp_path / "report" / name).is_file()
    payload = json.loads((tmp_path / "report/scores.json").read_text())
    assert payload["burn"] == 1
    assert payload["sources"]
