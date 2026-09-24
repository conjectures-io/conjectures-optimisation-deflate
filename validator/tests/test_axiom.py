"""Axiom events: the platform's envelope, off without credentials, and never in the way.

No network: a capturing transport stands in for the ingest endpoint, and a real `AxiomClient`
(its queue, its drain thread, its gzip) runs in front of it, so what the tests read back is
exactly the body Axiom would receive. The weight setter and gate worker tests use in-memory
fakes for the chain and the store, so they need neither a node nor Postgres.
"""

from __future__ import annotations

import datetime as dt
import gzip
import json
import logging
import subprocess
import sys
from collections.abc import Iterator, Mapping
from pathlib import Path
from unittest.mock import Mock

import pytest
from loguru import logger

VALIDATOR = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(VALIDATOR))

from test_weight_setter import PARAMS, FakeChain, at_epoch_boundary  # noqa: E402

import scoring  # noqa: E402
from db import models  # noqa: E402
from observability import axiom  # noqa: E402
from observability.gate import verdict_fields  # noqa: E402
from service import worker  # noqa: E402
from service.settings import Settings  # noqa: E402
from workers.weight_setter import WeightSetterConfig, step  # noqa: E402

# The platform's Severity values (conjectures_subnet/axiom/labels.py), verbatim.
PLATFORM_SEVERITIES = {"debug", "info", "warning", "error", "critical"}
ENVELOPE = {"_time", "severity", "source", "event_type", "environ"}


class Capture:
    """The ingest endpoint: remembers every POST, or fails every one when told to."""

    def __init__(self, fail: bool = False) -> None:
        self.fail = fail
        self.posts: list[tuple[str, bytes, dict[str, str]]] = []

    def __call__(self, url: str, body: bytes, headers: Mapping[str, str], timeout: float) -> None:
        if self.fail:
            raise OSError("connection refused")
        self.posts.append((url, body, dict(headers)))

    def records(self) -> list[dict[str, object]]:
        lines = [gzip.decompress(body).decode() for _, body, _ in self.posts]
        return [json.loads(line) for chunk in lines for line in chunk.splitlines()]


def client(capture: Capture, **kwargs: object) -> axiom.AxiomClient:
    return axiom.AxiomClient(
        dataset="conjectures",
        token="xaat-test",
        environ="dev",
        transport=capture,
        flush_seconds=0.05,
        **kwargs,  # pyright: ignore[reportArgumentType]
    )


@pytest.fixture(autouse=True)
def _fresh_sink() -> Iterator[None]:
    axiom.reset()
    yield
    axiom.reset()


def flushed(capture: Capture) -> list[dict[str, object]]:
    axiom.get_events().close()
    return capture.records()


def of_type(records: list[dict[str, object]], event_type: str) -> list[dict[str, object]]:
    return [r for r in records if r["event_type"] == event_type]


# ── The envelope ──────────────────────────────────────────────────────────


def test_the_envelope_is_the_platforms_and_is_written_last():
    capture = Capture()
    events = axiom.init("competition-gate-worker", client=client(capture), netuid=577)
    events.warning("gate_verdict", submission_id=7, source="spoofed", severity="spoofed")
    events.bind(network="test")
    events.info("service_started", when=dt.date(2026, 9, 24))
    first, second = flushed(capture)

    assert ENVELOPE <= set(first)
    assert first["source"] == "competition-gate-worker"  # a details key cannot displace it
    assert first["severity"] == "warning" and first["event_type"] == "gate_verdict"
    assert first["environ"] == "dev" and first["competition"] == "miniz-oxide"
    assert first["netuid"] == 577 and first["submission_id"] == 7
    stamped = dt.datetime.fromisoformat(str(first["_time"]))
    assert stamped.utcoffset() == dt.timedelta(0)
    assert second["network"] == "test" and second["when"] == "2026-09-24"  # str() fallback
    assert {r["severity"] for r in (first, second)} <= PLATFORM_SEVERITIES
    assert set(axiom.SEVERITIES) == PLATFORM_SEVERITIES


def test_one_gzipped_ndjson_post_to_the_dataset_with_a_bearer_token():
    capture = Capture()
    c = axiom.AxiomClient(
        dataset="a b", token="xaat-1", api_url="https://api.eu.axiom.co/", transport=capture
    )
    for _ in range(3):
        c.ingest(severity="info", source="competition-weight-setter", event_type="x", details={})
    c.close()
    assert len(capture.posts) == 1
    url, body, headers = capture.posts[0]
    assert url == "https://api.eu.axiom.co/v1/datasets/a%20b/ingest"
    assert headers["Authorization"] == "Bearer xaat-1"
    assert headers["Content-Type"] == "application/x-ndjson"
    assert headers["Content-Encoding"] == "gzip"
    assert len(gzip.decompress(body).decode().splitlines()) == 3
    assert c.stats() == {"sent": 3, "dropped": 0, "failed": 0, "queued": 0}


# ── Off unless configured ─────────────────────────────────────────────────


@pytest.mark.parametrize(
    "env",
    [
        {},
        {"AXIOM_TOKEN": "xaat-1"},
        {"AXIOM_DATASET": "d"},
        {"AXIOM_TOKEN": " ", "AXIOM_DATASET": "d"},
    ],
)
def test_without_both_credentials_nothing_is_built_or_bridged(env):
    before = len(logger._core.handlers)  # pyright: ignore[reportAttributeAccessIssue]
    hook = sys.excepthook
    events = axiom.init("competition-chain-watcher", env=env)
    assert isinstance(events.client, axiom.NoopClient) and not events.enabled
    assert len(logger._core.handlers) == before  # pyright: ignore[reportAttributeAccessIssue]
    assert sys.excepthook is hook
    events.error("chain_read_failed", error="nobody is listening")  # and nothing happens


def test_both_credentials_build_a_client_with_the_platforms_defaults():
    built = axiom.client_from_env(
        {"AXIOM_TOKEN": "xaat-1", "AXIOM_DATASET": "conjectures"}, transport=Capture()
    )
    assert isinstance(built, axiom.AxiomClient)
    assert built.url == "https://api.axiom.co/v1/datasets/conjectures/ingest"
    assert built.environ == "default"
    built.close()


# ── Never in the way ──────────────────────────────────────────────────────


def test_a_dead_endpoint_drops_and_counts_and_never_raises():
    capture = Capture(fail=True)
    c = client(capture)
    for _ in range(5):
        c.ingest(severity="error", source="competition-gate-worker", event_type="x", details={})
    c.close()
    c.close()  # idempotent
    assert c.stats()["failed"] == 5 and c.stats()["sent"] == 0


def test_a_full_queue_drops_rather_than_blocks():
    c = client(Capture(), queue_size=1, start=False)
    for _ in range(3):
        c.ingest(severity="info", source="competition-gate-worker", event_type="x", details={})
    assert c.stats()["dropped"] == 2
    c.close()


def test_a_broken_client_cannot_reach_the_caller():
    broken = Mock(enabled=True)
    broken.ingest.side_effect = RuntimeError("telemetry bug")
    broken.close.side_effect = RuntimeError("telemetry bug")
    events = axiom.Events(broken, source="competition-weight-setter")
    events.error("weights_failed", error="x")
    events.close()


# ── The log bridge ────────────────────────────────────────────────────────


def test_errors_logged_anywhere_arrive_as_log_error():
    capture = Capture()
    axiom.init("competition-submission-api", client=client(capture))
    logger.warning("not an error")
    logger.error("the store refused")
    try:
        raise ValueError("boom")
    except ValueError:
        logger.exception("tick failed")
    logging.getLogger("uvicorn.error").error("asgi exploded")
    logger.critical("disk full")
    records = of_type(flushed(capture), "log_error")

    assert [r["message"] for r in records] == [
        "the store refused",
        "tick failed",
        "asgi exploded",
        "disk full",
    ]
    assert [r["severity"] for r in records] == ["error", "error", "error", "critical"]
    first = records[0]
    assert first["source"] == "competition-submission-api"
    assert first["function"] == "test_errors_logged_anywhere_arrive_as_log_error"
    assert first["module"] == "test_axiom" and isinstance(first["line"], int)
    assert "ValueError: boom" in str(records[1]["exception"])
    assert records[2]["logger"] == "uvicorn.error"


def test_reset_removes_the_bridge():
    capture = Capture()
    axiom.init("competition-submission-api", client=client(capture))
    axiom.reset()
    logger.error("after reset")
    assert capture.records() == []


# ── The weight setter ─────────────────────────────────────────────────────


def weights_store() -> Mock:
    store = Mock()
    store.scoring.scoring_inputs.return_value = []
    store.scoring.record_weight_set.return_value = 1
    return store


def test_the_weight_setter_reports_a_set_vector_with_its_split():
    capture = Capture()
    axiom.init("competition-weight-setter", client=client(capture), netuid=66, network="finney")
    chain = FakeChain(hotkeys={"burn": 0}, block=at_epoch_boundary())
    config = WeightSetterConfig(netuid=66, burn_uid=0, dry_run=False)
    assert step(chain, weights_store(), config, scoring.ScoringConfig(), PARAMS).action == "set"
    (event,) = of_type(flushed(capture), "weights_set")
    assert event["severity"] == "info" and event["source"] == "competition-weight-setter"
    assert event["netuid"] == 66 and event["network"] == "finney"
    # An empty round: the treasury is paid everything, and nothing burns.
    assert event["uids"] == [121] and event["weights"] == [1.0]
    assert event["treasury_uid"] == 121 and event["treasury_share"] == 1.0
    assert event["competition_share"] == 0.2 and event["burn_uid"] == 0
    assert event["burn_share"] == 0.0 and event["miners"] == 0
    assert event["dry_run"] is False and isinstance(event["block"], int)
    assert "treasury=" in str(event["summary"])


@pytest.mark.parametrize(
    "config, chain, event_type, severity",
    [
        (
            WeightSetterConfig(netuid=66, dry_run=True),
            FakeChain(hotkeys={"burn": 0}, block=at_epoch_boundary()),
            "weights_planned",
            "info",
        ),
        (
            WeightSetterConfig(netuid=66, dry_run=False),
            FakeChain(uids=(0, 1), block=at_epoch_boundary()),
            "weights_skipped",
            "warning",
        ),
        (
            WeightSetterConfig(netuid=66, dry_run=False),
            FakeChain(block=at_epoch_boundary(), accept=False),
            "weights_failed",
            "error",
        ),
    ],
    ids=["dry-run", "no-treasury", "refused"],
)
def test_the_weight_setter_reports_every_other_outcome(config, chain, event_type, severity):
    capture = Capture()
    axiom.init("competition-weight-setter", client=client(capture))
    _ = step(chain, weights_store(), config, scoring.ScoringConfig(), PARAMS)
    (event,) = of_type(flushed(capture), event_type)
    assert event["severity"] == severity and event["dry_run"] is config.dry_run
    if event_type == "weights_skipped":
        assert "treasury uid 121 absent" in str(event["error"])
    if event_type == "weights_failed":
        assert event["error"] == "the chain refused the vector"


# ── The gate worker ───────────────────────────────────────────────────────


def gate_store(final: str) -> Mock:
    store = Mock()
    store.submissions.files.return_value = {}
    store.submissions.finish.return_value = final
    return store


def claimed(sub_id: int = 7) -> models.Submission:
    return models.Submission(
        id=sub_id,
        hotkey="5Hot",
        baseline_key=None,
        digest="d" * 64,
        claimed_at=dt.datetime(2026, 9, 24, tzinfo=dt.timezone.utc),
        verification_attempt="attempt",
    )


def gate_exits(monkeypatch, code: int, stdout: str = "", measured=None) -> None:
    def fake_gate(directory, results, claim=None, attempt=None):
        return subprocess.CompletedProcess(["verify.py"], code, stdout, "stderr tail")

    monkeypatch.setattr(worker, "run_gate", fake_gate)

    def fake_scored(_results: Path) -> dict[str, int | float]:
        return dict(measured or {})

    def no_admission(*_args: object, **_kwargs: object) -> list[object]:
        return []

    monkeypatch.setattr(worker, "scored", fake_scored)
    monkeypatch.setattr("db.admission.run", no_admission)


MEASURED = {
    "raw_bytes": 8_060_939,
    "bytes": 2_100_000,
    "incumbent_bytes": 2_000_000,
    "parse_seconds": 1.0,
    "compression_seconds": 1.1,
    "incumbent_seconds": 0.5,
    "time_ratio": 2.2,
}


def test_an_accepted_verdict_carries_its_numbers(monkeypatch, tmp_path):
    capture = Capture()
    axiom.init("competition-gate-worker", client=client(capture))
    gate_exits(monkeypatch, 0, "all six stages passed\n", MEASURED)
    final = worker.score_one(gate_store("accepted"), Settings(files=tmp_path), claimed())
    assert final == "accepted"
    (event,) = of_type(flushed(capture), "gate_verdict")
    assert event["severity"] == "info" and event["source"] == "competition-gate-worker"
    assert event["submission_id"] == 7 and event["hotkey"] == "5Hot"
    assert event["state"] == "accepted" and event["stage"] == "6 (score)"
    assert event["reason"] is None and event["bytes"] == 2_100_000
    assert event["vs_incumbent"] == 1.05 and event["time_ratio"] == 2.2
    assert isinstance(event["duration_seconds"], float)


def test_a_rejection_names_its_stage_and_reason(monkeypatch, tmp_path):
    capture = Capture()
    axiom.init("competition-gate-worker", client=client(capture))
    report = "stage 1 ok\n\nREJECTED at stage 2 (static)\n  parse.rs uses unsafe\n"
    gate_exits(monkeypatch, 1, report)
    assert worker.score_one(gate_store("rejected"), Settings(files=tmp_path), claimed()) == (
        "rejected"
    )
    (event,) = of_type(flushed(capture), "gate_verdict")
    assert event["severity"] == "warning" and event["state"] == "rejected"
    assert event["stage"] == "2 (static)" and event["reason"] == "parse.rs uses unsafe"
    assert event["bytes"] is None and event["vs_incumbent"] is None


def test_a_broken_validator_is_an_error_and_the_submission_goes_back(monkeypatch, tmp_path):
    capture = Capture()
    axiom.init("competition-gate-worker", client=client(capture))
    gate_exits(monkeypatch, 2, "\nVALIDATOR ERROR\n  missing syntax checker\n")
    store = gate_store("unused")
    assert worker.score_one(store, Settings(files=tmp_path), claimed()) == "error"
    store.submissions.requeue.assert_called_once()
    records = flushed(capture)
    (verdict,) = of_type(records, "gate_verdict")
    assert verdict["state"] == "error" and verdict["stage"] == "infrastructure"
    (broken,) = of_type(records, "gate_validator_error")
    assert broken["severity"] == "error" and broken["exit_code"] == 2
    assert broken["error"] == "missing syntax checker"
    (requeued,) = of_type(records, "submission_requeued")
    assert requeued["submission_id"] == 7 and "exit 2" in str(requeued["reason"])


def test_a_claim_is_reported_before_the_gate_runs(monkeypatch, tmp_path):
    capture = Capture()
    axiom.init("competition-gate-worker", client=client(capture))
    gate_exits(monkeypatch, 1, "REJECTED at stage 0 (intake)\n  missing Parse.lean\n")
    store = gate_store("rejected")
    store.submissions.claim_next.side_effect = [claimed(), None]
    assert worker.drain(store, Settings(files=tmp_path, worker_id="box-1")) == 1
    records = flushed(capture)
    (claim,) = of_type(records, "submission_claimed")
    assert claim["submission_id"] == 7 and claim["hotkey"] == "5Hot"
    assert claim["worker_id"] == "box-1"
    assert records.index(claim) < records.index(of_type(records, "gate_verdict")[0])


@pytest.mark.parametrize(
    "report, state, gate_state, expected",
    [
        ("", "accepted", "accepted", ("6 (score)", None)),
        ("", "rejected", "accepted", ("entitlement", None)),
        (
            "x\nREJECTED: the gate did not finish within 2700s\n",
            "rejected",
            "rejected",
            ("timeout", None),
        ),
        (
            "REJECTED at stage 5 (axioms)\n  sorryAx\n",
            "rejected",
            "rejected",
            ("5 (axioms)", "sorryAx"),
        ),
        ("", "error", None, (None, None)),
    ],
)
def test_verdict_fields_read_the_report(report, state, gate_state, expected):
    fields = verdict_fields(report, state=state, gate_state=gate_state)
    assert fields["stage"] == expected[0]
    if expected[1] is not None:
        assert fields["reason"] == expected[1]
