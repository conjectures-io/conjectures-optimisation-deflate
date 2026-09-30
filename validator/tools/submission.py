"""Queue local diagnostic/baseline submissions and inspect persisted milestones."""

from __future__ import annotations

import argparse
import dataclasses
import datetime as dt
import hashlib
import json
import re
import shutil
import sys
import time
from pathlib import Path
from typing import TypedDict, cast

from sqlalchemy import select, text

import db
from db import models
from db.admission_statistics import AdmissionComparison
from service.settings import MAX_FILE_BYTES, load
from service.storage import write_submission


def enqueue(store: db.Store, directory: Path, files: Path, baseline: str | None = None) -> int:
    source, proof = ((directory / name).read_bytes() for name in ("parse.rs", "Parse.lean"))
    if any(not data or len(data) > MAX_FILE_BYTES for data in (source, proof)):
        raise ValueError(f"Each file must be nonempty and at most {MAX_FILE_BYTES} bytes")
    if baseline is not None and not re.fullmatch(r"[A-Za-z0-9][A-Za-z0-9._-]{0,79}", baseline):
        raise ValueError("Baseline name must be 1–80 letters, digits, dots, underscores or hyphens")
    key = f"local:{baseline}" if baseline is not None else None
    created = None
    try:
        with store.sessions.begin() as session:
            if key:
                session.execute(text("SELECT pg_advisory_xact_lock(771002002)"))
                if session.scalar(
                    select(models.Submission.id).where(models.Submission.baseline_key == key)
                ):
                    raise ValueError("Baseline name already exists; choose a new name")
            row = models.Submission(
                hotkey=None,
                baseline_key=key,
                baseline_active=key is not None,
                digest=hashlib.sha256(source + proof).hexdigest(),
                state="queued",
            )
            session.add(row)
            session.flush()
            destination = files / str(row.id)
            destination.mkdir(parents=True, exist_ok=False)
            created = destination
            # Queue visibility begins only after both files are durable and DB commits.
            write_submission(destination, source, proof)
            sid = row.id
        return sid
    except BaseException:
        if created is not None:
            shutil.rmtree(created)
        raise


class MetricsPayload(TypedDict):
    total_s: float | None
    lz77_s: float | None
    byte_weighted_compression_pct: float | None


class ScorePayload(TypedDict):
    allocated: float
    payable: float
    frontier: bool
    burn_reason: str | None
    weight_set_id: int
    dry_run: bool
    chain_accepted: bool


class AggregationPayload(TypedDict):
    id: int | None
    statistics: dict[str, object] | None


class MilestonePayload(TypedDict):
    passed_at: dt.datetime | None


class BenchmarkPayload(TypedDict):
    measured_source_sha256: str | None


class AdmissionPayload(TypedDict):
    id: int | None
    # Ad hoc statuses this tool synthesizes itself (e.g. "stale-verification") carry
    # extra keys (like "message") that db.admission's own detail shape doesn't, so this
    # stays a plain dict rather than db.admission.AdmissionDetailExtra.
    details: dict[str, object] | None
    recorded_details: dict[str, object] | None
    excluded_test: bool


class StatusPayload(TypedDict):
    identical_source_submissions: list[int]
    metrics: MetricsPayload
    score: ScorePayload | None
    id: int
    kind: str
    hotkey: str | None
    baseline_key: str | None
    state: str
    worker: str | None
    submitted_at: dt.datetime
    claimed_at: dt.datetime | None
    finished_at: dt.datetime | None
    preverification: MilestonePayload
    lean_verification: MilestonePayload
    benchmark: BenchmarkPayload
    aggregation: AggregationPayload
    admission: AdmissionPayload
    exit_code: int | None
    report: str | None
    note: str


def status(store: db.Store, sid: int) -> StatusPayload:
    with store.sessions() as session:
        row = session.get(models.Submission, sid)
        if row is None:
            raise ValueError(f"No submission {sid}")
        test = row.hotkey is None and row.baseline_key is None
        aggregation = (
            session.get(models.BenchmarkAggregation, row.aggregation_id)
            if row.aggregation_id
            else None
        )
        admission = (
            session.get(models.SubmissionAdmissionCheck, row.admission_check_id)
            if row.admission_check_id
            else None
        )
        live_detail: dict[str, object] | None = None
        if not test and row.state == "accepted":
            from db.admission import evaluate

            try:
                points = store.scoring.inputs_for_admission(preview=False, session=session)
                current = next(
                    (p for p in evaluate(session, points) if p.submission_id == sid), None
                )
                live_detail = (
                    current.admission
                    if current
                    else {
                        "outcome": "pending",
                        "reason_code": "missing-current-evidence",
                        "message": "current compatible scoring evidence is unavailable",
                    }
                )
            except ValueError as exc:
                live_detail = {
                    "outcome": "pending",
                    "reason_code": "incompatible-evidence",
                    "message": str(exc),
                }
            if live_detail and live_detail.get("reason_code") == "awaiting-predecessor":
                live_detail = {
                    **live_detail,
                    "message": "awaiting current baseline evidence; "
                    "refresh baseline verification and compatible aggregations",
                }
        duplicates = (
            list(
                session.scalars(
                    select(models.Submission.id)
                    .where(
                        models.Submission.id < sid,
                        models.Submission.source_sha256 == row.source_sha256,
                        models.Submission.state == "accepted",
                        models.Submission.hotkey.is_not(None)
                        | models.Submission.baseline_key.is_not(None),
                    )
                    .order_by(models.Submission.id)
                )
            )
            if row.source_sha256
            else []
        )
        snapshot = (
            session.scalar(
                select(models.ScoreSnapshot)
                .where(
                    models.ScoreSnapshot.submission_id == sid,
                    models.ScoreSnapshot.aggregation_id == row.aggregation_id,
                    models.ScoreSnapshot.admission_check_id == row.admission_check_id,
                )
                .order_by(models.ScoreSnapshot.weight_set_id.desc())
                .limit(1)
            )
            if not test
            else None
        )
        weight_set = session.get(models.WeightSet, snapshot.weight_set_id) if snapshot else None
        return {
            "identical_source_submissions": duplicates,
            "metrics": {
                "total_s": row.compression_seconds,
                "lz77_s": row.parse_seconds,
                "byte_weighted_compression_pct": 100 * row.bytes / row.raw_bytes
                if row.bytes is not None and row.raw_bytes
                else None,
            },
            "score": {
                "allocated": snapshot.combined_weight,
                "payable": snapshot.payable_weight,
                "frontier": snapshot.on_frontier,
                "burn_reason": snapshot.burn_reason,
                "weight_set_id": snapshot.weight_set_id,
                "dry_run": weight_set.dry_run,
                "chain_accepted": weight_set.accepted,
            }
            if snapshot and weight_set
            else None,
            "id": row.id,
            "kind": "test" if test else "baseline" if row.baseline_key else "miner",
            "hotkey": row.hotkey,
            "baseline_key": row.baseline_key,
            "state": row.state,
            "worker": row.worker_id,
            "submitted_at": row.submitted_at,
            "claimed_at": row.claimed_at,
            "finished_at": row.finished_at,
            "preverification": {"passed_at": row.static_verified_at},
            "lean_verification": {"passed_at": row.lean_verified_at},
            "benchmark": {"measured_source_sha256": row.measured_source_sha256},
            "aggregation": {
                "id": row.aggregation_id,
                "statistics": aggregation.statistics if aggregation else None,
            },
            "admission": {
                "id": row.admission_check_id,
                "details": live_detail,
                "recorded_details": admission.details if admission else None,
                "excluded_test": test,
            },
            "exit_code": row.exit_code,
            "report": row.report,
            "note": "Milestones are stored successes, not live stage progress. "
            "Null means not recorded. "
            "Historical verification stamps do not guarantee current scoring eligibility.",
        }


def summary(payload: StatusPayload) -> str:
    terminal = payload["state"] in {"accepted", "rejected", "error"}
    missing = "not recorded" if terminal else "pending"
    state = "gate passed" if payload["state"] == "accepted" else payload["state"]
    lines = [f"Submission {payload['id']} ({payload['kind']}): {state}"]
    for label, done in (
        ("Preverification", payload["preverification"]["passed_at"]),
        ("Lean verification", payload["lean_verification"]["passed_at"]),
        ("Benchmark", payload["benchmark"]["measured_source_sha256"]),
        ("Aggregation", payload["aggregation"]["id"]),
    ):
        lines.append(f"  {label}: {'passed' if done else missing}")
    admission = payload["admission"]
    detail = admission["details"] or {}
    if admission["excluded_test"]:
        result = "excluded (test submission)"
    elif detail:
        outcome = detail["outcome"]
        if outcome in {"pending", "invalid_evidence"}:
            result = "pending — " + str(detail.get("message", detail.get("reason_code", outcome)))
        else:
            result = "admitted" if outcome in {"passed", "not_required"} else "not admitted"
            result += f" ({outcome})"
    else:
        result = "no decision recorded" if terminal else "pending"
    lines.append(f"  Speed admission: {result}")
    duplicates = payload["identical_source_submissions"]
    if duplicates:
        lines.append("  Identical source: submission " + ", ".join(map(str, duplicates)))
    stats = cast("AdmissionComparison | None", detail.get("statistics"))
    if stats:
        lines.append(
            f"  Speed gain: {stats['gain_pct']:+.3f}%; 95% lower bound: {stats['lower_pct']:+.3f}%"
        )
    metrics = payload["metrics"]
    values: list[str] = []
    for key, label, suffix in (
        ("total_s", "total", "s"),
        ("lz77_s", "LZ77", "s"),
        ("byte_weighted_compression_pct", "compression (byte-weighted)", "%"),
    ):
        value = cast("float | None", metrics[key])
        if value is not None:
            values.append(f"{label} {value:.3f}{suffix}")
    if values:
        lines.append("  Measurements: " + ", ".join(values))
    score = payload["score"]
    if score:
        mode = (
            "dry-run"
            if score["dry_run"]
            else "chain accepted"
            if score["chain_accepted"]
            else "not sent/accepted"
        )
        lines.append(
            f"  Last recorded score: {score['allocated']:.6f}; "
            f"payable {score['payable']:.6f} ({mode}, weight set {score['weight_set_id']})"
        )
        lines.append(
            f"  Pareto: {'yes' if score['frontier'] else 'no'}"
            + (f"; burn: {score['burn_reason']}" if score["burn_reason"] else "")
        )
    else:
        lines.append(
            "  Score: excluded (test submission)"
            if admission["excluded_test"]
            else "  Score: not eligible while admission is pending"
            if detail.get("outcome") in {"pending", "invalid_evidence"}
            else "  Score: not recorded for this evidence"
        )
    if payload["state"] in {"rejected", "error"}:
        report = payload.get("report") or ""
        reason = next(
            (
                line.strip()
                for line in reversed(report.splitlines())
                if "REJECTED" in line or "ERROR" in line
            ),
            None,
        )
        lines.append(
            "  Result: " + (reason[:240] if reason else "failed; see --verbose for the report")
        )
    return "\n".join(lines)


@dataclasses.dataclass
class Args:
    command: str = ""
    directory: Path = Path()
    name: str | None = None
    id: int = 0
    watch: bool = False
    verbose: bool = False


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    commands = ap.add_subparsers(dest="command", required=True)
    for kind in ("test", "baseline"):
        cmd = commands.add_parser(kind)
        cmd.add_argument("directory", type=Path)
        if kind == "baseline":
            cmd.add_argument("name", nargs="?")
    cmd = commands.add_parser("status")
    cmd.add_argument("id", type=int)
    cmd.add_argument("--watch", action="store_true")
    cmd.add_argument("--verbose", action="store_true", help="full stored JSON and gate report")
    args = ap.parse_args(argv, namespace=Args())
    store = db.connect()
    try:
        if args.command != "status":
            sid = enqueue(
                store,
                args.directory,
                load().files,
                (args.name or args.directory.resolve().name)
                if args.command == "baseline"
                else None,
            )
            print(f"Queued {args.command} submission {sid}.")
            print(f"Track: just submission-status {sid} --watch")
            return 0
        previous: str | None = None
        while True:
            payload = status(store, args.id)
            rendered = (
                json.dumps(payload, default=str, indent=2) if args.verbose else summary(payload)
            )
            if rendered != previous:
                print(rendered, flush=True)
                previous = rendered
            if not args.watch:
                return 0
            time.sleep(2)
    except (ValueError, OSError) as exc:
        print(str(exc), file=sys.stderr)
        return 2
    except KeyboardInterrupt:
        return 0
    finally:
        store.close()


if __name__ == "__main__":
    raise SystemExit(main())
