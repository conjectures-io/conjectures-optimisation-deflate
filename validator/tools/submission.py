"""Queue local diagnostic/baseline submissions and inspect persisted milestones."""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import shutil
import sys
import time
from pathlib import Path

from sqlalchemy import select, text

import db
from db import models
from service.settings import MAX_FILE_BYTES, load
from service.storage import write_submission


def enqueue(store, directory: Path, files: Path, baseline: str | None = None) -> int:
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


def status(store, sid: int) -> dict:
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
                "details": admission.details if admission else None,
                "excluded_test": test,
            },
            "exit_code": row.exit_code,
            "report": row.report,
            "note": "Milestones are stored successes, not live stage progress. "
            "Null means not recorded. "
            "Historical verification stamps do not guarantee current scoring eligibility.",
        }


def summary(payload: dict) -> str:
    terminal = payload["state"] in {"accepted", "rejected", "error"}
    missing = "not recorded" if terminal else "pending"
    lines = [f"Submission {payload['id']} ({payload['kind']}): {payload['state']}"]
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
        result = "admitted" if outcome in {"passed", "not_required"} else "not admitted"
        result += f" ({outcome})"
    else:
        result = "no decision recorded" if terminal else "pending"
    lines.append(f"  Speed admission: {result}")
    stats = detail.get("statistics")
    if stats:
        lines.append(
            f"  Speed gain: {stats['gain_pct']:+.3f}%; 95% lower bound: {stats['lower_pct']:+.3f}%"
        )
    metrics = payload.get("metrics", {})
    values = []
    for key, label, suffix in (
        ("total_s", "total", "s"),
        ("lz77_s", "LZ77", "s"),
        ("byte_weighted_compression_pct", "compression (byte-weighted)", "%"),
    ):
        if metrics.get(key) is not None:
            values.append(f"{label} {metrics[key]:.3f}{suffix}")
    if values:
        lines.append("  Measurements: " + ", ".join(values))
    score = payload.get("score")
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


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    commands = ap.add_subparsers(dest="command", required=True)
    for kind in ("test", "baseline"):
        cmd = commands.add_parser(kind)
        cmd.add_argument("directory", type=Path)
        if kind == "baseline":
            cmd.add_argument("name")
    cmd = commands.add_parser("status")
    cmd.add_argument("id", type=int)
    cmd.add_argument("--watch", action="store_true")
    cmd.add_argument("--verbose", action="store_true", help="full stored JSON and gate report")
    args = ap.parse_args(argv)
    store = db.connect()
    try:
        if args.command != "status":
            sid = enqueue(
                store,
                args.directory,
                load().files,
                args.name if args.command == "baseline" else None,
            )
            print(f"Queued {args.command} submission {sid}.")
            print(f"Track: just submission-status {sid} --watch")
            return 0
        previous = None
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
