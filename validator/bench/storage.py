"""Import complete single-process evidence atomically; never aggregate or score."""

from __future__ import annotations

import argparse
import math
import re
import sys
from datetime import datetime, timezone
from pathlib import Path
from typing import cast
from uuid import UUID

import sqlalchemy as sa
from sqlalchemy.dialects.postgresql import insert
from sqlalchemy.exc import SQLAlchemyError

from db.engine import create_db_engine
from db.models import BenchmarkCompressionResult, BenchmarkRun, BenchmarkSpeedSample

from .corpora import Corpus
from .errors import Malformed
from .hashing import canonical as canonical
from .hashing import sha256 as sha256
from .results import INCUMBENT, Run, parse


def preflight(engine: sa.Engine) -> None:
    """Check connectivity and required schema before doing expensive measurements."""
    with engine.connect() as conn:
        conn.execute(sa.select(BenchmarkRun).limit(0))
        conn.execute(sa.select(BenchmarkCompressionResult).limit(0))
        conn.execute(sa.select(BenchmarkSpeedSample).limit(0))


def read_artifact(path: Path) -> tuple[Run, list[dict[str, object]]]:
    text = path.read_text()
    # No original corpus directory or parser source is required to import evidence.
    run = parse(text, Corpus("import", Path("."), False, {}))
    raw = list(run.raw_records)
    if any(r.get("kind") != "file" for r in raw[1:]):
        raise Malformed("expected one meta record followed only by file records")
    if len(run.candidates()) != 1:
        raise Malformed(
            "import requires one candidate per file; merged multi-candidate reports "
            "have lost reference measurements: rerun with --store-db"
        )
    if not run.files or len({f.file for f in run.files}) != len(run.files):
        raise Malformed("the run needs nonempty, uniquely named corpus files")
    if INCUMBENT not in run.meta.methods:
        raise Malformed("missing incumbent metadata")
    for name in (INCUMBENT, *run.candidates()):
        source = run.meta.methods[name].source_sha256
        if source is None or re.fullmatch("[0-9a-f]{64}", source) is None:
            raise Malformed(f"{name}: missing or invalid source_sha256")
    if run.meta.warmup_rounds < 0 or run.meta.measured_rounds < 1:
        raise Malformed("invalid repetition counts")
    if not math.isfinite(run.meta.started_at_unix):
        raise Malformed("invalid start time")
    for file in run.files:
        if not 0 <= file.raw_bytes < 2**63 or re.fullmatch("[0-9a-f]{64}", file.sha256) is None:
            raise Malformed(f"{file.file}: invalid size or content hash")
        if set(file.methods) != set(run.meta.methods):
            raise Malformed(f"{file.file}: methods do not match metadata")
        for method in file.methods.values():
            if method.external != run.meta.methods[method.name].external:
                raise Malformed(f"{file.file}: {method.name}: inconsistent external flag")
            if method.output_bytes is not None and not 0 <= method.output_bytes < 2**63:
                raise Malformed(f"{file.file}: {method.name}: invalid output_bytes")
            for field, value in (
                ("output_sha256", method.output_sha256),
                ("tokens_sha256", method.tokens_sha256),
            ):
                if value is not None and re.fullmatch("[0-9a-f]{64}", value) is None:
                    raise Malformed(f"{file.file}: {method.name}: invalid {field}")
            if method.ok and (method.output_bytes is None or method.output_sha256 is None):
                raise Malformed(
                    f"{file.file}: {method.name}: successful result needs output size/hash"
                )
            for rep in method.reps:
                if (
                    rep.phase not in {"warmup", "measured"}
                    or not 0 <= rep.order_index < 2**63
                    or not math.isfinite(rep.time_s)
                    or rep.time_s < 0
                ):
                    raise Malformed(f"{file.file}: invalid timing sample")
            if method.ok:
                for phase, expected in (
                    ("warmup", run.meta.warmup_rounds),
                    ("measured", run.meta.measured_rounds),
                ):
                    if sum(rep.phase == phase for rep in method.reps) != expected:
                        raise Malformed(f"{file.file}: {method.name}: incomplete {phase} samples")
    # Also rejects non-finite numbers in fields outside the timing projection.
    canonical(raw)
    return run, raw


def import_file(
    engine: sa.Engine,
    path: Path,
    *,
    submission_id: int | None = None,
    gate_attempt_token: str | None = None,
) -> int:
    run, raw = read_artifact(path)
    identity = raw[0].get("run_uuid")
    if identity is None:
        key = "sha256:" + sha256(raw)
    elif isinstance(identity, str):
        key = "uuid:" + str(UUID(identity))
    else:
        raise Malformed("run_uuid must be a UUID string")
    candidate = run.candidates()[0]
    manifest = sorted((f.file, f.sha256, f.raw_bytes) for f in run.files)
    started = datetime.fromtimestamp(run.meta.started_at_unix, timezone.utc)
    # Failed methods remain inspectable, but this run must not be selected as successful.
    failed = any(not f.methods[name].ok for f in run.files for name in (INCUMBENT, candidate))
    with engine.begin() as conn:
        run_id = conn.execute(
            insert(BenchmarkRun)
            .values(
                run_key=key,
                submission_id=submission_id,
                gate_attempt_token=gate_attempt_token,
                source_sha256=run.meta.methods[candidate].source_sha256,
                candidate_method=candidate,
                corpus=run.meta.corpus,
                corpus_sha256=sha256(manifest),
                status="failed" if failed else "complete",
                started_at=started,
                raw_data=raw,
            )
            .on_conflict_do_nothing(index_elements=["run_key"])
            .returning(BenchmarkRun.id)
        ).scalar_one_or_none()
        if run_id is None:
            existing = conn.execute(
                sa.select(BenchmarkRun.id, BenchmarkRun.raw_data).where(BenchmarkRun.run_key == key)
            ).one()
            if cast(object, existing.raw_data) != raw:
                raise Malformed("run UUID already exists with different data")
            return cast(int, existing.id)
        insert_results(conn, run_id, run)
        return run_id


def insert_results(conn: sa.Connection, run_id: int, run: Run) -> None:
    """Project validated evidence; caller owns the transaction including the run row."""
    results: list[dict[str, object]] = []
    samples: list[dict[str, object]] = []
    for index, file in enumerate(run.files):
        for method in file.methods.values():
            # The engine compares token hashes, not compressed sizes across rounds.
            # Its default true flag alone does not establish that a comparison occurred.
            deterministic = None
            if not method.external and method.tokens_sha256 is not None:
                if not method.deterministic:
                    deterministic = False
                elif not method.errors and len(method.reps) > 1:
                    deterministic = True
            results.append(
                {
                    "run_id": run_id,
                    "file_index": index,
                    "method": method.name,
                    "file_path": file.file,
                    "file_sha256": file.sha256,
                    "raw_bytes": file.raw_bytes,
                    "output_bytes": method.output_bytes,
                    "output_sha256": method.output_sha256,
                    "tokens_sha256": method.tokens_sha256,
                    "tokens_deterministic": deterministic,
                    "succeeded": method.ok,
                }
            )
            samples.extend(
                {
                    "run_id": run_id,
                    "file_index": index,
                    "method": method.name,
                    "repetition": repetition,
                    "phase": rep.phase,
                    "order_index": rep.order_index,
                    "time_s": rep.time_s,
                    "encode_s": rep.encode_s,
                    "total_s": rep.total_s,
                }
                for repetition, rep in enumerate(method.reps)
            )
    for offset in range(0, len(results), 1000):
        conn.execute(sa.insert(BenchmarkCompressionResult), results[offset : offset + 1000])
    for offset in range(0, len(samples), 1000):
        conn.execute(sa.insert(BenchmarkSpeedSample), samples[offset : offset + 1000])


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("files", type=Path, nargs="+", help="single-candidate raw JSONL artifacts")
    args = parser.parse_args(argv)
    paths = cast(list[Path], args.files)
    engine = create_db_engine()
    try:
        preflight(engine)
        for path in paths:
            print(f"{path}: database run {import_file(engine, path)}")
    except SQLAlchemyError:
        print(
            "Database import failed; check DB configuration and run just db-migrate. "
            "Local artifacts can be retried with just bench-import.",
            file=sys.stderr,
        )
        return 2
    except (Malformed, ValueError, OSError, OverflowError) as exc:
        print(f"Import failed: {exc}", file=sys.stderr)
        return 2
    finally:
        engine.dispose()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
