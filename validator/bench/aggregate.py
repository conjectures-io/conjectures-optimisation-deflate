"""Aggregate database evidence, optionally publishing it to a verified submission."""

from __future__ import annotations

import argparse
import dataclasses
import json
from typing import cast

from sqlalchemy.orm import Session

from db.aggregation import (
    CorpusIdentity,
    aggregate,
    compression_statistics,
    publish,
    reduce_runs,
    select_runs,
    timing_statistics,
)
from db.engine import create_db_engine
from db.models import Submission


@dataclasses.dataclass
class Options(argparse.Namespace):
    source: str | None
    submission_id: int | None
    corpus: list[CorpusIdentity]
    run_id: list[int] | None
    preview: bool
    publish: bool
    speed_floor: float


def corpus_identity(value: str) -> CorpusIdentity:
    try:
        name, digest = value.rsplit(":", 1)
        return CorpusIdentity(name, digest)
    except ValueError as exc:
        raise argparse.ArgumentTypeError("expected CORPUS:SHA256") from exc


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    who = ap.add_mutually_exclusive_group(required=True)
    who.add_argument("--source")
    who.add_argument("--submission-id", type=int)
    ap.add_argument("--corpus", type=corpus_identity, action="append", required=True)
    ap.add_argument("--run-id", type=int, action="append")
    ap.add_argument("--preview", action="store_true")
    ap.add_argument("--publish", action="store_true")
    ap.add_argument("--speed-floor", type=float, default=8.0)
    args = cast(Options, ap.parse_args(argv))
    if args.publish and (args.preview or args.submission_id is None):
        ap.error("--publish requires --submission-id and cannot be used with --preview")
    engine = create_db_engine()
    try:
        with Session(engine) as session, session.begin():
            source = args.source
            if args.submission_id is not None:
                sub = session.get(Submission, args.submission_id)
                if sub is None or sub.source_sha256 is None:
                    raise ValueError("submission has no verified source identity")
                source = sub.source_sha256
            assert source is not None
            rows = select_runs(session, source, args.corpus, args.run_id)
            if args.preview:
                output = dataclasses.asdict(reduce_runs(rows)) | {
                    "statistics": {
                        **timing_statistics(rows),
                        "compression": compression_statistics(rows),
                    }
                }
            else:
                result = aggregate(session, rows)
                if args.publish:
                    assert args.submission_id is not None
                    publish(session, args.submission_id, result.id, speed_floor=args.speed_floor)
                output = {
                    "aggregation_id": result.id,
                    "context": result.context,
                    "statistics": result.statistics,
                }
        print(json.dumps(output, indent=2, allow_nan=False))
        return 0
    except ValueError as exc:
        ap.exit(2, f"Aggregation failed: {exc}\n")
    finally:
        engine.dispose()


if __name__ == "__main__":
    raise SystemExit(main())
