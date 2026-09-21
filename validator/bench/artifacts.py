"""Lossless, per-process artifacts usable without a database."""

from __future__ import annotations

import json
from pathlib import Path
from uuid import uuid4

from . import report
from .driver import Measurement


def write_import_files(m: Measurement, directory: Path, floor: float) -> list[Path]:
    directory.mkdir(parents=True, exist_ok=True)
    paths: list[Path] = []
    for run in m.runs:
        run_uuid = str(uuid4())
        single = Measurement(m.corpus, (run,), m.workspace, m.kept)
        records = list(run.raw_records) or report.records(single, floor)
        records[0] = records[0] | {"run_uuid": run_uuid, "corpus_public": m.corpus.public}
        path = directory / f"{run_uuid}.jsonl"
        with path.open("x") as stream:
            for record in records:
                stream.write(json.dumps(record, allow_nan=False) + "\n")
        paths.append(path)
    return paths
