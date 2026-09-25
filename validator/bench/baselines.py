"""Incrementally verify, benchmark and publish operator baseline revisions."""

from __future__ import annotations

import argparse
import hashlib
import shutil
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import cast

from sqlalchemy import Engine, select, text, update
from sqlalchemy.orm import Session, sessionmaker

from bench import corpora
from bench.artifacts import write_import_files
from bench.driver import Config, check, provenance, run
from bench.errors import BenchError
from bench.hashing import sha256
from bench.storage import import_file, preflight
from db.aggregation import (
    CorpusIdentity,
    aggregate,
    compatibility,
    publish,
    select_runs,
    validate_evidence,
)
from db.engine import create_db_engine
from db.models import BenchmarkAggregation, Submission, SubmissionFile
from service.settings import load
from service.storage import write_submission
from verifier.identity import required_fingerprint

ROOT = Path(__file__).resolve().parents[1]


@dataclass
class Options(argparse.Namespace):
    corpus: list[str]
    only: list[str] | None
    overwrite: bool


def discover() -> dict[str, Path]:
    paths = [ROOT.parent / "miner/template", *sorted((ROOT.parent / "miner/examples").iterdir())]
    found: dict[str, Path] = {}
    for path in paths:
        if not (path / "parse.rs").is_file() or not (path / "Parse.lean").is_file():
            continue
        if path.name in found:
            raise ValueError(f"ambiguous baseline name: {path.name}")
        found[path.name] = path
    return found


def toolchain_path() -> str:
    """PATH as the gate resolves its tools: verifier/config.sh puts the repo's own elan,
    and so `lake`, ahead of the operator's PATH. Setup installs Lean under
    validator/.work, so checking the bare PATH refused to seed on a validator whose gate
    runs fine."""
    result = subprocess.run(
        ["bash", "-c", 'source "$1" >/dev/null 2>&1 && printf %s "$PATH"', "config"]
        + [str(ROOT / "verifier/config.sh")],
        capture_output=True,
        text=True,
        check=True,
    )
    return result.stdout


def identity(corpus: corpora.Corpus) -> CorpusIdentity:
    corpus.require()
    files = sorted(p for p in corpus.path.iterdir() if p.is_file())
    manifest = [
        (p.name, hashlib.sha256(p.read_bytes()).hexdigest(), p.stat().st_size) for p in files
    ]
    return CorpusIdentity(corpus.name, sha256(manifest))


def seed_one(
    engine: Engine,
    name: str,
    directory: Path,
    selected: list[corpora.Corpus],
    config: Config,
    overwrite: bool = False,
) -> None:
    settings = load()
    source, proof = (directory / "parse.rs").read_bytes(), (directory / "Parse.lean").read_bytes()
    digest = hashlib.sha256(source + proof).hexdigest()
    # Session lock spans expensive work, but no SQL transaction spans tool invocations.
    with engine.connect() as lock:
        key = int(hashlib.sha256(("baseline:" + name).encode()).hexdigest()[:15], 16)
        lock.execute(text("SELECT pg_advisory_lock(:key)"), {"key": key})
        lock.commit()
        try:
            with Session(engine, expire_on_commit=False) as session, session.begin():
                sub = session.scalar(
                    select(Submission).where(
                        Submission.baseline_key == name, Submission.digest == digest
                    )
                )
                if sub is None:
                    sub = Submission(
                        hotkey=None, baseline_key=name, digest=digest, state="verifying"
                    )
                    session.add(sub)
                    session.flush()
                sid = sub.id
                # Keep source bytes with the revision even when all benchmark runs are reused.
                # Missing historical copies are filled in; an existing copy is immutable.
                for filename, content, recorded_hash in (
                    ("parse.rs", source, sub.source_sha256),
                    ("Parse.lean", proof, sub.proof_sha256),
                ):
                    if recorded_hash and recorded_hash != hashlib.sha256(content).hexdigest():
                        raise ValueError(f"baseline {filename} differs from verified source hash")
                    saved = session.get(SubmissionFile, (sid, filename))
                    if saved is None:
                        session.add(
                            SubmissionFile(submission_id=sid, name=filename, content=content)
                        )
                    elif saved.content != content:
                        raise ValueError(
                            f"stored baseline {filename} differs from immutable revision"
                        )
            stored = settings.submission_dir(sid)
            if stored.exists() and all((stored / f).exists() for f in ("parse.rs", "Parse.lean")):
                if (stored / "parse.rs").read_bytes() != source or (
                    stored / "Parse.lean"
                ).read_bytes() != proof:
                    raise ValueError("stored baseline revision differs from immutable digest")
            else:
                write_submission(stored, source, proof)
            if not (
                sub.source_sha256 == hashlib.sha256(source).hexdigest()
                and sub.proof_sha256 == hashlib.sha256(proof).hexdigest()
                and sub.verifier_fingerprint == required_fingerprint()
                and sub.static_verified_at is not None
                and sub.lean_verified_at is not None
            ):
                for stage in ("static", "lean"):
                    subprocess.run(
                        [
                            sys.executable,
                            str(ROOT / "verifier/verify.py"),
                            "--submission-id",
                            str(sid),
                            "--stage",
                            stage,
                        ],
                        check=True,
                    )
            ids: list[int] = []
            for corpus in selected:
                wanted = identity(corpus)
                existing = None
                if not overwrite:
                    with Session(engine) as session:
                        try:
                            row = select_runs(
                                session, hashlib.sha256(source).hexdigest(), [wanted]
                            )[0]
                            evidence = validate_evidence(row)
                            compatibility(evidence)
                            if (
                                evidence.raw_records[0].get("benchmark_provenance")
                                == provenance(config)
                                and evidence.meta.measured_rounds == config.reps
                                and evidence.meta.warmup_rounds == config.warmup
                            ):
                                existing = row.id
                        except ValueError:
                            pass
                if existing is not None:
                    print(f"{name}: reuse {corpus.name} run {existing}", flush=True)
                    ids.append(existing)
                    continue
                print(f"{name}: benchmark {corpus.name}", flush=True)
                measured = run(config, {name: stored / "parse.rs"}, corpus, speed_floor=None)
                paths = write_import_files(
                    measured, ROOT.parent / "data/benchmark-runs/baselines", None
                )
                ids.extend(import_file(engine, path) for path in paths)
            with Session(engine) as session, session.begin():
                rows = select_runs(
                    session,
                    hashlib.sha256(source).hexdigest(),
                    [identity(c) for c in selected],
                    ids,
                )
                result = aggregate(session, rows)
                publish(session, sid, result.id)
                session.execute(
                    update(Submission)
                    .where(Submission.baseline_key == name)
                    .values(baseline_active=False)
                )
                sub = session.get(Submission, sid)
                assert sub is not None
                sub.baseline_active = True
                sub.state = "accepted"
                print(f"{name}: published submission {sid}, aggregation {result.id}", flush=True)
        finally:
            lock.execute(text("SELECT pg_advisory_unlock(:key)"), {"key": key})
            lock.commit()


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument(
        "--corpus",
        action="append",
        help="repeat to select corpora; default: both competition stages",
    )
    ap.add_argument("--only", action="append", help="baseline name; repeat to select several")
    ap.add_argument(
        "--overwrite", action="store_true", help="fresh runs; preserve historical evidence"
    )
    args = cast(Options, ap.parse_args(argv))
    args.corpus = args.corpus or ["corpus-stage1", "corpus-stage2"]
    available = discover()
    from scoring.admission import BASELINE_ORDER

    unknown = set(available) - set(BASELINE_ORDER)
    if unknown:
        ap.error(f"update the versioned admission manifest for new baselines: {sorted(unknown)}")
    names = args.only or list(available)
    if len(set(names)) != len(names) or any(n not in available for n in names):
        ap.error("unknown or duplicate baseline name")
    names = [name for name in BASELINE_ORDER if name in names]
    registry = corpora.load(ROOT)
    selected = [registry.by_name(name) for name in args.corpus]
    if len(set(args.corpus)) != len(args.corpus):
        ap.error("duplicate corpus selection")
    for corpus in selected:
        identity(corpus)
    config = Config.from_env(ROOT)
    check(config)
    required_fingerprint()  # Reads the installed trusted translator binaries.
    search = toolchain_path()
    for tool in ("lake", "rustc", "cargo"):
        if shutil.which(tool, path=search) is None:
            ap.error(f"required tool is missing: {tool}")
    engine = create_db_engine()
    failures: list[str] = []
    try:
        preflight(engine)
        with Session(engine) as session:
            session.execute(select(Submission.baseline_key).limit(0))
            session.execute(
                select(BenchmarkAggregation.context, BenchmarkAggregation.statistics).limit(0)
            )
        for name in names:
            try:
                seed_one(engine, name, available[name], selected, config, args.overwrite)
            except (ValueError, BenchError, subprocess.CalledProcessError) as exc:
                failures.append(name)
                print(f"{name}: failed: {exc}", file=sys.stderr)
        from db.admission import run as admit
        from db.scoring import ScoringDb

        # Seeding is an explicit ordered replay: unchanged prefixes reuse decisions;
        # overwriting an earlier baseline appends decisions for the changed suffix.
        try:
            decisions = admit(ScoringDb(sessionmaker(engine)), persist=True, replay=True)
            for point in decisions:
                if point.admission and point.admission["outcome"] == "pending":
                    print(f"{point.baseline_key or point.submission_id}: awaiting admission")
                elif point.admission and point.admission["outcome"] == "invalid_evidence":
                    failures.append("admission")
                    print(
                        f"{point.baseline_key or point.submission_id}: "
                        f"admission error: {point.admission.get('error')}",
                        file=sys.stderr,
                    )
        except ValueError as exc:
            failures.append("admission")
            print(f"admission: failed: {exc}", file=sys.stderr)
        # This invokes only the DB report, never the chain weight setter.
        from workers.report import main as report

        report([])
        return 1 if failures else 0
    finally:
        engine.dispose()


if __name__ == "__main__":
    raise SystemExit(main())
