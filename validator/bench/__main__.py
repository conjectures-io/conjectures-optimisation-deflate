"""Benchmark parsers from the command line: the table, and the JSON behind it.

    python -m bench miner/template
    python -m bench                 # this repo's template and every example
    python -m bench miner/template --corpus silesia-subset --out results.json
    python -m bench --corpora       # what can be measured, and which is default
    python -m bench --clean         # drop every retained run workspace

Each argument is a submission directory or a `parse.rs`; its name is the method
name. With none, this repository's own `miner/template` and `miner/examples/*` are
measured. Every run also measures the incumbent, so the ratios are the ones the
gate would compute.

This is the tool a miner runs while tuning. It is not the gate: it proves
nothing, and unlike `verifier/verify.py` it falls back to running unsandboxed,
loudly, on a machine without bubblewrap.
"""

from __future__ import annotations

import argparse
import dataclasses
import json
import sys
import time
from dataclasses import dataclass
from pathlib import Path
from typing import cast

from loguru import logger

from . import corpora, report
from .driver import Config, Keep, Measurement, check, run, sweep
from .errors import BenchError, Misconfigured
from .results import SCHEMA_VERSION
from .verdict import SPEED_FLOOR

VALIDATOR = Path(__file__).resolve().parent.parent
REPO = VALIDATOR.parent


@dataclass(frozen=True)
class Options:
    submissions: list[str]
    list_corpora: bool
    clean: bool
    corpus: str
    out: Path | None
    runs_dir: Path | None
    reps: int | None
    warmup: int | None
    speed_floor: float
    keep: bool
    bars: bool
    quiet: bool


def parse_args(argv: list[str] | None = None) -> Options:
    ap = argparse.ArgumentParser(prog="python -m bench", description=(__doc__ or "").split("\n")[0])
    ap.add_argument(
        "submissions",
        nargs="*",
        help="submission directories or parse.rs files; default: this repo's own",
    )
    ap.add_argument("--corpora", action="store_true", help="list the corpora and stop")
    ap.add_argument("--clean", action="store_true", help="remove retained workspaces and stop")
    ap.add_argument("--corpus", default="", help="a name from corpora.toml, or a directory")
    ap.add_argument("--out", type=Path, help="write the JSON summary here")
    ap.add_argument("--runs-dir", type=Path, help="write the raw JSONL run here, named by time")
    ap.add_argument("--reps", type=int, help="timed reps per file per method")
    ap.add_argument("--warmup", type=int, help="discarded reps before them")
    ap.add_argument("--speed-floor", type=float, default=SPEED_FLOOR)
    ap.add_argument("--keep", action="store_true", help="keep the run workspace")
    ap.add_argument("--no-bars", action="store_true", help="skip miniz_oxide and libdeflate")
    ap.add_argument("--quiet", action="store_true", help="no table on stdout")
    a = ap.parse_args(argv)
    return Options(
        submissions=cast("list[str]", a.submissions),
        list_corpora=cast(bool, a.corpora),
        clean=cast(bool, a.clean),
        corpus=cast(str, a.corpus),
        out=cast("Path | None", a.out),
        runs_dir=cast("Path | None", a.runs_dir),
        reps=cast("int | None", a.reps),
        warmup=cast("int | None", a.warmup),
        speed_floor=cast(float, a.speed_floor),
        keep=cast(bool, a.keep),
        bars=not cast(bool, a.no_bars),
        quiet=cast(bool, a.quiet),
    )


def default_submissions() -> list[str]:
    # With no arguments, what this repository has to compare.
    return [
        str(REPO / "miner/template"),
        *sorted(str(p) for p in (REPO / "miner/examples").iterdir() if p.is_dir()),
    ]


def candidates(submissions: list[str]) -> dict[str, Path]:
    out: dict[str, Path] = {}
    for s in submissions or default_submissions():
        p = Path(s).resolve()
        source = p if p.is_file() else p / "parse.rs"
        if not source.is_file():
            raise Misconfigured(f"{s}: no parse.rs")
        name = source.parent.name if source.name == "parse.rs" else source.stem
        if name in out:
            raise Misconfigured(f"two submissions are both called {name}")
        out[name] = source
    return out


def configure(o: Options) -> Config:
    config = Config.from_env(VALIDATOR)
    config = dataclasses.replace(
        config,
        reps=max(o.reps, 1) if o.reps is not None else config.reps,
        warmup=max(o.warmup, 0) if o.warmup is not None else config.warmup,
        keep=Keep.ALWAYS if o.keep else config.keep,
        bars=config.bars and o.bars,
    )
    try:
        check(config)
    except Misconfigured as e:
        if not config.enabled:
            raise
        # A miner's laptop may have no bubblewrap. Say so once, clearly, and go on.
        logger.warning(f"[bench] no sandbox: {e}")
        logger.warning("[bench] running UNSANDBOXED — never do this as a validator")
        config = dataclasses.replace(config, enabled=False)
        check(config)
    return config


def corpus(name: str) -> corpora.Corpus:
    if not name:
        return corpora.default(VALIDATOR)
    known = corpora.load(VALIDATOR)
    if any(c.name == name for c in known):
        return known.by_name(name)
    return corpora.adhoc(Path(name)).require()


def write_runs_file(m: Measurement, runs_dir: Path, floor: float) -> Path:
    # One permanent, independently-readable artifact per run, never overwritten.
    runs_dir.mkdir(parents=True, exist_ok=True)
    stamp = time.strftime("%Y%m%dT%H%M%SZ", time.gmtime())
    path = runs_dir / f"{stamp}_v{SCHEMA_VERSION}.jsonl"
    with path.open("w") as f:
        for rec in report.records(m, floor):
            f.write(json.dumps(rec) + "\n")
    return path


def main(argv: list[str] | None = None) -> int:
    o = parse_args(argv)
    if o.list_corpora:
        known = corpora.load(VALIDATOR)
        for c in known:
            mark = " (default)" if c.name == known.default_name else ""
            where = "public" if c.public else "held out"
            missing = "" if c.path.is_dir() else "   MISSING"
            print(f"{c.name:<18} {where:<9} {c.path}{mark}{missing}")
        return 0
    if o.clean:
        config = Config.from_env(VALIDATOR)
        sweep(config)
        print(f"swept {config.workspace}")
        return 0
    gone = corpora.load(VALIDATOR).missing()
    if gone:
        logger.warning(
            f"[bench] not fetched yet: {', '.join(gone)} -- "
            "`just corpus-pull` and/or `just corpus-download`"
        )
    try:
        m = run(
            configure(o), candidates(o.submissions), corpus(o.corpus), speed_floor=o.speed_floor
        )
    except BenchError as e:
        detail = cast(str, getattr(e, "detail", ""))
        print(f"{e}\n{detail}".rstrip(), file=sys.stderr)
        return 2

    if not o.quiet:
        print(report.table(m, o.speed_floor))
    if o.out is not None:
        o.out.write_text(json.dumps(report.summary(m, o.speed_floor), indent=2) + "\n")
        logger.info(f"[bench] wrote {o.out}")
    if o.runs_dir is not None:
        print(write_runs_file(m, o.runs_dir, o.speed_floor))
    if m.kept:
        logger.info(f"[bench] kept {m.workspace}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
