#!/usr/bin/env python3
"""Turn a benchmark run (JSONL, from data/benchmark-runs/) into a markdown report and box plots.

    .venv/bin/python -m bench.analyze [run-file-or-name]

With no argument, uses the most recent run in `data/benchmark-runs/` (its filenames sort
chronologically). A bare filename (not a path) is resolved inside that directory; a path is
used as-is.

This script only reads and interprets -- it never re-runs the benchmark, so report iteration is
fast and independent of how slow collection was. It recomputes every statistic from the raw
per-rep timings in the run file, so a run only needs to be collected once no matter how the
analysis evolves.

The headline numbers are the gate's numbers: compressed bytes pooled over files against the
incumbent, and the sum of per-file minimum parse times against the incumbent's, with the
verdict the gate would give. Per-format tables, the Pareto front and the stability section are
context computed from the same file.

Output goes to `data/benchmark-reports/<run-stem>/`: REPORT.md plus, when matplotlib is installed,
the box plots drawn by plot.py for compression ratio and speed, by format and method.

Schema (v3; `bench/report.py` writes it and `validator/measure/src/record.rs` defines it):
first line is `{"kind": "meta", ...}`; every following line is `{"kind": "file", corpus, file,
format, raw_bytes, sha256, methods: {name: {output_bytes, output_sha256, tokens_sha256,
deterministic, external, errors, encode_s, reps: [{phase, order_index, time_s}, ...]}}}`
where `time_s` is the parse alone. Fields are additive-only -- this script reads known
keys and ignores anything else.
"""

from __future__ import annotations

import glob
import json
import os
import statistics
import sys
from collections import defaultdict
from typing import NotRequired, TypedDict, cast

# validator/bench/analyze.py -> validator/bench -> validator -> the repository root.
REPO_ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
RUNS_DIR = os.path.join(REPO_ROOT, "data", "benchmark-runs")
REPORTS_DIR = os.path.join(REPO_ROOT, "data", "benchmark-reports")

# What every ratio is taken against: validator/incumbent/parse.rs, measured as a
# method in every run.
REFERENCE_METHOD = "incumbent"
# Timing spread (max/min over measured reps) above which a file is called noisy.
NOISY_SPREAD = 1.25

METHOD_ORDER = [
    "incumbent",
    "no-lz77",
    "template",
    "hc-d4",
    "hc-sparse",
    "hash-chains",
    "hc-d64",
    "lazy",
    "mo-lazy",
    "btree",
    "optimal",
    "libdeflate-12",
]


class Rep(TypedDict):
    phase: str
    order_index: int
    time_s: float


class MethodRec(TypedDict):
    output_bytes: int
    # None for a reference bar, which produces compressed bytes rather than tokens.
    tokens_sha256: str | None
    deterministic: bool
    external: bool
    encode_s: float
    reps: list[Rep]
    output_sha256: NotRequired[str | None]
    errors: NotRequired[list[str]]


class FileRec(TypedDict):
    kind: str
    corpus: str
    file: str
    format: str
    raw_bytes: int
    sha256: str
    methods: dict[str, MethodRec]


class Row(TypedDict):
    # One (file, method, rep) -- the tidy form everything below groups from.
    corpus: str
    file: str
    format: str
    raw_bytes: int
    method: str
    output_bytes: int
    phase: str
    time_s: float


Meta = dict[str, object]
Key = tuple[str, str, str]


def method_order(methods_present: set[str]) -> list[str]:
    known = [m for m in METHOD_ORDER if m in methods_present]
    unknown = sorted(methods_present - set(known))
    return known + unknown


def resolve_run_path(arg: str | None) -> str:
    if arg is None:
        candidates = sorted(glob.glob(os.path.join(RUNS_DIR, "*.jsonl")))
        if not candidates:
            print(f"no run files in {RUNS_DIR}", file=sys.stderr)
            sys.exit(1)
        return candidates[-1]
    if os.sep in arg or os.path.exists(arg):
        return arg
    return os.path.join(RUNS_DIR, arg)


def load_run(path: str) -> tuple[Meta, list[FileRec]]:
    meta: Meta = {}
    files: list[FileRec] = []
    with open(path) as fh:
        for line in fh:
            line = line.strip()
            if not line:
                continue
            raw = cast(object, json.loads(line))  # json gives Any; everything below narrows
            rec = cast(dict[str, object], raw)
            if rec.get("kind") == "meta":
                meta = rec
            elif rec.get("kind") == "file":
                files.append(cast(FileRec, raw))
    return meta, files


def flatten(files: list[FileRec]) -> list[Row]:
    """One row per (file, method, rep) -- the tidy form everything below groups from."""
    rows: list[Row] = []
    for rec in files:
        for method, mrec in rec["methods"].items():
            for rep in mrec["reps"]:
                rows.append(
                    Row(
                        corpus=rec["corpus"],
                        file=rec["file"],
                        format=rec["format"],
                        raw_bytes=rec["raw_bytes"],
                        method=method,
                        output_bytes=mrec["output_bytes"],
                        phase=rep["phase"],
                        time_s=rep["time_s"],
                    )
                )
    return rows


def mean_std(xs: list[float]) -> tuple[float, float]:
    if not xs:
        return (float("nan"), float("nan"))
    if len(xs) == 1:
        return (xs[0], 0.0)
    return (statistics.mean(xs), statistics.stdev(xs))


def per_file_ratio(rows: list[Row]) -> dict[Key, float]:
    """{(format, method, file): ratio} -- deterministic, one value per file+method."""
    out: dict[Key, float] = {}
    for r in rows:
        out[(r["format"], r["method"], r["file"])] = r["output_bytes"] / r["raw_bytes"]
    return out


def per_file_min_time(rows: list[Row]) -> dict[Key, float]:
    """{(format, method, file): minimum measured time_s} -- the gate's statistic."""
    by_key: dict[Key, list[float]] = defaultdict(list)
    for r in rows:
        if r["phase"] != "measured":
            continue
        by_key[(r["format"], r["method"], r["file"])].append(r["time_s"])
    return {k: min(v) for k, v in by_key.items()}


def per_file_spread(rows: list[Row]) -> dict[Key, float]:
    """{(format, method, file): max/min measured time_s} -- how noisy that measurement was."""
    by_key: dict[Key, list[float]] = defaultdict(list)
    for r in rows:
        if r["phase"] == "measured":
            by_key[(r["format"], r["method"], r["file"])].append(r["time_s"])
    return {k: (max(v) / min(v) if min(v) > 0 else 1.0) for k, v in by_key.items()}


def per_file_speed_ratio(min_time: dict[Key, float]) -> dict[Key, float]:
    """{(format, method, file): time(method) / time(reference)} on the same file."""
    ref_time: dict[tuple[str, str], float] = {}
    for (fmt, method, f), t in min_time.items():
        if method == REFERENCE_METHOD:
            ref_time[(fmt, f)] = t
    out: dict[Key, float] = {}
    for (fmt, method, f), t in min_time.items():
        r = ref_time.get((fmt, f))
        if r is not None and r > 0:
            out[(fmt, method, f)] = t / r
    return out


def group_by_format_method(per_file: dict[Key, float]) -> dict[tuple[str, str], list[float]]:
    """{(format, method): [values across files]}."""
    out: dict[tuple[str, str], list[float]] = defaultdict(list)
    for (fmt, method, _f), v in per_file.items():
        out[(fmt, method)].append(v)
    return out


def pooled_bytes(files: list[FileRec]) -> dict[str, int]:
    """{method: compressed bytes summed over files} -- the score's arithmetic."""
    out: dict[str, int] = defaultdict(int)
    for f in files:
        for m, r in f["methods"].items():
            out[m] += r["output_bytes"]
    return dict(out)


def pooled_min_time(min_time: dict[Key, float]) -> dict[str, float]:
    """{method: sum over files of the minimum parse time} -- the floor's arithmetic."""
    out: dict[str, float] = defaultdict(float)
    for (_fmt, method, _f), t in min_time.items():
        out[method] += t
    return dict(out)


def verdict(method: str, ratio: float, speed: float, floor: float, external: set[str]) -> str:
    """What the gate would print for this method against the incumbent."""
    if method in external:
        return "reference"
    if method == REFERENCE_METHOD:
        return "incumbent"
    if speed > floor:
        return "over the floor"
    return "accepted" if ratio < 1 else "no improvement"


def pareto_front(
    bytes_by: dict[str, int], time_by: dict[str, float], exclude: set[str]
) -> list[str]:
    """Methods no other method beats on both bytes and time, fewest bytes first."""
    names = [m for m in bytes_by if m not in exclude and m in time_by]

    def dominated(m: str) -> bool:
        return any(
            bytes_by[o] <= bytes_by[m]
            and time_by[o] <= time_by[m]
            and (bytes_by[o] < bytes_by[m] or time_by[o] < time_by[m])
            for o in names
            if o != m
        )

    return sorted((m for m in names if not dominated(m)), key=lambda m: bytes_by[m])


def stability(files: list[FileRec], spread: dict[Key, float]) -> dict[str, tuple[float, int, bool]]:
    """{method: (worst spread, noisy files, deterministic on every file)}."""
    out: dict[str, tuple[float, int, bool]] = {}
    for f in files:
        for m, r in f["methods"].items():
            worst, noisy, det = out.get(m, (1.0, 0, True))
            s = spread.get((f["format"], m, f["file"]), 1.0)
            out[m] = (max(worst, s), noisy + int(s > NOISY_SPREAD), det and r["deterministic"])
    return out


def md_table(rows: list[list[str]], header: list[str]) -> str:
    lines = ["| " + " | ".join(header) + " |", "|" + "---|" * len(header)]
    lines += ["| " + " | ".join(r) + " |" for r in rows]
    return "\n".join(lines)


def md_by_format(
    by_format_method: dict[tuple[str, str], list[float]],
    formats: list[str],
    methods: list[str],
    spec: str,
    suffix: str = "",
) -> str:
    rows: list[list[str]] = []
    for fmt in formats:
        cells = [fmt, str(len(by_format_method.get((fmt, methods[0]), [])))]
        for m in methods:
            vals = by_format_method.get((fmt, m))
            cells.append(f"{statistics.mean(vals):{spec}}{suffix}" if vals else "--")
        rows.append(cells)
    return md_table(rows, ["format", "files"] + methods)


def report(meta: Meta, files: list[FileRec], run_path: str) -> str:
    rows = flatten(files)
    formats = sorted({r["format"] for r in rows})
    methods = method_order({r["method"] for r in rows})
    external = {m for f in files for m, r in f["methods"].items() if r.get("external")}
    floor_raw = meta.get("speed_floor")
    floor = float(floor_raw) if isinstance(floor_raw, (int, float)) else 8.0

    ratio = per_file_ratio(rows)
    min_time = per_file_min_time(rows)
    speed_ratio = per_file_speed_ratio(min_time)
    ratio_by_fm = group_by_format_method(ratio)
    speed_by_fm = group_by_format_method(speed_ratio)
    pb, pt = pooled_bytes(files), pooled_min_time(min_time)
    stab = stability(files, per_file_spread(rows))
    raw = sum(f["raw_bytes"] for f in files)

    score_rows: list[list[str]] = []
    for m in sorted(methods, key=lambda m: pb[m]):
        r, s = pb[m] / pb[REFERENCE_METHOD], pt[m] / pt[REFERENCE_METHOD]
        cells = [m, f"{pb[m]:,}", f"{r:.4f}x", f"{s:.2f}x", verdict(m, r, s, floor, external)]
        score_rows.append(cells)
    stab_rows = [
        [m, f"{stab[m][0]:.2f}", str(stab[m][1]), "yes" if stab[m][2] else "**NO**"]
        for m in methods
    ]
    run_stem = os.path.splitext(os.path.basename(run_path))[0]
    hashed = meta.get("methods")
    n_hashed = len(cast(dict[str, object], hashed)) if isinstance(hashed, dict) else 0
    corpus = str(meta.get("corpus", "unknown"))

    lines = [
        f"# {run_stem} -- benchmark report",
        "",
        f"Source: `{os.path.relpath(run_path, REPO_ROOT)}`",
        "",
        "Run metadata:",
        f"- corpus: {corpus}; {n_hashed} method(s), each with its source hashed in the run file",
        f"- host: {meta.get('os')}/{meta.get('arch')}, CPU: {meta.get('cpu_model', 'unknown')} "
        f"({meta.get('cpu_governor', 'unknown')} governor)",
        f"- toolchain: {meta.get('rustc_version', 'unknown')}",
        f"- warmup rounds: {meta.get('warmup_rounds')}, "
        f"measured rounds: {meta.get('measured_rounds')}",
        "",
        f"## Score: pooled bytes and pooled minimum parse time against `{REFERENCE_METHOD}` "
        f"({len(files)} files, {raw:,} raw bytes)",
        "",
        f"The gate's arithmetic. `accepted` means fewer bytes and at most {floor:.0f}x the "
        "incumbent's time. Only the parse is timed; the encoder is the same for everyone.",
        "",
        md_table(score_rows, ["method", "bytes", "vs incumbent", "time", "gate would say"]),
        "",
        "## Pareto front of provable methods (fewest bytes for their time)",
        "",
        ", ".join(f"`{m}`" for m in pareto_front(pb, pt, external)),
        "",
        "## Compression ratio (compressed / raw), by format -- mean over files, equal weight",
        "",
        md_by_format(ratio_by_fm, formats, methods, ".3f"),
        "",
        f"## Speed vs. `{REFERENCE_METHOD}`, by format -- min-of-reps parse time ratio, mean",
        "",
        md_by_format(speed_by_fm, formats, methods, ".2f", "x"),
        "",
        "## Stability: timing spread (max/min over measured reps) and token-stream determinism",
        "",
        f"A file is noisy when its spread exceeds {NOISY_SPREAD}. Bytes never vary between reps; "
        "a non-deterministic parser is a bug.",
        "",
        md_table(stab_rows, ["method", "worst spread", "noisy files", "deterministic"]),
        "",
        "## Plots",
        "",
        "- `ratio-by-format.png`",
        "- `speed-ratio-by-format.png`",
        "",
    ]
    return "\n".join(lines)


def main() -> None:
    arg = sys.argv[1] if len(sys.argv) > 1 else None
    run_path = resolve_run_path(arg)
    meta, files = load_run(run_path)
    if not files:
        print(f"no file records in {run_path}", file=sys.stderr)
        sys.exit(1)
    rows = flatten(files)
    formats = sorted({r["format"] for r in rows})
    methods = method_order({r["method"] for r in rows})
    run_stem = os.path.splitext(os.path.basename(run_path))[0]
    out_dir = os.path.join(REPORTS_DIR, run_stem)
    os.makedirs(out_dir, exist_ok=True)

    text = report(meta, files, run_path)
    report_path = os.path.join(out_dir, "REPORT.md")
    with open(report_path, "w") as fh:
        fh.write(text)
    print("wrote", report_path)

    try:
        from bench.plot import boxplot_by_format

        boxplot_by_format(
            group_by_format_method(per_file_ratio(rows)),
            formats,
            methods,
            f"{run_stem} -- compressed size, fraction of raw, by format",
            "compressed / raw (lower is better)",
            os.path.join(out_dir, "ratio-by-format.png"),
        )
        boxplot_by_format(
            group_by_format_method(per_file_speed_ratio(per_file_min_time(rows))),
            formats,
            methods,
            f"{run_stem} -- min parse time vs. {REFERENCE_METHOD}, by format",
            f"time(method) / time({REFERENCE_METHOD}) (lower is faster)",
            os.path.join(out_dir, "speed-ratio-by-format.png"),
        )
        print("plots in", out_dir)
    except ImportError:
        print("matplotlib not installed; report written without plots", file=sys.stderr)


if __name__ == "__main__":
    main()
