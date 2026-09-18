#!/usr/bin/env python3
"""Check that two runs of the same code agree: same bytes and tokens, time in bounds.

    .venv/bin/python -m bench.compare RUN_A RUN_B

Exit 0 when the runs agree, 1 with one line per difference otherwise. This is the repeatability
check: a submission benchmarked twice must produce identical token streams and byte counts on
every file, and its pooled minimum parse time must not have moved more than TIME_TOLERANCE.
"""

from __future__ import annotations

import sys

from .analyze import (
    FileRec,
    Meta,
    flatten,
    load_run,
    per_file_min_time,
    pooled_min_time,
)

# Time may move this much between two runs on the same machine before it is a finding.
TIME_TOLERANCE = 0.15


def compare(a: tuple[Meta, list[FileRec]], b: tuple[Meta, list[FileRec]]) -> list[str]:
    """Every difference that matters between two runs."""
    problems: list[str] = []
    fa = {(f["corpus"], f["file"]): f for f in a[1]}
    fb = {(f["corpus"], f["file"]): f for f in b[1]}
    for key in sorted(set(fa) | set(fb)):
        label = f"{key[0]}/{key[1]}"
        if key not in fa or key not in fb:
            problems.append(f"{label}: only in one run")
            continue
        if fa[key]["sha256"] != fb[key]["sha256"]:
            problems.append(f"{label}: corpus file differs")
        for m in sorted(set(fa[key]["methods"]) | set(fb[key]["methods"])):
            ra, rb = fa[key]["methods"].get(m), fb[key]["methods"].get(m)
            if ra is None or rb is None:
                problems.append(f"{label} {m}: only in one run")
            elif ra["tokens_sha256"] != rb["tokens_sha256"]:
                problems.append(f"{label} {m}: different tokens")
            elif ra["output_bytes"] != rb["output_bytes"]:
                problems.append(f"{label} {m}: different bytes")
            elif ra.get("output_sha256") != rb.get("output_sha256"):
                problems.append(f"{label} {m}: same byte count, different bytes")
    ta = pooled_min_time(per_file_min_time(flatten(a[1])))
    tb = pooled_min_time(per_file_min_time(flatten(b[1])))
    for m in sorted(set(ta) & set(tb)):
        if ta[m] > 0 and abs(tb[m] - ta[m]) / ta[m] > TIME_TOLERANCE:
            problems.append(
                f"{m}: pooled min parse time {ta[m]:.4f}s -> {tb[m]:.4f}s ({tb[m] / ta[m]:.2f}x)"
            )
    for k in ("methods", "cpu_model", "rustc_version"):
        if a[0].get(k) != b[0].get(k):
            problems.append(f"meta {k} differs between the runs")
    return problems


def main() -> None:
    if len(sys.argv) != 3:
        print(__doc__, file=sys.stderr)
        sys.exit(2)
    problems = compare(load_run(sys.argv[1]), load_run(sys.argv[2]))
    for p in problems:
        print(p)
    if problems:
        sys.exit(f"{len(problems)} difference(s) between {sys.argv[1]} and {sys.argv[2]}")
    print(
        f"agree: same bytes and tokens on every file, pooled parse time within {TIME_TOLERANCE:.0%}"
    )


if __name__ == "__main__":
    main()
