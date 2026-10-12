#!/usr/bin/env python3
"""Rank methods across heterogeneous results (PLAN.md §3.4).

Per method, against a reference method:
  size  = hierarchical geometric mean of bytes / reference bytes
  time  = the same for median total time
The hierarchy is file -> source -> category: a source's files are averaged
first, then a category's sources, then categories count equally, so neither a
big file nor a format with many files dominates. 95% intervals come from a
bootstrap that resamples sources within each category. Also: the worst file,
leave-one-category-out rank stability (Kendall tau), and Pareto membership.

    rank.py [--ref incumbent] [--map MAP.json] [--boot 2000] [--json OUT] FILE.jsonl...

A file's category defaults to its JSONL label (and mode), its source to the first
component of its path; MAP.json ({"<label>/<file>": ["category", "source"]})
overrides either.
"""

from __future__ import annotations

import argparse
import json
import math
import random
from collections import defaultdict
from pathlib import Path


def load(paths: list[Path], mapping: dict) -> tuple[dict, set]:
    """-> {method: {(category, source, label/file): (log size ratio, log time ratio | None)}}"""
    rows: dict[tuple[str, str], dict[str, dict]] = defaultdict(dict)
    meta_mode = {}
    for p in paths:
        lines = [json.loads(x) for x in p.read_text().splitlines() if x.strip()]
        meta = lines[0]
        unit = f"{meta.get('label')}" + ("" if meta.get("mode") in (None, "Whole") else f" [{meta.get('mode')}]")
        meta_mode[unit] = meta.get("mode")
        for r in lines[1:]:
            if r.get("kind") == "file":
                rows[(unit, r["file"])][r["method"]] = r
    return rows, set(meta_mode)


def build(rows: dict, ref: str, mapping: dict):
    data: dict[str, dict] = defaultdict(dict)
    worst: dict[str, tuple[str, float]] = {}
    failures: dict[str, int] = defaultdict(int)
    for (unit, file), by in rows.items():
        base = by.get(ref)
        if not base or not base.get("bytes") or not base.get("verified"):
            continue
        cat, src = mapping.get(f"{unit}/{file}", (unit, file.split("/")[0]))
        for m, r in by.items():
            if not r.get("verified") or not r.get("bytes"):
                failures[m] += 1
                continue
            ls = math.log(r["bytes"] / base["bytes"])
            lt = None
            if r.get("median_total_s") and base.get("median_total_s"):
                lt = math.log(r["median_total_s"] / base["median_total_s"])
            data[m][(cat, src, f"{unit}/{file}")] = (ls, lt)
            loss = 100.0 * (r["bytes"] - base["bytes"]) / base["bytes"]
            if m not in worst or loss > worst[m][1]:
                worst[m] = (f"{unit}/{file}", loss)
    return data, worst, failures


def hier(values: dict, idx: int, sources: dict | None = None) -> float | None:
    """Hierarchical mean of component idx; `sources` optionally gives a resampled
    list of sources per category."""
    by_cat: dict[str, dict[str, list[float]]] = defaultdict(lambda: defaultdict(list))
    for (cat, src, _f), v in values.items():
        if v[idx] is not None:
            by_cat[cat][src].append(v[idx])
    cats = []
    for cat, srcs in by_cat.items():
        chosen = sources[cat] if sources else list(srcs)
        means = [sum(srcs[s]) / len(srcs[s]) for s in chosen if s in srcs]
        if means:
            cats.append(sum(means) / len(means))
    return sum(cats) / len(cats) if cats else None


def kendall(a: list[float], b: list[float]) -> float:
    n, c, d = len(a), 0, 0
    for i in range(n):
        for j in range(i + 1, n):
            s = (a[i] - a[j]) * (b[i] - b[j])
            c += s > 0
            d += s < 0
    return (c - d) / (c + d) if c + d else 1.0


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--ref", default="incumbent")
    ap.add_argument("--map", type=Path)
    ap.add_argument("--boot", type=int, default=2000)
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--json", type=Path)
    ap.add_argument("files", nargs="+", type=Path)
    a = ap.parse_args()
    mapping = {k: tuple(v) for k, v in json.loads(a.map.read_text()).items()} if a.map else {}
    rows, units = load(a.files, mapping)
    data, worst, failures = build(rows, a.ref, mapping)

    # Sources per category, from the reference's coverage.
    cat_sources: dict[str, list[str]] = defaultdict(list)
    for (cat, src, _f) in data.get(a.ref, {}):
        if src not in cat_sources[cat]:
            cat_sources[cat].append(src)

    rng = random.Random(a.seed)
    boots = [{c: [rng.choice(s) for _ in s] for c, s in cat_sources.items()} for _ in range(a.boot)]
    out = []
    for m, vals in data.items():
        size, time = hier(vals, 0), hier(vals, 1)
        bs = sorted(x for x in (hier(vals, 0, b) for b in boots) if x is not None)
        bt = sorted(x for x in (hier(vals, 1, b) for b in boots) if x is not None)

        def ci(xs: list[float]) -> tuple[float, float] | None:
            if not xs:
                return None
            return (math.exp(xs[int(0.025 * (len(xs) - 1))]), math.exp(xs[int(0.975 * (len(xs) - 1))]))

        out.append(
            {
                "method": m,
                "files": len(vals),
                "failures": failures.get(m, 0),
                "size": math.exp(size) if size is not None else None,
                "size_ci": ci(bs),
                "time": math.exp(time) if time is not None else None,
                "time_ci": ci(bt),
                "worst": worst.get(m),
            }
        )

    # Pareto on (time, size); methods without timing are left out of it.
    timed = sorted((r for r in out if r["time"] is not None and r["size"] is not None), key=lambda r: (r["time"], r["size"]))
    best = float("inf")
    for r in timed:
        r["pareto"] = r["size"] < best
        best = min(best, r["size"])

    # Leave one category out: does the size ranking hold?
    cats = sorted(cat_sources)
    full = {r["method"]: r["size"] for r in out if r["size"] is not None}
    names = sorted(full)
    taus = {}
    for c in cats:
        part = {m: hier({k: v for k, v in data[m].items() if k[0] != c}, 0) for m in names}
        common = [m for m in names if part[m] is not None]
        if len(common) > 2:
            taus[c] = kendall([full[m] for m in common], [part[m] for m in common])

    out.sort(key=lambda r: (r["size"] if r["size"] is not None else 9))
    if a.json:
        a.json.write_text(json.dumps({"ref": a.ref, "categories": cats, "loo_kendall": taus, "methods": out}, indent=1))
    print(f"reference {a.ref}; {len(cats)} categories: {', '.join(cats)}")
    print(f"{'method':28} {'size':>7} {'95% CI':>17} {'time':>7} {'95% CI':>17} {'P':1} {'fail':>4}  worst file")
    for r in out:
        def f(v):
            return f"{v:7.4f}" if v is not None else "      -"

        def fci(c):
            return f"[{c[0]:.4f},{c[1]:.4f}]" if c else " " * 17
        w = f"{r['worst'][0][-40:]} {r['worst'][1]:+.1f}%" if r["worst"] else ""
        print(f"{r['method'][:28]:28} {f(r['size'])} {fci(r['size_ci'])} {f(r['time'])} {fci(r['time_ci'])} "
              f"{'*' if r.get('pareto') else ' '} {r['failures']:>4}  {w}")
    if taus:
        print("leave-one-category-out Kendall tau of the size ranking: "
              + ", ".join(f"{c} {t:.3f}" for c, t in taus.items()))


if __name__ == "__main__":
    main()
