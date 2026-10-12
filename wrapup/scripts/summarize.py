#!/usr/bin/env python3
"""Summarise `arena bench` JSONL files the way the competition scores.

Per corpus and method: total bytes, mean per-file compressed % (the score's
ratio axis), mean per-file median-time ratio against a reference method (the
score's time axis), the change against the reference, and the worst file.

    summarize.py [--ref incumbent] FILE.jsonl...
"""

from __future__ import annotations

import argparse
import json
from collections import defaultdict
from pathlib import Path


def load(path: Path) -> tuple[dict, list[dict]]:
    lines = [json.loads(line) for line in path.read_text().splitlines() if line.strip()]
    return lines[0], [r for r in lines[1:] if r.get("kind") == "file"]


def summarize(meta: dict, rows: list[dict], ref: str) -> list[dict]:
    by = defaultdict(dict)
    for r in rows:
        by[r["method"]][r["file"]] = r
    base = by.get(ref, {})
    out = []
    for method, files in by.items():
        ok = [r for r in files.values() if r["bytes"] is not None and r["verified"] and r["raw"] > 0]
        errors = [f"{r['file']}: {r['error']}" for r in files.values() if r.get("error")]
        pct = [100.0 * r["bytes"] / r["raw"] for r in ok]
        tr, gains = [], []
        worst = None
        for r in ok:
            b = base.get(r["file"])
            if not b or not b.get("bytes"):
                continue
            g = 100.0 * (b["bytes"] - r["bytes"]) / b["bytes"]
            gains.append(g)
            if worst is None or g < worst[1]:
                worst = (r["file"], g)
            if r.get("median_total_s") and b.get("median_total_s"):
                tr.append(r["median_total_s"] / b["median_total_s"])
        timed = [r for r in ok if r.get("median_total_s")]
        mbps = (sum(r["raw"] for r in timed) / sum(r["median_total_s"] for r in timed) / 1e6) if timed else None
        out.append(
            {
                "mbps": mbps,
                "raw": sum(r["raw"] for r in ok),
                "corpus": meta.get("label"),
                "mode": meta.get("mode"),
                "method": method,
                "files": len(ok),
                "bytes": sum(r["bytes"] for r in ok),
                "mean_pct": sum(pct) / len(pct) if pct else None,
                "file_gain": sum(gains) / len(gains) if gains else None,
                "time_ratio": sum(tr) / len(tr) if tr else None,
                "worst": worst,
                "errors": errors,
            }
        )
    return out


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--ref", default="incumbent")
    ap.add_argument("--json", action="store_true", help="print JSON instead of a table")
    ap.add_argument("files", nargs="+", type=Path)
    a = ap.parse_args()
    table = []
    for f in a.files:
        meta, rows = load(f)
        table.extend(summarize(meta, rows, a.ref))
    if a.json:
        print(json.dumps(table, indent=1))
        return
    table.sort(key=lambda r: (r["corpus"] or "", r["mode"] or "", r["mean_pct"] or 1e9))
    head = f"{'corpus':6} {'mode':22} {'method':26} {'bytes':>11} {'mean%':>7} {'gain%':>7} {'t/ref':>6} {'MB/s':>7}  worst file"
    print(head)
    for r in table:
        def fmt(v, spec):
            return format(v, spec) if v is not None else "-"
        worst = f"{r['worst'][0]} {r['worst'][1]:+.1f}" if r["worst"] else ""
        err = f"  ERRORS {len(r['errors'])}: {r['errors'][0][:60]}" if r["errors"] else ""
        print(
            f"{r['corpus'] or '':6} {(r['mode'] or '')[:22]:22} {r['method'][:26]:26} {r['bytes']:>11,} "
            f"{fmt(r['mean_pct'], '7.3f')} {fmt(r['file_gain'], '+7.2f')} {fmt(r['time_ratio'], '6.2f')} {fmt(r['mbps'], '7.1f')}  {worst}{err}"
        )


if __name__ == "__main__":
    main()
