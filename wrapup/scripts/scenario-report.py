#!/usr/bin/env python3
"""One table per scenario from `run-scenarios.sh` output.

Per method: hierarchical geometric-mean size against a reference (95% CI), the same
for time, throughput in MB/s of input (total input / total median time), total
bytes, and whether it is on the scenario's Pareto frontier (time, size). External
command-line tools (`<tag>-ext.jsonl`) are compared on size only: their times
include process start-up.

    scenario-report.py RESULTS_DIR [--json OUT] [--md OUT]
"""

from __future__ import annotations

import argparse
import json
import math
import sys
from collections import defaultdict
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
import rank  # noqa: E402

SCENARIOS = [
    ("s1-web", "S1 static web precompression (whole files, gzip framing)", "zlib-6"),
    ("s2-large-stream", "S2 large files, streamed in 1 MiB chunks (gzip framing)", "zlib-6"),
    ("s2-large-whole", "S2 large files, whole buffer (gzip framing)", "libdeflate-6"),
    ("s3-bgzf", "S3 BGZF genomics, 64 KiB blocks", "zlib-6"),
    ("s4-png", "S4 PNG, IDAT recompressed with the image's filters", "zlib-9"),
    ("s5-archive", "S5 archive members, one stream per file", "zlib-6"),
    ("s6-logs", "S6 logs, streamed with a sync flush every 64 KiB", "zlib-6"),
    ("s7-msg-w15", "S7 messages, sync flush per message, 32 KiB window", "zlib-6"),
    ("s7-msg-w12", "S7 messages, sync flush per message, 4 KiB window", "zlib-6"),
]


def totals(paths: list[Path]) -> dict[str, dict]:
    t: dict[str, dict] = defaultdict(lambda: {"raw": 0, "bytes": 0, "time": 0.0, "ok": True})
    for p in paths:
        for line in p.read_text().splitlines()[1:]:
            r = json.loads(line)
            if r.get("kind") != "file":
                continue
            d = t[r["method"]]
            if not r.get("verified") or r.get("bytes") is None:
                d["ok"] = False
                continue
            d["raw"] += r["raw"]
            d["bytes"] += r["bytes"]
            d["time"] += r.get("median_total_s") or 0.0
    return t


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("results", type=Path)
    ap.add_argument("--json", type=Path)
    ap.add_argument("--md", type=Path)
    ap.add_argument("--boot", type=int, default=1000)
    a = ap.parse_args()
    report, md = {}, []
    for tag, title, ref in SCENARIOS:
        main_file = a.results / f"{tag}.jsonl"
        if not main_file.exists():
            continue
        ext_tag = tag.rsplit("-", 1)[0] if tag.startswith("s2-") else tag
        ext_file = a.results / f"{ext_tag}-ext.jsonl"
        rows, _data, _cats = rank.score([main_file], ref, {}, a.boot)
        tot = totals([main_file])
        ext_rows = []
        if ext_file.exists():
            # Sizes only: score the external tools against the same reference by merging runs.
            merged, _d, _c = rank.score([main_file, ext_file], ref, {}, 0, merge_runs=True)
            ext_names = {json.loads(x)["method"] for x in ext_file.read_text().splitlines()[1:]}
            ext_rows = [r for r in merged if r["method"] in ext_names]
            for m, v in totals([ext_file]).items():
                tot[m] = v
        best = float("inf")
        timed = sorted((r for r in rows if r["time"] is not None), key=lambda r: (r["time"], r["size"]))
        for r in timed:
            r["pareto"] = r["size"] < best
            best = min(best, r["size"])
        out = []
        for r in rows + ext_rows:
            t = tot.get(r["method"], {})
            mbps = t["raw"] / t["time"] / 1e6 if t.get("time") else None
            out.append({**r, "mbps": mbps, "bytes": t.get("bytes"), "raw": t.get("raw"),
                        "external": r in ext_rows, "all_verified": t.get("ok", False)})
        out.sort(key=lambda r: r["size"])
        report[tag] = {"title": title, "ref": ref, "methods": out}

        print(f"\n## {title}   (size and time relative to {ref})")
        print(f"{'method':24} {'size':>7} {'95% CI':>17} {'time':>7} {'MB/s':>7} {'bytes':>13} P ok")
        md.append(f"\n### {title}\n\nRelative to {ref}. P = on the frontier.\n")
        md.append("| method | size | time | MB/s | P |\n|---|---|---|---|---|")
        for r in out:
            ci = f"[{r['size_ci'][0]:.4f},{r['size_ci'][1]:.4f}]" if r.get("size_ci") else ""
            tm = "ext" if r["external"] else (f"{r['time']:.2f}" if r["time"] is not None else "-")
            mb = f"{r['mbps']:.1f}" if r["mbps"] and not r["external"] else "-"
            print(f"{r['method'][:24]:24} {r['size']:7.4f} {ci:>17} {tm:>7} {mb:>7} {r['bytes'] or 0:>13,} "
                  f"{'*' if r.get('pareto') else ' '} {'y' if r['all_verified'] else 'NO'}")
            md.append(f"| {r['method']} | {r['size']:.4f} | {tm} | {mb} | {'*' if r.get('pareto') else ''} |")
    if a.json:
        a.json.write_text(json.dumps(report, indent=1))
    if a.md:
        a.md.write_text("\n".join(md) + "\n")


if __name__ == "__main__":
    main()
