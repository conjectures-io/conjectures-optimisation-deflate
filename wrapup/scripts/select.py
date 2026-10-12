#!/usr/bin/env python3
"""The pre-registered robustness screen and selection (docs/wrapup/PREREGISTRATION.md).

    select.py --operator OPERATOR.json --pool pool.csv --map c4/map.json \
              --c4 C4.jsonl... --setA SETA.jsonl... [--boot 2000] [--json OUT]

Methods named `p<id>` are submissions (their group comes from pool.csv); `incumbent`,
`mo-lazy`, `optimal-iter` are baselines. References (zlib, libdeflate ...) are context
only: never screened, never selected.
"""

from __future__ import annotations

import argparse
import csv
import json
import math
import sys
from collections import defaultdict
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
import rank  # noqa: E402

BASELINES = {"incumbent", "mo-lazy", "optimal-iter"}
LOSS_PCT, LOSS_MIN_BYTES, FLAG_PCT = 20.0, 32, 10.0
SLOPE_MAX, TIME_FACTOR, TIME_MIN_BYTES = 1.15, 5.0, 64 * 1024


def is_parser(m: str) -> bool:
    return m in BASELINES or (m.startswith("p") and m[1:].isdigit())


def jsonl_rows(paths: list[Path]) -> list[dict]:
    out = []
    for run, p in enumerate(paths):
        lines = [json.loads(x) for x in p.read_text().splitlines() if x.strip()]
        label = lines[0].get("label")
        out += [dict(r, label=label, run=run) for r in lines[1:] if r.get("kind") == "file"]
    return out


RULES = "revised"  # set from --rules


def expands(raw: int, out: int, inc: int | None = None) -> bool:
    over = out > raw * 1.001 + 5 * math.ceil(max(raw, 1) / 65536) + 5
    if RULES == "revised" and inc is not None:
        # Deviation 4: the shared encoder cannot store a block with any match in
        # it, so on random data every parser expands; only worse-than-incumbent counts.
        return over and out > inc * 1.001
    return over


def loss(sub: int, inc: int, raw: int | None = None) -> tuple[bool, bool]:
    """(fails, flagged) for one file."""
    d = sub - inc
    big = True
    if RULES == "revised" and raw:
        # Deviation 3: on near-degenerate inputs (1 MB -> 1 KB) a few KB is +300%;
        # a loss must also cost more than 1% of the input.
        big = d > 0.01 * raw
    return (big and d > LOSS_MIN_BYTES and 100.0 * d / inc > LOSS_PCT,
            big and d > LOSS_MIN_BYTES and 100.0 * d / inc > FLAG_PCT)


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--operator", type=Path, required=True)
    ap.add_argument("--pool", type=Path, required=True)
    ap.add_argument("--map", type=Path, required=True)
    ap.add_argument("--c4", type=Path, nargs="+", required=True)
    ap.add_argument("--setA", type=Path, nargs="+", required=True)
    ap.add_argument("--boot", type=int, default=2000)
    ap.add_argument("--json", type=Path)
    ap.add_argument("--extra-fails", type=Path,
                    help="TSV method<TAB>reason: screen failures found by a supplementary run "
                         "(e.g. withheld submissions that have no rerun data)")
    ap.add_argument("--index", type=Path, help="PROD sources index.tsv (id, hotkey, submitted_at, sha)")
    ap.add_argument("--rules", choices=("strict", "revised"), default="revised",
                    help="strict = as pre-registered (+ deviations 1-2); revised = + deviations 3-4")
    a = ap.parse_args()
    global RULES
    RULES = a.rules

    op = json.loads(a.operator.read_text())
    op_by_id = {s["id"]: s for s in op["submissions"]}
    pool = list(csv.DictReader(a.pool.open()))
    group_of, members_of, submitted = {}, {}, {}
    for g in pool:
        for mid in g["member_ids"].split():
            group_of[mid] = g["rep"]
        members_of[g["rep"]] = g["member_ids"].split()
        submitted[g["rep"]] = g["submitted_at"]

    def sub_id(m: str) -> str | None:
        return m[1:] if m.startswith("p") and m[1:].isdigit() else None

    mapping = {k: tuple(v) for k, v in json.loads(a.map.read_text()).items()}
    scored, _data, _cats = rank.score(a.c4, "incumbent", mapping, a.boot)
    c4 = {r["method"]: r for r in scored}
    c4_rows, sa_rows = jsonl_rows(a.c4), jsonl_rows(a.setA)

    fails: dict[str, list[str]] = defaultdict(list)
    flags: dict[str, list[str]] = defaultdict(list)
    parsers = sorted(m for m in c4 if is_parser(m))

    # 1. Size and expansion on c1, c2, c3 (rerun data) ...
    for m in parsers:
        sid = sub_id(m)
        s = op_by_id.get(sid) if sid else None
        if s is None:
            continue
        for c in ("c1", "c2", "c3"):
            for name, raw, inc, sub, _t in (s.get("corpora") or {}).get(c, {}).get("files") or []:
                f, fl = loss(sub, inc, raw)
                if f:
                    fails[m].append(f"{c}/{name} {100 * (sub - inc) / inc:+.1f}%")
                elif fl:
                    flags[m].append(f"{c}/{name} {100 * (sub - inc) / inc:+.1f}%")
                if expands(raw, sub, inc):
                    fails[m].append(f"{c}/{name} expands")
    # ... and on C4 and set A (this run), plus errors and determinism.
    for rows in (c4_rows, sa_rows):
        base = {(r["run"], r["label"], r["file"]): r for r in rows if r["method"] == "incumbent"}
        for r in rows:
            m = r["method"]
            if m not in parsers:
                continue
            where = f"{r['label']}/{r['file']}"
            if r.get("error") or not r.get("verified"):
                fails[m].append(f"{where}: {r.get('error') or 'unverified'}")
                continue
            b = base.get((r["run"], r["label"], r["file"]))
            if b and b.get("bytes"):
                f, fl = loss(r["bytes"], b["bytes"], r["raw"])
                if f:
                    fails[m].append(f"{where} {100 * (r['bytes'] - b['bytes']) / b['bytes']:+.1f}%")
                elif fl:
                    flags[m].append(f"{where} {100 * (r['bytes'] - b['bytes']) / b['bytes']:+.1f}%")
            if expands(r["raw"], r["bytes"], b["bytes"] if b else None):
                fails[m].append(f"{where} expands")

    # 3. Time: scaling slope and per-file blow-ups on set A.
    sa = defaultdict(dict)
    for r in sa_rows:
        sa[(r["run"], r["file"])][r["method"]] = r
    slopes = {}
    for m in parsers:
        pts = [(math.log(d[m]["raw"]), math.log(d[m]["median_total_s"]))
               for (_run, f), d in sa.items() if f.startswith("scale-") and m in d and d[m].get("median_total_s")]
        if len(pts) >= 3:
            mx = sum(x for x, _ in pts) / len(pts)
            my = sum(y for _, y in pts) / len(pts)
            slope = sum((x - mx) * (y - my) for x, y in pts) / sum((x - mx) ** 2 for x, _ in pts)
            slopes[m] = slope
            if slope > SLOPE_MAX:
                fails[m].append(f"time slope {slope:.2f} over scale-01m..64m")
        c4t = c4[m]["time"]
        for (_run, f), d in sa.items():
            r, b = d.get(m), d.get("incumbent")
            if not r or not b or r["raw"] < TIME_MIN_BYTES or not r.get("median_total_s") or not b.get("median_total_s"):
                continue
            tr = r["median_total_s"] / b["median_total_s"]
            if c4t and tr > TIME_FACTOR * c4t:
                fails[m].append(f"setA/{f} time ratio {tr:.1f} vs C4 {c4t:.2f}")

    if a.extra_fails:
        for line in a.extra_fails.read_text().splitlines():
            if line.strip() and not line.startswith("#"):
                m, reason = line.split("\t", 1)
                if m in parsers:
                    fails[m].append(reason)
    passing = [m for m in parsers if not fails[m]]

    # Frontier on C4 among passing parsers.
    pts = sorted((c4[m]["time"], c4[m]["size"], m) for m in passing if c4[m]["time"] and c4[m]["size"])
    frontier, best = [], float("inf")
    for t, s, m in pts:
        if s < best:
            frontier.append(m)
            best = s

    index_when = {}
    if a.index:
        for line in a.index.read_text().splitlines():
            i, _hot, t, _sha = line.split("\t")
            index_when[i] = t.replace(" ", "T")

    def when(m: str) -> str:
        sid = sub_id(m)
        rep = group_of.get(sid, sid) if sid else None
        return submitted.get(rep) or index_when.get(sid or "", "0") if rep else "0"

    chosen: list[str] = []
    if frontier:
        lt = [math.log(c4[m]["time"]) for m in frontier]
        picks = [0, len(frontier) - 1]
        for k in (1, 2, 3):
            target = lt[0] + k / 4 * (lt[-1] - lt[0])
            order = sorted(range(len(frontier)), key=lambda i: abs(lt[i] - target))
            nxt = next((i for i in order if i not in picks), None)
            if nxt is not None:  # a frontier of five or fewer points is selected whole
                picks.append(nxt)
        for i in sorted(set(picks)):
            m = frontier[i]
            # Tie with a neighbour: overlapping size CI and time within 10% -> earlier, then unflagged.
            cands = [m]
            for j in (i - 1, i + 1):
                if 0 <= j < len(frontier):
                    n = frontier[j]
                    a_ci, b_ci = c4[m]["size_ci"], c4[n]["size_ci"]
                    if a_ci and b_ci and a_ci[0] <= b_ci[1] and b_ci[0] <= a_ci[1] \
                            and abs(c4[n]["time"] / c4[m]["time"] - 1) <= 0.10:
                        cands.append(n)
            pick = min(cands, key=lambda x: (when(x), bool(flags[x])))
            if pick not in chosen:
                chosen.append(pick)

    def gain_c12(m: str) -> float | None:
        sid = sub_id(m)
        s = op_by_id.get(sid) if sid else None
        if not s:
            return None
        logs = []
        for c in ("c1", "c2"):
            fs = (s.get("corpora") or {}).get(c, {}).get("files") or []
            if fs:
                logs.append(sum(math.log(sub / inc) for _n, _r, inc, sub, _t in fs) / len(fs))
        return 1 - math.exp(sum(logs) / len(logs)) if logs else None

    def overfit(m: str) -> float | None:
        g12 = gain_c12(m)
        if g12 is None or g12 <= 0 or c4[m]["size"] is None:
            return None
        return 1 - (1 - c4[m]["size"]) / g12

    print(f"rules: {RULES}")
    print(f"screened {len(parsers)} parsers: {len(passing)} pass, {len(parsers) - len(passing)} fail")
    print(f"C4 frontier among passing ({len(frontier)}): " + " ".join(frontier))
    print()
    print(f"{'method':14} {'submitted':10} {'size':>7} {'95% CI':>17} {'time':>6} {'overfit':>7} {'flags':>5}  members / first failure")
    for m in sorted(parsers, key=lambda x: c4[x]["time"] or 0):
        r = c4[m]
        mark = "SELECT" if m in chosen else ("front " if m in frontier else ("fail  " if fails[m] else "      "))
        of = overfit(m)
        sid = sub_id(m)
        mem = " ".join(members_of.get(group_of.get(sid, ""), [])) if sid else "baseline"
        info = fails[m][0] if fails[m] else f"members {mem}"
        ci = f"[{r['size_ci'][0]:.4f},{r['size_ci'][1]:.4f}]" if r["size_ci"] else ""
        print(f"{mark} {m:8} {when(m)[:10]:10} {r['size']:7.4f} {ci:>17} {r['time']:6.2f} "
              f"{(f'{of:+.2f}' if of is not None else '-'):>7} {len(flags[m]):5}  {info[:70]}")
    if a.json:
        a.json.write_text(json.dumps({
            "selected": chosen, "frontier": frontier, "passing": passing,
            "fails": dict(fails), "flags": dict(flags), "slopes": slopes,
            "c4": {m: c4[m] for m in parsers}, "overfit": {m: overfit(m) for m in parsers},
        }, indent=1))


if __name__ == "__main__":
    main()
