#!/usr/bin/env python3
"""The candidate pool from the s66 rerun data (`reruns-operator/<env>.json`).

Groups submissions that behave identically: the same compressed size on every
file of every rerun corpus. Each group is represented by its earliest member
(attribution goes to whoever got there first). Writes one CSV row per group and
prints a summary, including a preliminary frontier over c1+c2+c3 of the groups
with no pathological file: the general frontier the final selection refines on
C4 and the robustness set.

    pool.py OPERATOR_JSON [--out pool.csv] [--max-loss 20]
"""

from __future__ import annotations

import argparse
import csv
import json
from collections import defaultdict
from pathlib import Path

CORPORA = ("c1", "c2", "c3")


def signature(sub: dict) -> tuple | None:
    sig = []
    for c in CORPORA:
        files = (sub.get("corpora") or {}).get(c, {}).get("files")
        if not files:
            return None
        sig.append(tuple((f[0], f[3]) for f in sorted(files)))
    return tuple(sig)


def worst_loss(sub: dict, corpus: str) -> tuple[str, float] | None:
    files = (sub.get("corpora") or {}).get(corpus, {}).get("files") or []
    worst = None
    for name, raw, inc, mine, _t in files:
        if inc:
            g = 100.0 * (inc - mine) / inc
            if worst is None or g < worst[1]:
                worst = (name, g)
    return worst


def frontier(points: list[tuple[float, float, str]]) -> list[str]:
    """Lower is better on both axes. Points as (time, ratio, id)."""
    out, best = [], float("inf")
    for t, r, i in sorted(points):
        if r < best:
            out.append(i)
            best = r
    return out


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("operator_json", type=Path)
    ap.add_argument("--out", type=Path, default=Path("pool.csv"))
    ap.add_argument("--max-loss", type=float, default=20.0, help="per-file loss vs incumbent that disqualifies (pp)")
    a = ap.parse_args()

    d = json.loads(a.operator_json.read_text())
    subs = [s for s in d["submissions"] if s.get("corpora")]
    groups: dict[tuple, list[dict]] = defaultdict(list)
    loose = []
    for s in subs:
        sig = signature(s)
        if sig is None:
            loose.append(s)
        else:
            groups[sig].append(s)
    rows = []
    for members in groups.values():
        members.sort(key=lambda s: (s["submitted_at"], int(s["id"]) if s["id"].isdigit() else 0))
        rep = members[0]
        cs = rep["corpora"]
        worst = {c: worst_loss(rep, c) for c in CORPORA}
        maxloss = max((-w[1] for w in worst.values() if w), default=0.0)
        row = {
            "rep": rep["id"],
            "kind": rep["kind"],
            "who": rep["who"],
            "submitted_at": rep["submitted_at"],
            "members": len(members),
            "member_ids": " ".join(m["id"] for m in members),
            "member_hotkeys": len({m["who"] for m in members}),
            "on_frontier_any": any((m.get("api") or {}).get("on_frontier") for m in members),
            "payable_sum": sum((m.get("api") or {}).get("payable") or 0 for m in members),
            "flags": " ".join(sorted({f for m in members for f in m.get("flags", [])})),
            "retention_c3": (rep.get("retention") or {}).get("c3"),
            "max_file_loss": maxloss,
            "worst_c3": f"{worst['c3'][0]} {worst['c3'][1]:+.1f}" if worst["c3"] else "",
        }
        for c in CORPORA:
            row[f"{c}_mean_pct"] = cs[c]["mean_pct"]
            row[f"{c}_gain"] = cs[c]["file_gain"]
            row[f"{c}_time"] = cs[c]["time_ratio"]
        row["all_mean_pct"] = sum(cs[c]["mean_pct"] for c in CORPORA) / 3
        row["all_time"] = sum(cs[c]["time_ratio"] for c in CORPORA) / 3
        rows.append(row)

    safe = [r for r in rows if r["max_file_loss"] <= a.max_loss]
    scored = frontier([(r["c1_time"] + r["c2_time"], r["c1_mean_pct"] + r["c2_mean_pct"], r["rep"]) for r in rows])
    general = frontier([(r["all_time"], r["all_mean_pct"], r["rep"]) for r in safe])
    for r in rows:
        r["frontier_scored"] = r["rep"] in scored
        r["frontier_general"] = r["rep"] in general

    rows.sort(key=lambda r: r["all_time"])
    with a.out.open("w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=list(rows[0].keys()))
        w.writeheader()
        w.writerows(rows)

    print(f"{len(subs)} rerun submissions -> {len(rows)} behaviour groups ({len(loose)} without full reruns)")
    print(f"groups with more than one member: {sum(r['members'] > 1 for r in rows)}; "
          f"largest: {max(r['members'] for r in rows)}")
    print(f"no file worse than -{a.max_loss:g}% on c1/c2/c3: {len(safe)} groups")
    print(f"frontier on scored corpora (c1+c2), rerun times: {len(scored)} groups; "
          f"general frontier (c1+c2+c3, safe only): {len(general)} groups; overlap {len(set(scored) & set(general))}")
    print()
    print(f"{'rep':>5} {'date':10} {'mem':>3} {'c1%':>7} {'c2%':>7} {'c3%':>7} {'t(all)':>6} {'kept3':>5} {'maxloss':>7}  flags")
    for r in rows:
        if r["frontier_general"]:
            k = r["retention_c3"]
            print(f"{r['rep']:>5} {r['submitted_at'][:10]} {r['members']:>3} {r['c1_mean_pct']:7.3f} {r['c2_mean_pct']:7.3f} "
                  f"{r['c3_mean_pct']:7.3f} {r['all_time']:6.2f} {('%.2f' % k) if k is not None else '-':>5} "
                  f"{r['max_file_loss']:7.1f}  {r['flags']}")


if __name__ == "__main__":
    main()
