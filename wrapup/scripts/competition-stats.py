#!/usr/bin/env python3
"""Competition statistics from a PROD dump's tables, as `pg_restore --data-only -t T -f -` text.

    competition-stats.py TABLES_DIR [--json OUT]

Reads submissions, registrations, bounty_accruals, weight_sets (header columns
only) and score_snapshots, streaming the COPY blocks, and prints: submissions
per day, hotkeys and coldkeys, alpha paid and its concentration, frontier size
and pay per scoring pass over time, and the record bytes / time over time.
"""

from __future__ import annotations

import argparse
import json
from collections import Counter, defaultdict
from pathlib import Path

RAO = 1e9


def unescape(v: str) -> str | None:
    if v == r"\N":
        return None
    if "\\" not in v:
        return v
    out, i = [], 0
    while i < len(v):
        c = v[i]
        if c == "\\" and i + 1 < len(v):
            n = v[i + 1]
            out.append({"t": "\t", "n": "\n", "r": "\r", "\\": "\\"}.get(n, n))
            i += 2
        else:
            out.append(c)
            i += 1
    return "".join(out)


def copy_rows(path: Path, want: list[str] | None = None):
    """Yield dicts (only `want` columns) from the COPY block in a pg_restore text file."""
    with path.open(encoding="utf-8", errors="replace") as f:
        cols: list[str] | None = None
        for line in f:
            if cols is None:
                if line.startswith("COPY "):
                    cols = [c.strip() for c in line[line.index("(") + 1:line.index(")")].split(",")]
                    idx = [cols.index(c) for c in (want or cols)]
                continue
            if line.startswith("\\."):
                return
            parts = line.rstrip("\n").split("\t")
            yield {c: unescape(parts[i]) for c, i in zip(want or cols, idx)}


def day(ts: str | None) -> str:
    return (ts or "")[:10]


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("tables", type=Path)
    ap.add_argument("--json", type=Path)
    a = ap.parse_args()
    t = a.tables
    out: dict = {}

    regs = list(copy_rows(t / "registrations.sql", ["uid", "ss58_hot", "ss58_cold", "block_date"]))
    cold_of = {r["ss58_hot"]: r["ss58_cold"] for r in regs}
    subs = list(copy_rows(t / "submissions.sql", ["id", "hotkey", "submitted_at", "state", "bytes", "incumbent_bytes",
                                                   "time_ratio", "baseline_key", "finished_at"]))
    miners = [s for s in subs if not s["baseline_key"]]
    acc = [s for s in miners if s["state"] == "accepted"]
    per_day = Counter(day(s["submitted_at"]) for s in miners)
    acc_day = Counter(day(s["submitted_at"]) for s in acc)
    hot = {s["hotkey"] for s in acc}
    cold = {cold_of.get(h, f"?{h[:8]}") for h in hot}
    out["submissions"] = {
        "miner_total": len(miners), "states": Counter(s["state"] for s in miners),
        "accepted": len(acc), "baselines": sum(1 for s in subs if s["baseline_key"]),
        "first": min(s["submitted_at"] for s in miners), "last": max(s["submitted_at"] for s in miners),
        "hotkeys_accepted": len(hot), "coldkeys_accepted": len(cold),
        "per_day": dict(sorted(per_day.items())), "accepted_per_day": dict(sorted(acc_day.items())),
    }

    # Record progress (official gate numbers): best bytes and best time ratio so far, per day.
    rec_b, rec_t, prog = None, None, {}
    for s in sorted(acc, key=lambda s: s["submitted_at"]):
        b, tr = s["bytes"], s["time_ratio"]
        if b and (rec_b is None or int(b) < rec_b[0]):
            rec_b = (int(b), s["id"])
        if tr and (rec_t is None or float(tr) < rec_t[0]):
            rec_t = (float(tr), s["id"])
        prog[day(s["submitted_at"])] = {"best_bytes": rec_b, "best_time_ratio": rec_t}
    out["records"] = prog

    # Alpha paid.
    by_hot, by_cold, by_day, total = Counter(), Counter(), Counter(), 0
    for r in copy_rows(t / "bounty_accruals.sql", ["hotkey", "coldkey", "alpha_rao", "created_at"]):
        v = int(r["alpha_rao"] or 0)
        total += v
        by_hot[r["hotkey"]] += v
        by_cold[r["coldkey"] or cold_of.get(r["hotkey"], "?")] += v
        by_day[day(r["created_at"])] += v
    top = by_cold.most_common()
    hhi = sum((v / total) ** 2 for _, v in top) if total else 0.0
    out["alpha"] = {
        "total": total / RAO, "hotkeys_paid": len(by_hot), "coldkeys_paid": len(by_cold),
        "top_coldkeys": [(k, v / RAO, v / total) for k, v in top[:10]] if total else [],
        "top2_share": sum(v for _, v in top[:2]) / total if total else 0.0,
        "hhi": hhi, "per_day": {d: v / RAO for d, v in sorted(by_day.items())},
    }

    # Frontier per scoring pass.
    ws_time = {r["id"]: r["created_at"] for r in copy_rows(t / "weight_sets.sql", ["id", "created_at"])}
    front = defaultdict(set)
    paid = defaultdict(float)
    ever = Counter()
    for r in copy_rows(t / "score_snapshots.sql", ["weight_set_id", "submission_id", "on_frontier", "combined_weight", "baseline_key"]):
        if r["on_frontier"] == "t":
            front[r["weight_set_id"]].add(r["submission_id"])
            if not r["baseline_key"]:
                ever[r["submission_id"]] += 1
            paid[r["weight_set_id"]] += float(r["combined_weight"] or 0)
    per_day_front = defaultdict(list)
    for ws, ids in front.items():
        per_day_front[day(ws_time.get(ws))].append(len(ids))
    out["frontier"] = {
        "passes": len(front),
        "size_per_day": {d: {"min": min(v), "max": max(v), "last": v[-1]} for d, v in sorted(per_day_front.items())},
        "submissions_ever_on_frontier": len(ever),
        "longest_on_frontier": [(k, v) for k, v in ever.most_common(10)],
    }

    s = out["submissions"]
    print(f"miner submissions {s['miner_total']} ({dict(s['states'])}), {s['baselines']} baselines; "
          f"{s['first'][:16]} .. {s['last'][:16]}")
    print(f"accepted from {s['hotkeys_accepted']} hotkeys / {s['coldkeys_accepted']} coldkeys")
    print("accepted per day: " + ", ".join(f"{d[5:]} {n}" for d, n in s["accepted_per_day"].items()))
    al = out["alpha"]
    print(f"alpha paid {al['total']:.1f} to {al['hotkeys_paid']} hotkeys / {al['coldkeys_paid']} coldkeys; "
          f"top-2 coldkeys {100 * al['top2_share']:.0f}%, HHI {al['hhi']:.3f}")
    print("frontier size by day (last pass): " + ", ".join(f"{d[5:]} {v['last']}" for d, v in out["frontier"]["size_per_day"].items()))
    print(f"submissions ever on the frontier: {out['frontier']['submissions_ever_on_frontier']}")
    last = list(prog.items())[-1][1] if prog else {}
    print(f"records: best bytes {last.get('best_bytes')}, best time ratio {last.get('best_time_ratio')}")
    if a.json:
        a.json.write_text(json.dumps(out, indent=1, default=list))


if __name__ == "__main__":
    main()
