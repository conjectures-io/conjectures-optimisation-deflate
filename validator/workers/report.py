"""Operator-only database scoring preview and reproducible plots; never sets weights."""

from __future__ import annotations

import argparse
import dataclasses
import json
from pathlib import Path

import db
import scoring
from scoring.pareto import global_coefficients, local_coefficients


def main(argv: list[str] | None = None) -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--method")
    ap.add_argument("--aggregation-id", type=int, action="append")
    ap.add_argument("--out-dir", type=Path)
    ap.add_argument(
        "--metagraph",
        type=Path,
        help="JSON hotkey-to-uid mapping; absent means provisional payments",
    )
    ap.add_argument("--burn-uid", type=int, default=0)
    args = ap.parse_args(argv)
    config = scoring.ScoringConfig.from_env()
    if args.method:
        config = dataclasses.replace(config, method=args.method)
    eligible = None
    if args.metagraph:
        eligible = {
            key
            for key, uid in json.loads(args.metagraph.read_text()).items()
            if uid != args.burn_uid
        }
    store = db.connect()
    try:
        rows = store.scoring.scoring_inputs(aggregation_ids=args.aggregation_id)
        from sqlalchemy import select

        from db.models import BenchmarkAggregation, BenchmarkAggregationInput

        provenance = {}
        with store.sessions() as session:
            for row in rows:
                aggregation = session.get(BenchmarkAggregation, row.aggregation_id)
                provenance[str(row.submission_id)] = {
                    "source_sha256": aggregation.source_sha256,
                    "aggregation_id": aggregation.id,
                    "calculator_version": aggregation.calculator_version,
                    "run_ids": list(
                        session.scalars(
                            select(BenchmarkAggregationInput.run_id).where(
                                BenchmarkAggregationInput.aggregation_id == aggregation.id
                            )
                        )
                    ),
                    "timing": {
                        k: v for k, v in (aggregation.statistics or {}).items() if k != "files"
                    },
                }
    finally:
        store.close()
    result = scoring.score(rows, rows, config, eligible_hotkeys=eligible)
    print(f"method={config.method} points={len(rows)} frontier={len(result.frontier.frontier)}")
    if eligible is None:
        print("Registration eligibility unknown: miner payments below are provisional.")
    points = result.frontier.points
    front = sorted((points[key] for key in result.frontier.frontier), key=lambda p: p.time_s)
    local = local_coefficients(front, 2.0, 0.0) if front else {}
    glob = global_coefficients(front, 2.0, 0.0) if front else {}
    output = []
    previous = None
    for s in sorted(result.scores, key=lambda s: s.time_s):
        key = str(s.submission_id)
        label = s.baseline_key or s.hotkey or key
        row = dataclasses.asdict(s) | {
            "label": label,
            "local": local.get(key),
            "global": glob.get(key),
        }
        if s.on_frontier:
            if previous is not None:
                row["time_change_pct"] = 100 * (s.time_s / previous.time_s - 1)
                row["size_change_pct"] = (
                    100 * (s.ratio_pct / previous.ratio_pct - 1) if previous.ratio_pct else None
                )
            previous = s
        output.append(row)
        print(
            f"{s.submission_id:>5} {label:<18} {s.time_s:>9.5f}s {s.ratio_pct:>7.3f}% "
            f"frontier={s.on_frontier} pareto={s.pareto_weight:.5f} "
            f"recency={s.improvement_weight:.5f} payable={s.payable_weight:.5f} "
            f"{s.burn_reason or ''}"
        )
    print(f"burn={result.burn_weight:.5f}")
    if args.out_dir:
        args.out_dir.mkdir(parents=True, exist_ok=True)
        payload = {
            "config": dataclasses.asdict(config),
            "sources": provenance,
            "points": output,
            "context": rows[0].context if rows else None,
            "registration_eligibility_known": result.eligibility_known,
            "burn": result.burn_weight,
        }
        (args.out_dir / "scores.json").write_text(json.dumps(payload, indent=2, allow_nan=False))
        plot(result, args.out_dir)


def plot(result, directory):
    import matplotlib

    matplotlib.use("Agg")
    import matplotlib.pyplot as plt

    fig, axes = plt.subplots(1, 2, figsize=(14, 5))
    ordered = sorted(result.scores, key=lambda s: s.time_s)
    for index, s in enumerate(ordered):
        label = s.baseline_key or s.hotkey or str(s.submission_id)
        axes[0].scatter(s.time_s, s.ratio_pct, marker="s" if s.baseline_key else "o")
        axes[0].annotate(
            label,
            (s.time_s, s.ratio_pct),
            xytext=(4, 8 if index % 2 == 0 else -14),
            textcoords="offset points",
            fontsize=8,
        )
    front = [s for s in ordered if s.on_frontier]
    axes[0].plot([s.time_s for s in front], [s.ratio_pct for s in front], "--", color="gray")
    labels = [s.baseline_key or f"{s.hotkey}:{s.submission_id}" for s in ordered]
    paid = [s.payable_weight for s in ordered]
    burned = [s.combined_weight - s.payable_weight for s in ordered]
    unclaimed = max(0.0, 1.0 - sum(s.combined_weight for s in ordered))
    if unclaimed > 0:
        labels.append("unclaimed")
        paid.append(0.0)
        burned.append(unclaimed)
    axes[1].bar(labels, paid, label="payable (provisional without metagraph)")
    axes[1].bar(labels, burned, bottom=paid, label="burned allocation")
    axes[1].tick_params(axis="x", rotation=60)
    axes[1].legend()
    if ordered and all(s.time_s > 0 for s in ordered):
        axes[0].set_xscale("log")
    axes[0].margins(x=0.15, y=0.15)
    axes[0].set(xlabel="Sum of per-file median parse seconds", ylabel="Compressed / raw (%)")
    axes[1].set(ylabel="Share of total emission")
    fig.tight_layout()
    fig.savefig(directory / "pareto.png", dpi=160)
    plt.close(fig)


if __name__ == "__main__":
    main()
