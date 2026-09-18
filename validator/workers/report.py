"""What the scorer would pay right now, printed.

    cd validator && python -m workers.report        (or: just weights-preview)

Reads the store and nothing else -- no chain, no wallet, no writes. It is the answer to
"why did I get that weight", runnable by an operator on a live validator without
disturbing anything, and the fastest way to see what a change to the scoring knobs would
do before setting them.
"""

from __future__ import annotations

import argparse
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

import db  # noqa: E402
import scoring  # noqa: E402


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--method", help=f"override the weight function: {sorted(scoring.METHODS)}")
    args = ap.parse_args()

    config = scoring.ScoringConfig.from_env()
    if args.method:
        config = scoring.ScoringConfig(
            method=args.method,
            pareto_share=config.pareto_share,
            improvement_share=config.improvement_share,
            improvement_window=config.improvement_window,
            improvement_threshold=config.improvement_threshold,
            improvement_decay=config.improvement_decay,
            speed_floor=config.speed_floor,
        )

    store = db.connect()
    try:
        best = store.scoring.best_per_hotkey()
        history = store.scoring.accepted_history()
    finally:
        store.close()

    if not best:
        print("nothing accepted yet: the whole vector would burn")
        return

    result = scoring.score(best, history, config)
    bounds = result.frontier.bounds
    print(
        f"method={config.method}  "
        f"split={config.pareto_share:.2f}/{config.improvement_share:.2f}  "
        f"window={config.improvement_window}  threshold={config.improvement_threshold:.4%}"
    )
    print(
        f"time boundary {bounds.time_s:.3f}s "
        f"({config.speed_floor:g}x the incumbent), {len(best)} competitor(s), "
        f"{len(result.frontier.frontier)} on the frontier\n"
    )
    print(
        f"{'hotkey':<12} {'time (s)':>9} {'ratio (%)':>10} {'front':>6} "
        f"{'pareto':>8} {'recency':>8} {'total':>8}"
    )
    for s in sorted(result.scores, key=lambda s: -s.combined_weight):
        time_s = f"{s.time_s:.4f}" if s.time_s is not None else "-"
        ratio = f"{s.ratio_pct:.3f}" if s.ratio_pct is not None else "-"
        print(
            f"{s.hotkey[:12]:<12} {time_s:>9} {ratio:>10} {'yes' if s.on_frontier else 'no':>6} "
            f"{s.pareto_weight:>8.4f} {s.improvement_weight:>8.4f} {s.combined_weight:>8.4f}"
        )
    paid = sum(s.combined_weight for s in result.scores)
    print(f"\n{'':<12} {'':>9} {'':>10} {'':>6} {'':>8} {'burn':>8} {1.0 - paid:>8.4f}")

    if result.improvements:
        print("\nrecent improvements, newest first:")
        for i, event in enumerate(result.improvements):
            print(
                f"  {i + 1:>2}. {event.hotkey[:12]:<12} submission {event.submission_id:<6} "
                f"{event.bytes} bytes, {event.relative_gain:.3%} under {event.previous_best}"
            )
    else:
        print("\nno improvement has beaten the incumbent yet: the recency share burns")


if __name__ == "__main__":
    main()
