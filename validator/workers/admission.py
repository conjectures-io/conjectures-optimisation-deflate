"""Publish initial statistical admission or explicitly replay a changed context."""

from __future__ import annotations

import argparse
import json
from pathlib import Path

import db
from db.admission import run


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--preview", action="store_true", help="compute without writing decisions")
    ap.add_argument("--replay", action="store_true", help="allow replacement of existing contexts")
    ap.add_argument(
        "--historical",
        action="store_true",
        help="use historical verification; does not refresh it or enable live scoring",
    )
    ap.add_argument("--out", type=Path, help="write API-ready decision JSON")
    args = ap.parse_args(argv)
    store = db.connect()
    try:
        points = run(
            store.scoring,
            persist=not args.preview,
            replay=args.replay or args.preview,
            historical=args.historical,
        )
        payload = []
        for p in points:
            detail = {**p.admission, "admission_check_id": p.admission_check_id}
            payload.append(detail)
            stats = detail.get("statistics")
            gain = (
                f" measured={stats['gain_pct']:.3f}% lower={stats['lower_pct']:.3f}%"
                if stats
                else ""
            )
            print(
                f"{p.submission_id} {p.baseline_key or p.hotkey}: "
                f"{detail['outcome']} ({detail['reason_code']}){gain}"
            )
        if args.out:
            args.out.parent.mkdir(parents=True, exist_ok=True)
            args.out.write_text(json.dumps(payload, indent=2, allow_nan=False))
        if args.preview:
            print("Preview only: no admission decisions published.")
        return (
            1
            if any(p.admission["outcome"] in {"pending", "invalid_evidence"} for p in points)
            else 0
        )
    finally:
        store.close()


if __name__ == "__main__":
    raise SystemExit(main())
