"""What a gate run's report says, as the fields of a `gate_verdict` event.

verify.py ends its report with one verdict line -- `REJECTED at stage <stage>` followed by the
reason, `VALIDATOR ERROR` followed by the problem, or nothing when every stage passed -- and the
worker appends its own `REJECTED: ...` for a timeout or a spent registration. Reading those
lines here keeps the gate worker's own edit (a pinned file) to the calls that emit events.
"""

from __future__ import annotations

import re

# The last stage; an accepted submission passed all of them.
FINAL_STAGE = "6 (score)"
_STAGE = re.compile(r"^REJECTED at stage (?P<stage>.+?)\s*$\n^\s*(?P<reason>.*)$", re.M)
_ERROR = re.compile(r"^VALIDATOR ERROR\s*$\n^\s*(?P<reason>.*)$", re.M)
_WORKER = re.compile(r"^REJECTED: (?P<reason>.*)$", re.M)


def _last(pattern: re.Pattern[str], report: str) -> re.Match[str] | None:
    matches = list(pattern.finditer(report))
    return matches[-1] if matches else None


def verdict_fields(
    report: str | None, *, state: str, gate_state: str | None = None
) -> dict[str, object]:
    """`stage` reached and `reason`, from a run's report, its final state and the gate's own.

    `gate_state` is what verify.py's exit code said; it differs from `state` only when the gate
    accepted a submission whose hotkey had no registration left to spend.
    """
    report = report or ""
    if state == "accepted":
        return {"stage": FINAL_STAGE, "reason": None}
    if state == "rejected" and gate_state == "accepted":
        return {
            "stage": "entitlement",
            "reason": "accepted by the gate, but the hotkey has no unclaimed registration left",
        }
    if (worker := _last(_WORKER, report)) is not None:
        reason = worker["reason"].strip()
        # The worker's own: the gate ran out of time.
        return {"stage": "timeout", "reason": reason[:1000]}
    if (rejected := _last(_STAGE, report)) is not None:
        return {"stage": rejected["stage"], "reason": rejected["reason"].strip()[:1000]}
    if (error := _last(_ERROR, report)) is not None:
        return {"stage": "infrastructure", "reason": error["reason"].strip()[:1000]}
    return {"stage": None, "reason": None}


def vs_incumbent(measured: dict[str, int | float]) -> float | None:
    """Bytes over the incumbent's, as the API's leaderboard reports it."""
    size, incumbent = measured.get("bytes"), measured.get("incumbent_bytes")
    return round(size / incumbent, 5) if size is not None and incumbent else None


__all__ = ["FINAL_STAGE", "verdict_fields", "vs_incumbent"]
