"""The gate's arithmetic: what counts as passing, in one place.

The engine measures and decides nothing. This is the other half -- the floor,
the correctness rule, and the words for the outcome -- so the gate and the tool
a miner runs while tuning cannot disagree about what would happen.
"""

from __future__ import annotations

from dataclasses import dataclass

from .results import INCUMBENT, Run

#: Slower than this multiple of the incumbent is rejected. Loose on purpose:
#: SIMD must not decide it.
SPEED_FLOOR = 8.0


@dataclass(frozen=True)
class Verdict:
    method: str
    #: Correct, and inside the speed floor. This is what the exit code means.
    accepted: bool
    #: Smaller than the incumbent. A correct, fast, larger parser is accepted
    #: and simply does not win.
    improved: bool
    ratio: float
    slowdown: float
    reason: str
    failures: tuple[str, ...]

    def line(self) -> str:
        if not self.accepted:
            return f"REJECTED — {self.reason}"
        return ("ACCEPTED — " if self.improved else "") + self.reason


def judge(run: Run, method: str, floor: float = SPEED_FLOOR) -> Verdict:
    ratio = run.ratio(method)
    slowdown = run.slowdown(method)
    failures = run.failures(method)

    def rejected(reason: str) -> Verdict:
        return Verdict(method, False, False, ratio, slowdown, reason, failures)

    def passed(improved: bool, reason: str) -> Verdict:
        return Verdict(method, True, improved, ratio, slowdown, reason, failures)

    # The reference itself misbehaved: nothing measured here means anything.
    if incumbent := run.failures(INCUMBENT):
        return rejected(f"the incumbent failed: {incumbent[0]}")
    if failures:
        return rejected(f"{len(failures)} correctness failure(s)")
    if slowdown > floor:
        return rejected(f"{slowdown:.2f}x slower than the incumbent, floor is {floor:.1f}x")
    if ratio < 1.0:
        return passed(True, f"{(1.0 - ratio) * 100:.3f}% smaller than the incumbent.")
    if ratio > 1.0:
        return passed(
            False, f"no improvement — {(ratio - 1.0) * 100:.3f}% larger than the incumbent."
        )
    return passed(False, "no change — byte-identical to the incumbent.")
