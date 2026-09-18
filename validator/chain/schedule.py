"""When to set weights: once an epoch, a margin before the boundary, inside the limit."""

from __future__ import annotations

import dataclasses as dc


@dc.dataclass(frozen=True, slots=True)
class SetDecision:
    proceed: bool
    rate_off_blocks: int
    epoch_blocks: int
    next_try_block: int


def blocks_until_next_epoch(current_block: int, tempo: int, netuid: int) -> int:
    # The subnet's epoch boundary is offset by its netuid, which is why it appears here.
    if tempo <= 0:
        return 0
    return tempo - (current_block + netuid + 1) % (tempo + 1)


def should_set(
    *,
    current_block: int,
    tempo: int,
    netuid: int,
    blocks_since_last_update: int,
    weights_rate_limit: int,
    set_margin: int,
) -> SetDecision:
    """Proceed only when the rate limit is clear and the epoch boundary is close.

    Setting late in the epoch means the vector lands just before consensus reads it, so
    it reflects the newest scores; setting early wastes the window and risks the rate
    limit blocking the one that would have mattered. `next_try_block` is what the caller
    logs so an operator can see when the next attempt is due rather than watching a
    silent loop.
    """
    rate_off_blocks = max(0, weights_rate_limit - blocks_since_last_update)
    epoch_blocks = blocks_until_next_epoch(current_block, tempo, netuid)
    rate_clear = current_block + rate_off_blocks
    margin_wait = max(0, blocks_until_next_epoch(rate_clear, tempo, netuid) - set_margin)
    next_try_block = rate_clear + margin_wait
    proceed = rate_off_blocks == 0 and epoch_blocks <= set_margin
    return SetDecision(proceed, rate_off_blocks, epoch_blocks, next_try_block)
