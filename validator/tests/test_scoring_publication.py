"""Unchanged polls reuse evidence; actual chain attempts keep their own audit rows."""

from copy import deepcopy
from typing import NotRequired, TypedDict

import pytest
import sqlalchemy as sa
from test_weight_setter import (
    CONFIG,
    PARAMS,
    SCORING,
    FakeChain,
    accept,
    at_epoch_boundary,
    snapshots,
    weight_sets,
)

from db import models
from workers.weight_setter import step


class Publication(TypedDict):
    netuid: int
    block: int
    uids: list[int]
    weights: list[float]
    summary: str
    accepted: bool
    snapshots: list[dict[str, object]]
    api_snapshot: dict[str, object]
    reuse_unchanged: bool
    dry_run: NotRequired[bool]


def publication() -> Publication:
    return {
        "netuid": 66,
        "block": 100,
        "uids": [1],
        "weights": [1.0],
        "summary": "scores",
        "accepted": False,
        "snapshots": [{"hotkey": "alice", "payable_weight": 1.0}],
        "api_snapshot": {"computed_at": "first", "items": [], "policy": {}, "bounty": {}},
        "reuse_unchanged": True,
    }


def test_unchanged_publication_reuses_scores_across_restart_and_keeps_original_time(store):
    values = publication()
    first, created = store.scoring.publish_weight_set(**values)
    assert created
    store.scoring.weight_set_outcome(first, accepted=True, error=None)
    values["block"] = 200
    values["api_snapshot"]["computed_at"] = "second"
    # Identity is persisted in the database, not held in a worker's memory.
    second, created = store.scoring.publish_weight_set(**values)
    assert (second, created) == (first, False)
    rows = weight_sets(store)
    assert len(rows) == 1 and rows[0].block == 100 and rows[0].accepted
    assert rows[0].api_snapshot is not None
    assert rows[0].api_snapshot["computed_at"] == "first"
    assert len(snapshots(store, first)) == 1


@pytest.mark.parametrize("change", ["bounty", "policy", "membership", "scores", "uids", "dry_run"])
def test_relevant_changes_publish_new_evidence(store, change):
    values = publication()
    first, _ = store.scoring.publish_weight_set(**values)
    changed = deepcopy(values)
    if change in ("bounty", "policy"):
        changed["api_snapshot"][change] = {"changed": True}
    elif change == "membership":
        changed["api_snapshot"]["items"] = [{"submission": {"id": 1}}]
    elif change == "scores":
        changed["snapshots"][0]["payable_weight"] = 0.5
    elif change == "uids":
        changed["uids"] = [2]
    else:
        changed["dry_run"] = True
    second, created = store.scoring.publish_weight_set(**changed)
    assert created and second != first
    # A -> B -> A is a new publication; do not reuse arbitrary historical rows.
    third, created = store.scoring.publish_weight_set(**values)
    assert created and third not in (first, second)


def test_cleared_payload_is_republished_even_when_content_hash_matches(store):
    values = publication()
    first, _ = store.scoring.publish_weight_set(**values)
    with store.engine.begin() as conn:
        conn.execute(sa.update(models.WeightSet).values(api_snapshot=sa.null()))
    second, created = store.scoring.publish_weight_set(**values)
    assert created and second != first


def test_waiting_polls_reuse_snapshot_but_real_attempts_have_distinct_records(store):
    accept(store, "alice", 2_000_000, 0.4)
    chain = FakeChain(hotkeys={"alice": 1}, block=at_epoch_boundary(), since=0)
    first = step(chain, store, CONFIG, SCORING, PARAMS)
    second = step(chain, store, CONFIG, SCORING, PARAMS)
    assert first.action == second.action == "wait"
    assert first.weight_set_id == second.weight_set_id
    assert len(weight_sets(store)) == 1

    chain.since = 1000
    attempt = step(chain, store, CONFIG, SCORING, PARAMS)
    assert attempt.action == "set" and attempt.weight_set_id != first.weight_set_id
    assert attempt.weight_set_id is not None
    assert len(snapshots(store, attempt.weight_set_id)) == 1
    chain.since = 0
    waiting = step(chain, store, CONFIG, SCORING, PARAMS)
    assert waiting.weight_set_id == attempt.weight_set_id
    assert weight_sets(store)[-1].accepted
    assert len(weight_sets(store)) == 2

    chain.since = 1000
    chain.block += 100
    chain.last_epoch = chain.block - 90
    chain.accept = False
    refused = step(chain, store, CONFIG, SCORING, PARAMS)
    assert refused.action == "failed"
    assert refused.weight_set_id != attempt.weight_set_id
    assert len(weight_sets(store)) == 3
    assert weight_sets(store)[1].accepted and not weight_sets(store)[2].accepted
