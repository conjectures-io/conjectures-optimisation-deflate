"""Stack command ordering and scope without starting services."""

from tools import services


def empty_processes() -> list[dict[str, object]]:
    return []


def test_up_orders_database_before_workers(monkeypatch):
    calls = []
    monkeypatch.setattr(services, "inspect", empty_processes)

    def command(*args):
        calls.append(args)
        return 0

    def start(name, **kwargs):
        calls.append((name,))
        return 0

    monkeypatch.setattr(services, "command", command)
    monkeypatch.setattr(services, "start_background", start)
    assert services.main(["up"]) == 0
    assert calls == [
        ("just", "db-up"),
        ("just", "db-migrate"),
        ("baseline-seed",),
        ("service-worker",),
        ("chain-watcher",),
        ("weight-setter",),
    ]


def test_down_does_not_stop_database_after_worker_failure(monkeypatch):
    calls = []
    monkeypatch.setattr(services, "inspect", empty_processes)

    def start(name, **kwargs):
        assert kwargs == {"stop": True}
        return 2 if name == "service-worker" else 0

    def command(*args):
        calls.append(args)
        return 0

    monkeypatch.setattr(services, "start_background", start)
    monkeypatch.setattr(services, "command", command)
    assert services.main(["down"]) == 2
    assert not calls


def test_logs_exclude_other_competitions(monkeypatch):
    # `miniz-oxide-*` is this competition under its pre-rename name, so it is still ours.
    def inspect():
        return [
            {"name": "deflate-gate-worker", "pm2_env": {"pm_out_log_path": "/tmp/ours"}},
            {"name": "miniz-oxide-weight-setter", "pm2_env": {"pm_out_log_path": "/tmp/old"}},
            {"name": "other-worker", "pm2_env": {"pm_out_log_path": "/tmp/theirs"}},
        ]

    calls = []

    def command(*args):
        calls.append(args)
        return 0

    monkeypatch.setattr(services, "inspect", inspect)
    monkeypatch.setattr(services, "command", command)
    assert services.main(["logs", "--no-follow"]) == 0
    assert calls == [("tail", "-n", "100", "--", "/tmp/ours", "/tmp/old")]
