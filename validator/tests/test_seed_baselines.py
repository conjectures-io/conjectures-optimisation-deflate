"""Baselines seed themselves as the validator starts, and find the toolchain the gate uses."""

import subprocess
from pathlib import Path

import pytest

from bench import baselines
from tools import seed_baselines


@pytest.mark.parametrize(
    ("value", "expected"),
    [(None, True), ("1", True), ("yes", True), ("0", False), ("false", False), (" OFF ", False)],
)
def test_seeding_is_on_unless_turned_off(value, expected):
    env = {} if value is None else {"BASELINE_SEED_ON_START": value}
    assert seed_baselines.enabled(env) is expected


def test_turned_off_builds_and_seeds_nothing(monkeypatch, capsys):
    monkeypatch.setenv("BASELINE_SEED_ON_START", "0")

    def forbidden(*args, **kwargs):
        raise AssertionError("seeding ran while turned off")

    monkeypatch.setattr(subprocess, "run", forbidden)
    monkeypatch.setattr(baselines, "main", forbidden)
    assert seed_baselines.main([]) == 0
    assert "not seeding" in capsys.readouterr().out


def test_seeding_builds_both_crates_then_passes_arguments_through(monkeypatch, tmp_path):
    monkeypatch.setenv("BASELINE_SEED_ON_START", "1")
    built, seeded = [], []
    monkeypatch.setattr(seed_baselines, "cargo", lambda: "/bin/cargo")

    def run(args: list[str], cwd: Path, check: bool = False, **kwargs: object):
        built.append((args, cwd.name))
        return subprocess.CompletedProcess(args, 0)

    def seed(argv):
        seeded.append(argv)
        return 0

    monkeypatch.setattr(subprocess, "run", run)
    monkeypatch.setattr(baselines, "main", seed)
    assert seed_baselines.main(["--only", "lazy"]) == 0
    assert [cwd for _, cwd in built] == ["slot", "measure"]
    assert all(args == ["/bin/cargo", "build", "--release", "-q"] for args, _ in built)
    assert seeded == [["--only", "lazy"]]


def test_toolchain_path_puts_the_configured_elan_first(monkeypatch, tmp_path):
    # verifier/config.sh honours an operator ELAN_HOME; the seeder must see what the gate sees.
    monkeypatch.setenv("ELAN_HOME", str(tmp_path / "elan"))
    monkeypatch.setenv("PATH", "/usr/bin:/bin")
    path = baselines.toolchain_path().split(":")
    assert path[0] == str(tmp_path / "elan" / "bin")
    assert "/usr/bin" in path
