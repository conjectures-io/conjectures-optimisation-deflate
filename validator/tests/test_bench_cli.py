"""Host failures should be visible, with local-only resource-limit fallback."""

from __future__ import annotations

import shutil
import subprocess
import sys
from pathlib import Path
from unittest.mock import Mock

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from bench import __main__ as cli  # noqa: E402
from bench import driver  # noqa: E402
from bench.errors import Misconfigured  # noqa: E402
from sandbox import bwrap  # noqa: E402


def test_cli_reports_build_diagnostics(
    monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str], tmp_path: Path
):
    monkeypatch.setattr(cli, "configure", Mock(return_value=None))
    monkeypatch.setattr(cli, "candidates", Mock(return_value={}))
    monkeypatch.setattr(cli, "corpus", Mock(return_value=None))

    monkeypatch.setattr(
        cli,
        "run",
        Mock(side_effect=driver.BuildFailed("incumbent", "compiler diagnostic", tmp_path)),
    )
    assert cli.main([]) == 2
    assert capsys.readouterr().err == "incumbent does not build\ncompiler diagnostic\n"


def test_resource_failure_falls_back_only_for_cli(monkeypatch: pytest.MonkeyPatch, tmp_path: Path):
    config = driver.Config(validator=tmp_path, workspace=tmp_path / "runs")
    config.engine.parent.mkdir(parents=True)
    config.engine.touch()
    monkeypatch.setattr(driver.Config, "from_env", Mock(return_value=config))
    monkeypatch.setattr(bwrap, "check", Mock(return_value=None))
    monkeypatch.setattr(shutil, "which", Mock(return_value="/usr/bin/systemd-run"))
    calls: list[list[str]] = []

    def unavailable(argv: list[str], **_kwargs: object):
        calls.append(argv)
        return subprocess.CompletedProcess(argv, 1, "", "Failed to connect to bus")

    monkeypatch.setattr(subprocess, "run", unavailable)
    with pytest.raises(Misconfigured, match="Failed to connect to bus"):
        driver.check(config)
    local = cli.configure(cli.parse_args([]))
    assert local.enabled
    assert local.memory_mb == local.build_memory_mb == 0
    assert local.cpus == ""
    assert all("--scope" in argv for argv in calls)
