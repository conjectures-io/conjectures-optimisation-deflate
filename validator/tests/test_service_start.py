"""PM2 startup must never launch a duplicate or bypass an inspection failure."""

import json
import shutil
import subprocess
from subprocess import CompletedProcess

import pytest

from tools import service_start


def missing_pm2(_name: str) -> None:
    return None


def installed_pm2(_name: str) -> str:
    return "/bin/pm2"


def test_missing_pm2(monkeypatch, capsys):
    monkeypatch.setattr(shutil, "which", missing_pm2)
    assert service_start.start_background("service-worker") == 2
    assert "npm install -g pm2" in capsys.readouterr().err


@pytest.mark.parametrize(
    "banner", ["", "[PM2] Spawning PM2 daemon\n[PM2] PM2 Successfully daemonized\n"]
)
@pytest.mark.parametrize("status", ["online", "launching"])
def test_existing_service_is_not_started(monkeypatch, tmp_path, capsys, status, banner):
    monkeypatch.setattr(service_start, "ROOT", tmp_path)
    monkeypatch.setattr(shutil, "which", installed_pm2)
    calls = []

    def run(args, **kwargs):
        calls.append(args)
        return CompletedProcess(
            args,
            0,
            banner
            + json.dumps(
                [
                    {
                        "name": "miniz-oxide-gate-worker",
                        "pm_id": 7,
                        "pm2_env": {"status": status},
                    }
                ]
            ),
        )

    monkeypatch.setattr(subprocess, "run", run)
    assert service_start.start_background("service-worker") == 0
    assert len(calls) == 1
    assert "no duplicate started" in capsys.readouterr().err


@pytest.mark.parametrize(
    "output,code,expected_calls",
    [
        ("[]", 0, 2),
        ("[PM2] Successfully daemonized\n[]\n", 0, 2),
        ("bad json", 0, 1),
        ("", 1, 1),
        ("[null]", 0, 1),
        ("[{}]", 0, 1),
        ('[\n{"name":"broken","args":[]', 0, 1),
    ],
)
def test_start_requires_successful_inspection(monkeypatch, tmp_path, output, code, expected_calls):
    monkeypatch.setattr(service_start, "ROOT", tmp_path)
    monkeypatch.setattr(shutil, "which", installed_pm2)
    calls = []

    def run(args, **kwargs):
        calls.append(args)
        return CompletedProcess(args, code, output)

    monkeypatch.setattr(subprocess, "run", run)
    result = service_start.start_background("service-worker")
    assert len(calls) == expected_calls
    if expected_calls == 2:
        assert result == 0
        assert calls[-1][-2:] == ["--only", "miniz-oxide-gate-worker"]
    else:
        assert result != 0


@pytest.mark.parametrize("present", [False, True])
def test_stop_only_selected_service(monkeypatch, tmp_path, present):
    monkeypatch.setattr(service_start, "ROOT", tmp_path)
    monkeypatch.setattr(shutil, "which", installed_pm2)
    processes = [{"name": "unrelated", "pm_id": 9, "pm2_env": {}}]
    if present:
        processes.append({"name": "miniz-oxide-gate-worker", "pm_id": 7, "pm2_env": {}})
    calls = []

    def run(args, **kwargs):
        calls.append(args)
        return CompletedProcess(args, 0, json.dumps(processes))

    monkeypatch.setattr(subprocess, "run", run)
    assert service_start.start_background("service-worker", stop=True) == 0
    assert len(calls) == (2 if present else 1)
    if present:
        assert calls[-1] == ["/bin/pm2", "stop", "7"]


@pytest.mark.parametrize("status", ["stopped", "errored", "online"])
def test_background_resumes_existing_entry(monkeypatch, tmp_path, status):
    monkeypatch.setattr(service_start, "ROOT", tmp_path)
    monkeypatch.setattr(shutil, "which", installed_pm2)
    calls = []

    def run(args, **kwargs):
        calls.append(args)
        return CompletedProcess(
            args,
            0,
            json.dumps(
                [
                    {
                        "name": "miniz-oxide-gate-worker",
                        "pm_id": 7,
                        "pm2_env": {"status": status},
                    }
                ]
            ),
        )

    monkeypatch.setattr(subprocess, "run", run)
    assert service_start.start_background("service-worker", restart=status == "online") == 0
    assert calls[-1] == ["/bin/pm2", "restart", "7"]
    assert len(calls) == 2
