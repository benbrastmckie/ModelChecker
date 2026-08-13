"""Unit tests for the CLI invocation-mode vocabulary and dispatch.

Covers `tests/utils/cli_mode.get_cli_test_mode` (mode validation) and
`tests/utils/helpers.run_cli_command` (mode-dispatched command/environment construction).
Written before the implementation (TDD): confirm RED, then implement `cli_mode.py` and the
`run_cli_command` rewrite until these pass GREEN.
"""

from __future__ import annotations

import shutil
import sys
from pathlib import Path
from unittest.mock import patch

import pytest


# ---------------------------------------------------------------------------------------------
# get_cli_test_mode()
# ---------------------------------------------------------------------------------------------


def test_default_mode_is_source(monkeypatch):
    """Absent env var -> 'source', so the existing developer loop is unaffected."""
    monkeypatch.delenv("MODELCHECKER_CLI_TEST_MODE", raising=False)
    from tests.utils.cli_mode import get_cli_test_mode

    assert get_cli_test_mode() == "source"


@pytest.mark.parametrize("mode", ["source", "installed", "installed-module"])
def test_each_known_mode_is_accepted(monkeypatch, mode):
    monkeypatch.setenv("MODELCHECKER_CLI_TEST_MODE", mode)
    from tests.utils.cli_mode import get_cli_test_mode

    assert get_cli_test_mode() == mode


def test_unknown_mode_raises_immediately_with_offending_value(monkeypatch):
    monkeypatch.setenv("MODELCHECKER_CLI_TEST_MODE", "bogus-mode")
    from tests.utils.cli_mode import get_cli_test_mode

    with pytest.raises(ValueError, match="bogus-mode"):
        get_cli_test_mode()


# ---------------------------------------------------------------------------------------------
# run_cli_command dispatch per mode
# ---------------------------------------------------------------------------------------------


def _last_run_call(mock_run):
    """Return (cmd, kwargs) of the most recent subprocess.run call."""
    args, kwargs = mock_run.call_args
    return args[0], kwargs


def test_source_mode_keeps_pythonpath_injection_and_module_invocation(monkeypatch):
    monkeypatch.delenv("MODELCHECKER_CLI_TEST_MODE", raising=False)
    from tests.utils.helpers import run_cli_command

    with patch("subprocess.run") as mock_run:
        mock_run.return_value.returncode = 0
        run_cli_command(["--version"])

    cmd, kwargs = _last_run_call(mock_run)
    assert cmd[0] == sys.executable
    assert cmd[1:3] == ["-m", "model_checker"]
    assert "PYTHONPATH" in kwargs["env"]
    assert kwargs["env"]["PYTHONPATH"].split(__import__("os").pathsep)[0].endswith("src")


def test_installed_mode_pops_pythonpath_and_uses_console_script(monkeypatch):
    monkeypatch.setenv("MODELCHECKER_CLI_TEST_MODE", "installed")
    from tests.utils.helpers import run_cli_command

    with patch("shutil.which", return_value="/usr/bin/model-checker"):
        with patch("subprocess.run") as mock_run:
            mock_run.return_value.returncode = 0
            run_cli_command(["--version"])

    cmd, kwargs = _last_run_call(mock_run)
    assert cmd == ["/usr/bin/model-checker", "--version"]
    assert "PYTHONPATH" not in kwargs["env"]


def test_installed_mode_raises_clear_error_when_console_script_missing(monkeypatch):
    monkeypatch.setenv("MODELCHECKER_CLI_TEST_MODE", "installed")
    from tests.utils.helpers import run_cli_command

    with patch("shutil.which", return_value=None):
        with pytest.raises(RuntimeError, match="model-checker"):
            run_cli_command(["--version"])


def test_installed_module_mode_pops_pythonpath_but_keeps_module_invocation(monkeypatch):
    monkeypatch.setenv("MODELCHECKER_CLI_TEST_MODE", "installed-module")
    from tests.utils.helpers import run_cli_command

    with patch("subprocess.run") as mock_run:
        mock_run.return_value.returncode = 0
        run_cli_command(["--version"])

    cmd, kwargs = _last_run_call(mock_run)
    assert cmd[0] == sys.executable
    assert cmd[1:3] == ["-m", "model_checker"]
    assert "PYTHONPATH" not in kwargs["env"]


def test_unknown_mode_raises_immediately_from_run_cli_command(monkeypatch):
    monkeypatch.setenv("MODELCHECKER_CLI_TEST_MODE", "bogus-mode")
    from tests.utils.helpers import run_cli_command

    with pytest.raises(ValueError, match="bogus-mode"):
        run_cli_command(["--version"])
