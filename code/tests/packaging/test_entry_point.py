"""Console-script entry-point assertion for the packaging contract.

Installs the built wheel into a fresh venv and proves the `model-checker` console script
installs and runs, and that the declared `[project.scripts]` entry point resolves. This is a
minimal declare-install-run liveness check -- no assertions about CLI output content beyond
non-empty output. Broader console-script behavior coverage lives in
`code/tests/packaging/test_cli_console_script.py`.

`installed_venv` and `_console_script_path` are defined in `conftest.py` (shared across
`tests/packaging/`, not duplicated here) so this file's fixture-setup responsibility is limited
to consuming them.

Uses the same CI-gated skip/fail provisioning-failure policy as `conftest.py`'s
`packaging_toolchain` fixture: never a silent pass.
"""

import os
import subprocess

import pytest

from .conftest import _console_script_path

pytestmark = [pytest.mark.packaging, pytest.mark.slow]


def test_console_script_installed_and_executable(installed_venv):
    script_path = _console_script_path(installed_venv)
    assert script_path.exists(), f"console script not found at {script_path}"
    if os.name != "nt":
        assert os.access(script_path, os.X_OK), f"console script not executable: {script_path}"


def test_console_script_runs(installed_venv):
    """`--version` is confirmed supported (argparse `action='version'`); no `--help` fallback
    is needed."""
    script_path = _console_script_path(installed_venv)
    result = subprocess.run(
        [str(script_path), "--version"],
        env=installed_venv["env"],
        capture_output=True,
        text=True,
    )
    assert result.returncode == 0, (
        f"model-checker --version exited {result.returncode}:\n"
        f"STDOUT:\n{result.stdout}\nSTDERR:\n{result.stderr}"
    )
    assert result.stdout.strip(), "model-checker --version produced no stdout"


def test_entry_point_module_importable(installed_venv):
    """Confirms the declared `[project.scripts]` entry point
    (`model-checker = "model_checker.__main__:run"`) resolves in the installed venv."""
    result = subprocess.run(
        [str(installed_venv["python"]), "-c", "from model_checker.__main__ import run"],
        env=installed_venv["env"],
        capture_output=True,
        text=True,
    )
    assert result.returncode == 0, (
        f"model_checker.__main__.run not importable in installed venv:\n"
        f"STDOUT:\n{result.stdout}\nSTDERR:\n{result.stderr}"
    )
