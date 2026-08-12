"""Console-script entry-point assertion for the packaging contract.

Installs the built wheel into a fresh venv and proves the `model-checker` console script
installs and runs, and that the declared `[project.scripts]` entry point resolves. This is a
minimal declare-install-run liveness check -- no assertions about CLI output content beyond
non-empty output. Broader console-script behavior coverage belongs to `code/tests/e2e/`.

Uses the same CI-gated skip/fail provisioning-failure policy as `conftest.py`'s
`packaging_toolchain` fixture: never a silent pass.
"""

import os
import subprocess
from pathlib import Path

import pytest

pytestmark = [pytest.mark.packaging, pytest.mark.slow]


def _provisioning_failure(reason: str) -> None:
    if os.environ.get("CI"):
        pytest.fail(reason)
    else:
        pytest.skip(reason)


def _venv_bin_dir(venv_dir: Path) -> Path:
    bin_dir = venv_dir / "bin"
    if not bin_dir.is_dir():
        bin_dir = venv_dir / "Scripts"  # pragma: no cover -- Windows path
    return bin_dir


@pytest.fixture(scope="session")
def installed_venv(built_artifacts, tmp_path_factory):
    """Create a fresh venv under a pytest temp dir and install the built wheel into it."""
    import venv

    venv_dir = tmp_path_factory.mktemp("pkgentryvenv")
    try:
        venv.EnvBuilder(with_pip=True).create(venv_dir)
    except Exception as exc:  # pragma: no cover -- environment-dependent failure path
        _provisioning_failure(f"Failed to create entry-point venv at {venv_dir}: {exc}")
        raise RuntimeError("unreachable")  # pragma: no cover

    bin_dir = _venv_bin_dir(venv_dir)
    interp = bin_dir / ("python.exe" if os.name == "nt" else "python")

    # Strip PYTHONPATH: the outer test invocation typically runs with PYTHONPATH=src (per
    # project convention) so that the source tree resolves on sys.path -- inherited verbatim
    # into this subprocess, that would make pip's "already satisfied" check see model_checker
    # as already importable via the source tree and skip (re)installing the wheel, silently
    # leaving the console script uninstalled. This venv must resolve model_checker from its own
    # site-packages only.
    env = {k: v for k, v in os.environ.items() if k != "PYTHONPATH"}
    env["PIP_USER"] = "0"
    result = subprocess.run(
        [str(interp), "-m", "pip", "install", "--no-user", str(built_artifacts["wheel"])],
        env=env,
        capture_output=True,
        text=True,
    )
    if result.returncode != 0:
        _provisioning_failure(
            f"Failed to install built wheel into venv (exit {result.returncode}):\n"
            f"{result.stderr[-2000:]}"
        )
        raise RuntimeError("unreachable")  # pragma: no cover

    return {"venv_dir": venv_dir, "bin_dir": bin_dir, "python": interp, "env": env}


def _console_script_path(installed_venv) -> Path:
    script_name = "model-checker.exe" if os.name == "nt" else "model-checker"
    return installed_venv["bin_dir"] / script_name


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
