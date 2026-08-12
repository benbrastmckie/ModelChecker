"""Console-script *behavioral* coverage for the packaging contract.

This file owns broader console-script behavior coverage beyond `test_entry_point.py`'s
declare-install-run liveness check: real `--version`/`--help` cross-checked against the
equivalent `python -m model_checker` invocation (both run inside the same installed venv, so the
comparison is apples-to-apples), a real example run through the installed script, and an
explicit no-`PYTHONPATH` invocation proving the installed package is self-sufficient.

Consumes the `installed_venv` fixture and `_console_script_path` helper from `conftest.py`
(shared across `tests/packaging/`, not duplicated here) -- no second venv is built.
"""

from __future__ import annotations

import subprocess

import pytest

from .conftest import _console_script_path, handle_known_venv_libz3_link_failure

pytestmark = [pytest.mark.packaging, pytest.mark.slow]


_TINY_EXAMPLE_CONTENT = '''"""Minimal example module for console-script behavioral testing."""

from model_checker.theory_lib import bimodal

theory = bimodal.get_theory()
semantic_theories = {"console_script_test": theory}

example_range = {
    "CONSOLE_SCRIPT_TEST": [
        [],
        ["A"],
        {"N": 2},
    ]
}
'''


def test_version_matches_python_dash_m_invocation(installed_venv):
    """The console script and `python -m model_checker` resolve to the same run() -- proven by
    cross-checking their --version output inside the same installed venv, not merely that each
    exits 0 independently."""
    script_path = _console_script_path(installed_venv)

    script_result = subprocess.run(
        [str(script_path), "--version"],
        env=installed_venv["env"],
        capture_output=True,
        text=True,
    )
    module_result = subprocess.run(
        [str(installed_venv["python"]), "-m", "model_checker", "--version"],
        env=installed_venv["env"],
        capture_output=True,
        text=True,
    )

    assert script_result.returncode == 0
    assert module_result.returncode == 0
    assert script_result.stdout == module_result.stdout, (
        "console script and `python -m model_checker` --version output diverged: "
        f"{script_result.stdout!r} != {module_result.stdout!r}"
    )


def test_help_matches_python_dash_m_invocation(installed_venv):
    """Same cross-check as --version, for --help."""
    script_path = _console_script_path(installed_venv)

    script_result = subprocess.run(
        [str(script_path), "--help"],
        env=installed_venv["env"],
        capture_output=True,
        text=True,
    )
    module_result = subprocess.run(
        [str(installed_venv["python"]), "-m", "model_checker", "--help"],
        env=installed_venv["env"],
        capture_output=True,
        text=True,
    )

    assert script_result.returncode == 0
    assert module_result.returncode == 0
    assert script_result.stdout == module_result.stdout, (
        "console script and `python -m model_checker` --help output diverged"
    )


def test_real_example_run_through_console_script(installed_venv, tmp_path):
    """Runs a real example file through the installed console script (no `python -m`
    indirection) and confirms it produces real model-checking output."""
    example_file = tmp_path / "console_example.py"
    example_file.write_text(_TINY_EXAMPLE_CONTENT)

    script_path = _console_script_path(installed_venv)
    result = subprocess.run(
        [str(script_path), str(example_file)],
        env=installed_venv["env"],
        capture_output=True,
        text=True,
    )
    handle_known_venv_libz3_link_failure(result)

    assert result.returncode == 0, (
        f"console script exited {result.returncode}:\n"
        f"STDOUT:\n{result.stdout}\nSTDERR:\n{result.stderr}"
    )
    assert 'Traceback' not in result.stderr
    assert result.stdout.strip(), "console script produced no stdout"
    assert 'EXAMPLE' in result.stdout


def test_console_script_runs_without_pythonpath(installed_venv, tmp_path):
    """`installed_venv["env"]` already has PYTHONPATH stripped (see conftest.py's fixture
    docstring); this test makes that guarantee an explicit, checked assertion rather than an
    implicit side effect of fixture setup, proving the installed package resolves
    `model_checker` from its own site-packages with no source-tree PYTHONPATH assistance -- the
    property the retired mock-based subprocess test in
    `builder/tests/test_package_loading.py` only ever pretended to check.
    """
    assert 'PYTHONPATH' not in installed_venv["env"]

    example_file = tmp_path / "no_pythonpath_example.py"
    example_file.write_text(_TINY_EXAMPLE_CONTENT)

    script_path = _console_script_path(installed_venv)
    result = subprocess.run(
        [str(script_path), str(example_file)],
        env=installed_venv["env"],
        capture_output=True,
        text=True,
    )
    handle_known_venv_libz3_link_failure(result)

    assert result.returncode == 0
    assert 'Traceback' not in result.stderr
    assert 'ModuleNotFoundError' not in result.stderr
