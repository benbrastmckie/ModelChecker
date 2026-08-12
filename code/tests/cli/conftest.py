"""Shared fixtures for `code/tests/cli/` -- the ParseFileFlags unit tests and the flag matrix.

All CLI invocations in this directory go through `python -m model_checker` (never the installed
console script -- that lives in `code/tests/packaging/`), so no venv is built here.
"""

from __future__ import annotations

from pathlib import Path
from typing import Callable

import pytest

# Minimal, deliberately tiny valid example module: one theory, one example, N=2. Modeled on the
# module format used by code/tests/e2e/test_batch_output_real.py. Kept minimal so every flag
# matrix invocation stays fast even though it forks a real Z3 solve.
_TINY_EXAMPLE_CONTENT = '''"""Minimal example module for CLI flag-matrix testing."""

from model_checker.theory_lib import bimodal

theory = bimodal.get_theory()
semantic_theories = {"cli_test": theory}

example_range = {
    "CLI_TEST": [
        [],        # premises
        ["A"],     # conclusions
        {"N": 2},  # settings
    ]
}
'''


@pytest.fixture
def tiny_example_file(tmp_path: Path) -> Path:
    """Write the minimal valid example module to tmp_path and return its path."""
    example_path = tmp_path / "cli_tiny_example.py"
    example_path.write_text(_TINY_EXAMPLE_CONTENT)
    return example_path


@pytest.fixture
def tiny_example_content() -> str:
    """Expose the raw module source, for tests that need to write variants of it."""
    return _TINY_EXAMPLE_CONTENT


@pytest.fixture
def run_cli() -> Callable[..., object]:
    """Expose tests/utils/helpers.run_cli_command as a fixture for this directory.

    A thin fixture wrapper (rather than a bare module import in every test file) so tests here
    read consistently with the rest of the CLI suite's fixture-based style.
    """
    from tests.utils.helpers import run_cli_command

    return run_cli_command
