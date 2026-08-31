"""Shared fixtures for `code/tests/cli/` -- the ParseFileFlags unit tests and the flag matrix.

All CLI invocations in this directory go through `tests.utils.helpers.run_cli_command` (the
`run_cli` fixture below), which dispatches over `MODELCHECKER_CLI_TEST_MODE`
(`tests.utils.cli_mode.get_cli_test_mode`): `source` (default) invokes `python -m model_checker`
against the working tree, exactly as this module originally did unconditionally; `installed`
invokes the pip-installed `model-checker` console script; `installed-module` invokes
`python -m model_checker` against an installed package with no source-tree `PYTHONPATH`
injection. No venv is built by this directory itself -- `installed`/`installed-module` runs
expect one already active on `PATH`/the interpreter (see `code/tests/README.md`'s "CLI Invocation
Modes" section, or `code/scripts/verify-installed-cli.sh` for a containerized one). Console
script behavior specific to packaging concerns (build/install contract, not CLI dispatch) still
lives in `code/tests/packaging/`.
"""

from __future__ import annotations

from pathlib import Path
from typing import Callable

import pytest

# Minimal, deliberately tiny valid example module: one theory, one example, N=2. Modeled on the
# module format used by code/tests/e2e/test_batch_output_real.py. Kept minimal so every flag
# matrix invocation stays fast even though it forks a real Z3 solve.
#
# Uses logos rather than bimodal, for the same class of reason test_flag_matrix.py's
# _CVC5_COMPATIBLE_EXAMPLE already documents for its own switch. Two reasons here:
#
# 1. **Cost.** This example's bimodal solve takes ~4.2s and rising as bimodal's frame class is
#    filled in; the same example under logos takes ~0.001s. Every test below forks one or two
#    real CLI subprocesses, so the bimodal cost was multiplied across the whole directory.
#    Worse, bimodal's DEFAULT_EXAMPLE_SETTINGS max_time is 1s and this module set no explicit
#    budget, so the solve did not merely run slowly -- it timed out, found no model, and left
#    -p/-z/-i with nothing extra to print. `test_output_affecting_boolean_flag_changes_output`
#    was reduced to comparing two timeout messages that differ only in a "Solver Run Time:
#    1.000X seconds" float, passing or failing on microsecond jitter (it failed three ways under
#    `-n 4`). See TESTING_GUIDE.md section 8.6 on inheriting a theory's default max_time.
# 2. **Gating scope.** These are gating CLI-plumbing tests -- they assert that flags are
#    accepted, change output, and write files. Nothing about them is bimodal-specific. Pinning
#    them to the one theory that is under active construction and deliberately non-gating (see
#    TESTING_GUIDE.md section 8.14) coupled the CLI gate to that theory's solver cost, which is
#    exactly the coupling the `development` marker exists to remove.
_TINY_EXAMPLE_CONTENT = '''"""Minimal example module for CLI flag-matrix testing."""

from model_checker.theory_lib import logos

theory = logos.get_theory()
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
