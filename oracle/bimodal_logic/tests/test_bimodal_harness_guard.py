"""Regression tests preventing an unguarded ``bimodal_harness`` import from
crashing pytest collection.

``bimodal_harness`` is a developer-local, optional package (a sibling checkout
at ``/home/benjamin/Projects/BimodalHarness/src``) that is never installed in
CI. Any test module in this tree that imports it unconditionally at module
scope will crash pytest *collection* -- before ``-m unstable`` (or any other
marker) deselection has a chance to run -- on every machine and every CI
runner where that sibling checkout does not exist. This is exactly what
happened to ``unstable-watch.yml``'s oracle-tree step.

The required pattern for any test file that needs ``bimodal_harness`` is the
shared guard module ``oracle/bimodal_logic/tests/_bimodal_harness.py``: check
for the sibling checkout, attempt the import inside a ``try/except
ImportError``, and gate only the specific tests that need the guarded symbols
behind ``pytest.mark.skipif(not BH_AVAILABLE, ...)``. A bare, unguarded,
module-level ``from bimodal_harness...`` import anywhere in this directory is
the failure mode this file exists to catch.

Verification note: on the original author's machine, the sibling checkout
really exists, so collecting the whole ``oracle/bimodal_logic/tests/``
directory locally does *not* reproduce the CI crash -- an alphabetically
earlier guarded file's ``sys.path.insert`` leaks a working import path to a
later, unguarded file as an accidental side effect. A plain local run is
therefore not evidence of anything. The tests below instead launch a
*subprocess* that installs an explicit ``sys.meta_path`` finder raising
``ImportError`` for ``bimodal_harness`` (and any of its submodules) before
running pytest collection, faithfully simulating a CI runner where the
package genuinely does not exist -- regardless of what happens to be present
on this machine's ``sys.path``.
"""

from __future__ import annotations

import subprocess
import sys
from pathlib import Path

# Repository root: oracle/bimodal_logic/tests/ -> oracle/bimodal_logic/ -> oracle/ -> repo root
_REPO_ROOT = Path(__file__).resolve().parents[3]
_ORACLE_TESTS_DIR = _REPO_ROOT / "oracle" / "bimodal_logic" / "tests"
_ORACLE_INTERFACE_FILE = _ORACLE_TESTS_DIR / "test_oracle_interface.py"

# Installed in the *child* process only, ahead of any other import, so that
# `import bimodal_harness` (and any submodule import) fails exactly the way
# it would on a CI runner that never has the sibling checkout on disk. This
# must never be a `sys.modules` deletion or a `monkeypatch`: neither of those
# survives into pytest's own fresh module collection inside the child.
_BLOCKER_PREAMBLE = """
import sys

class _BlockBimodalHarness:
    def find_spec(self, name, path, target=None):
        if name == "bimodal_harness" or name.startswith("bimodal_harness."):
            raise ImportError(f"blocked by test harness: {name!r}")
        return None

sys.meta_path.insert(0, _BlockBimodalHarness())
"""


def _run_collect_under_blocker(target: str) -> subprocess.CompletedProcess:
    """Run `pytest --collect-only -q {target}` in a child process with
    `bimodal_harness` forcibly unimportable via a `sys.meta_path` blocker.

    `target` is passed relative to the repo root (matching how
    `unstable-watch.yml` invokes pytest from the repo root).
    """
    script = _BLOCKER_PREAMBLE + f"""
import pytest
raise SystemExit(pytest.main(["--collect-only", "-q", {target!r}]))
"""
    env = dict(**_child_env())
    return subprocess.run(
        [sys.executable, "-c", script],
        cwd=str(_REPO_ROOT),
        env=env,
        capture_output=True,
        text=True,
        timeout=120,
    )


def _child_env():
    import os

    env = dict(os.environ)
    env["PYTHONPATH"] = str(_REPO_ROOT / "code" / "src")
    return env


class TestOracleTreeCollectsUnderBlocker:
    """Directory-wide regression test: the exact scope `unstable-watch.yml`
    uses (`oracle/bimodal_logic/tests/`), collected with `bimodal_harness`
    forcibly unavailable."""

    def test_directory_collects_cleanly_without_bimodal_harness(self):
        result = _run_collect_under_blocker("oracle/bimodal_logic/tests/")
        combined = result.stdout + result.stderr
        assert "ModuleNotFoundError" not in combined, (
            "bimodal_harness leaked into collection output:\n" + combined
        )
        assert "ERROR collecting" not in combined, (
            "a collection error occurred:\n" + combined
        )
        # pytest exit code 0 (tests collected) or 5 (no tests collected) are
        # both acceptable here -- this test asserts collection safety, not
        # that any particular test exists or is selected.
        assert result.returncode in (0, 5), (
            f"unexpected exit code {result.returncode}:\n" + combined
        )


class TestOracleInterfaceCollectsUnderBlocker:
    """Narrower regression test isolating `test_oracle_interface.py` alone,
    so a future failure localizes immediately to this file rather than
    requiring a directory-wide bisection."""

    def test_file_collects_cleanly_without_bimodal_harness(self):
        result = _run_collect_under_blocker(
            "oracle/bimodal_logic/tests/test_oracle_interface.py"
        )
        combined = result.stdout + result.stderr
        assert "ModuleNotFoundError" not in combined, (
            "bimodal_harness leaked into collection output:\n" + combined
        )
        assert "ERROR collecting" not in combined, (
            "a collection error occurred:\n" + combined
        )
        assert result.returncode in (0, 5), (
            f"unexpected exit code {result.returncode}:\n" + combined
        )
