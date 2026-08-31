"""Executable contract for `code/run_tests.py`'s `--markers`/`-m` passthrough (GAP 2 from
`specs/177_bimodal_in_development_status_and_ci_non_gating/reports/
01_bimodal-ci-gating-ground-truth.md` -- see `code/docs/core/TESTING_GUIDE.md` section 8.14).

Before this module existed, no test file for `run_tests.py` existed anywhere in the tree, and
`TestConfig.markers` was a dead field: declared on the dataclass and populated via
`getattr(args, 'markers', [])`, but no argparse option named `markers` was ever registered, so
the value was always the `[]` default. This meant the unified runner could not reproduce the
gating drivers' `-m` selection, nor explicitly select the in-development (`development`-marked)
set, without dropping to raw `pytest` invocations.

This module asserts, in order:

1. The parser accepts `--markers "<expr>"` and its `-m` short form, and `TestConfig.markers`
   receives the value via `TestConfig.from_args`.
2. Every one of the five pytest-command-building sites in `run_tests.py` appends `-m <expr>` to
   its built command when `config.markers` is supplied.
3. Every one of those same five sites appends NO `-m` token at all when `config.markers` is not
   supplied -- the regression guard on "stays runnable and failing by default" (criterion (b)):
   a bare `./run_tests.py bimodal` must keep running the full, unfiltered bimodal suite.
4. `--markers` has no default value: a bare invocation leaves `config.markers` falsy.
5. Pytest exits 5 ("no tests ran") when an `-m` expression collects tests but deselects all of
   them -- observed directly: `pytest bimodal/tests -k example -m "not development"` reports
   "313 deselected" and exits 5, since every bimodal test carries `development`. When the
   caller explicitly supplied `--markers`, that is the intended selection outcome (e.g.
   reproducing the gate finds zero in-scope tests), not a failure, so each execution site
   normalizes a markers-caused exit 5 to 0. Exit 5 is left unmodified when no markers were
   supplied, since it then signals a genuine collection problem.

`run_tests.py` is a script, not a package module (no `__init__.py` chain makes it importable by
name), so it is loaded by absolute path via `importlib.util`, following the established in-repo
pattern in `code/tests/ci/test_unstable_watch_classifier.py::_load_classifier`.

The four `_run_*`/`_build_pytest_command` sites that shell out via `subprocess.run` are exercised
against real, already-existing test directories in this repository (no tmp-dir fixtures needed --
`logos/subtheories/modal/tests`, `bimodal/tests`, `logos/tests` all exist today) with
`subprocess.run` monkeypatched to a command-capturing stub, so no real pytest subprocess is ever
spawned by this module.

**Patching `subprocess.run` safely.** `run_tests.py` does a plain `import subprocess`, so
`run_tests_mod.subprocess` is the SAME global `subprocess` module object every other test module
in this session also imports -- it is not a private copy. Every test below therefore patches it
via pytest's `monkeypatch` fixture (`monkeypatch.setattr(run_tests_mod.subprocess, "run", ...)`),
never by hand-assigning `run_tests_mod.subprocess.run = ...` and restoring it in a `finally`
block: a hand-rolled restore that re-reads `subprocess.run` *after* already overwriting it
captures the stand-in, not the original, and leaves the real global `subprocess.run` permanently
patched for the rest of the pytest session -- exactly the kind of cross-test corruption
`monkeypatch`'s guaranteed teardown exists to prevent.
"""

from __future__ import annotations

import importlib.util
import types
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parents[3]
RUN_TESTS_PY = REPO_ROOT / "code" / "run_tests.py"
CODE_DIR = REPO_ROOT / "code"


def _load_run_tests():
    """Load `code/run_tests.py` by absolute path. `if __name__ == "__main__":` guards `main()`,
    so importing it has no side effects."""
    spec = importlib.util.spec_from_file_location("run_tests_under_test", RUN_TESTS_PY)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


run_tests_mod = _load_run_tests()

MARKER_EXPR = "not development"


def _base_config(module, **overrides):
    """A minimal, valid TestConfig for direct command-building calls (bypasses argparse/
    TestConfig.from_args, which is exercised separately below)."""
    fields = dict(
        theories=[],
        subtheories={},
        components=[],
        run_examples=True,
        run_unit=True,
        run_package=True,
        verbose=False,
        failfast=False,
        coverage=False,
        markers=None,
        pytest_args=[],
    )
    fields.update(overrides)
    return module.TestConfig(**fields)


class _CapturingRun:
    """Stand-in for `subprocess.run` that records the command list and reports success,
    without spawning a real pytest subprocess."""

    def __init__(self):
        self.calls = []

    def __call__(self, command, cwd=None, env=None):
        self.calls.append(list(command))
        return types.SimpleNamespace(returncode=0)


class TestMarkersArgparsePassthrough:
    """Assertion group 1 and 4: the parser accepts `--markers`/`-m` with no default, and
    `TestConfig.from_args` threads the value through."""

    def test_long_form_accepted(self):
        parser = run_tests_mod.create_argument_parser()
        args = parser.parse_args(["--markers", MARKER_EXPR])
        assert args.markers == MARKER_EXPR

    def test_short_form_accepted(self):
        parser = run_tests_mod.create_argument_parser()
        args = parser.parse_args(["-m", MARKER_EXPR])
        assert args.markers == MARKER_EXPR

    def test_has_no_default_value(self):
        parser = run_tests_mod.create_argument_parser()
        args = parser.parse_args([])
        assert not args.markers, f"expected a falsy default for --markers, got {args.markers!r}"

    def test_test_config_from_args_receives_the_value(self):
        parser = run_tests_mod.create_argument_parser()
        args = parser.parse_args(["--markers", MARKER_EXPR])
        runner = run_tests_mod.TestRunner()
        config = run_tests_mod.TestConfig.from_args(args, runner)
        assert config.markers == MARKER_EXPR

    def test_test_config_from_args_bare_invocation_leaves_markers_falsy(self):
        """Regression guard for criterion (b): with no --markers, config.markers must be falsy
        so no command-building site appends an unwanted -m token."""
        parser = run_tests_mod.create_argument_parser()
        args = parser.parse_args([])
        runner = run_tests_mod.TestRunner()
        config = run_tests_mod.TestConfig.from_args(args, runner)
        assert not config.markers, (
            f"expected config.markers to be falsy on a bare invocation, got {config.markers!r}"
        )


class TestMarkersThreadedIntoEveryCommandBuildingSite:
    """Assertion groups 2 and 3: every one of the five identified command-building sites
    appends `-m <expr>` when markers are supplied, and appends no `-m` token at all when they
    are not."""

    def test_logos_example_tests_site(self, monkeypatch):
        runner = run_tests_mod.ExampleTestRunner(CODE_DIR)
        capture = _CapturingRun()
        monkeypatch.setattr(run_tests_mod.subprocess, "run", capture)

        with_markers = _base_config(run_tests_mod, markers=MARKER_EXPR)
        runner._run_logos_example_tests(["modal"], with_markers)
        without_markers = _base_config(run_tests_mod, markers=None)
        runner._run_logos_example_tests(["modal"], without_markers)

        assert len(capture.calls) == 2
        with_cmd, without_cmd = capture.calls
        assert "-m" in with_cmd, f"expected -m in {with_cmd!r} when markers supplied"
        assert with_cmd[with_cmd.index("-m") + 1] == MARKER_EXPR
        assert "-m" not in without_cmd, f"expected no -m token in {without_cmd!r}"

    def test_standard_example_tests_site(self, monkeypatch):
        runner = run_tests_mod.ExampleTestRunner(CODE_DIR)
        capture = _CapturingRun()
        monkeypatch.setattr(run_tests_mod.subprocess, "run", capture)

        with_markers = _base_config(run_tests_mod, markers=MARKER_EXPR)
        runner._run_standard_example_tests("bimodal", with_markers)
        without_markers = _base_config(run_tests_mod, markers=None)
        runner._run_standard_example_tests("bimodal", without_markers)

        assert len(capture.calls) == 2
        with_cmd, without_cmd = capture.calls
        assert "-m" in with_cmd, f"expected -m in {with_cmd!r} when markers supplied"
        assert with_cmd[with_cmd.index("-m") + 1] == MARKER_EXPR
        assert "-m" not in without_cmd, f"expected no -m token in {without_cmd!r}"

    def test_logos_unit_tests_site(self, monkeypatch):
        runner = run_tests_mod.UnitTestRunner(CODE_DIR)
        capture = _CapturingRun()
        monkeypatch.setattr(run_tests_mod.subprocess, "run", capture)

        with_markers = _base_config(run_tests_mod, markers=MARKER_EXPR)
        runner._run_logos_unit_tests([], with_markers)
        without_markers = _base_config(run_tests_mod, markers=None)
        runner._run_logos_unit_tests([], without_markers)

        assert len(capture.calls) == 2
        with_cmd, without_cmd = capture.calls
        assert "-m" in with_cmd, f"expected -m in {with_cmd!r} when markers supplied"
        assert with_cmd[with_cmd.index("-m") + 1] == MARKER_EXPR
        assert "-m" not in without_cmd, f"expected no -m token in {without_cmd!r}"

    def test_standard_unit_tests_site(self, monkeypatch):
        runner = run_tests_mod.UnitTestRunner(CODE_DIR)
        capture = _CapturingRun()
        monkeypatch.setattr(run_tests_mod.subprocess, "run", capture)

        with_markers = _base_config(run_tests_mod, markers=MARKER_EXPR)
        runner._run_standard_unit_tests("bimodal", with_markers)
        without_markers = _base_config(run_tests_mod, markers=None)
        runner._run_standard_unit_tests("bimodal", without_markers)

        assert len(capture.calls) == 2
        with_cmd, without_cmd = capture.calls
        assert "-m" in with_cmd, f"expected -m in {with_cmd!r} when markers supplied"
        assert with_cmd[with_cmd.index("-m") + 1] == MARKER_EXPR
        assert "-m" not in without_cmd, f"expected no -m token in {without_cmd!r}"

    def test_build_pytest_command_site(self):
        """PackageTestRunner._build_pytest_command returns the command list directly -- no
        subprocess monkeypatching needed for this site."""
        runner = run_tests_mod.PackageTestRunner(CODE_DIR)
        test_dir = CODE_DIR / "src" / "model_checker" / "iterate" / "tests"
        assert test_dir.exists(), f"expected {test_dir} to exist for this assertion to be real"

        with_markers = _base_config(run_tests_mod, markers=MARKER_EXPR)
        with_cmd = runner._build_pytest_command(test_dir, with_markers)
        assert "-m" in with_cmd, f"expected -m in {with_cmd!r} when markers supplied"
        assert with_cmd[with_cmd.index("-m") + 1] == MARKER_EXPR

        without_markers = _base_config(run_tests_mod, markers=None)
        without_cmd = runner._build_pytest_command(test_dir, without_markers)
        assert "-m" not in without_cmd, f"expected no -m token in {without_cmd!r}"


class _ReturnCode5Run:
    """Stand-in for `subprocess.run` that always reports pytest's exit 5 ("no tests ran"),
    regardless of the command it was given."""

    def __call__(self, command, cwd=None, env=None):
        return types.SimpleNamespace(returncode=5)


class TestExitCodeFiveNormalizedOnlyWhenMarkersSupplied:
    """Assertion group 5: a markers-caused exit 5 (full deselection) is normalized to 0 at
    every subprocess-executing site; an exit 5 with no markers supplied is left as a genuine
    failure signal."""

    def test_logos_example_tests_site(self, monkeypatch):
        runner = run_tests_mod.ExampleTestRunner(CODE_DIR)
        monkeypatch.setattr(run_tests_mod.subprocess, "run", _ReturnCode5Run())

        with_markers = _base_config(run_tests_mod, markers=MARKER_EXPR)
        assert runner._run_logos_example_tests(["modal"], with_markers) == 0
        without_markers = _base_config(run_tests_mod, markers=None)
        assert runner._run_logos_example_tests(["modal"], without_markers) == 5

    def test_standard_example_tests_site(self, monkeypatch):
        runner = run_tests_mod.ExampleTestRunner(CODE_DIR)
        monkeypatch.setattr(run_tests_mod.subprocess, "run", _ReturnCode5Run())

        with_markers = _base_config(run_tests_mod, markers=MARKER_EXPR)
        assert runner._run_standard_example_tests("bimodal", with_markers) == 0
        without_markers = _base_config(run_tests_mod, markers=None)
        assert runner._run_standard_example_tests("bimodal", without_markers) == 5

    def test_logos_unit_tests_site(self, monkeypatch):
        runner = run_tests_mod.UnitTestRunner(CODE_DIR)
        monkeypatch.setattr(run_tests_mod.subprocess, "run", _ReturnCode5Run())

        with_markers = _base_config(run_tests_mod, markers=MARKER_EXPR)
        assert runner._run_logos_unit_tests([], with_markers) == 0
        without_markers = _base_config(run_tests_mod, markers=None)
        assert runner._run_logos_unit_tests([], without_markers) == 5

    def test_standard_unit_tests_site(self, monkeypatch):
        runner = run_tests_mod.UnitTestRunner(CODE_DIR)
        monkeypatch.setattr(run_tests_mod.subprocess, "run", _ReturnCode5Run())

        with_markers = _base_config(run_tests_mod, markers=MARKER_EXPR)
        assert runner._run_standard_unit_tests("bimodal", with_markers) == 0
        without_markers = _base_config(run_tests_mod, markers=None)
        assert runner._run_standard_unit_tests("bimodal", without_markers) == 5

    def test_package_component_tests_site(self, monkeypatch):
        runner = run_tests_mod.PackageTestRunner(CODE_DIR)
        monkeypatch.setattr(run_tests_mod.subprocess, "run", _ReturnCode5Run())

        with_markers = _base_config(run_tests_mod, markers=MARKER_EXPR)
        assert runner.run_component_tests("iterate", with_markers) == 0
        without_markers = _base_config(run_tests_mod, markers=None)
        assert runner.run_component_tests("iterate", without_markers) == 5
