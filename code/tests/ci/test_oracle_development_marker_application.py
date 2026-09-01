"""The oracle tree's `development` blanket, and the soundness core it deliberately exempts.

Companion to `test_development_marker_application.py`, which guards the same marker's
application to the in-package bimodal theory tree (`src/model_checker/theory_lib/bimodal/tests`).
This file guards the *second* blanket: `oracle/bimodal_logic/tests`, the standalone
cross-oracle differential harness.

Why a second blanket exists
---------------------------
The oracle tree is bimodal, entirely -- all of its test files live under
`oracle/bimodal_logic/tests` and there is nothing else in `oracle/`. It is a separately
implemented Z3 encoding used to differentially validate the in-package bimodal semantics. While
bimodal is under active construction, its completeness claims are expected to fail and are
tracked rather than gated, exactly as `development` is defined for in `code/pyproject.toml`.

What is emphatically NOT quarantined
------------------------------------
The soundness core (`_SOUNDNESS_CORE_CLASSES` below) stays gating. These are the six classes
`.github/workflows/differential-tests.yml`'s "Run CI gate tests explicitly" step names by node
id -- a step whose unconditional-gating property is separately enforced by
`test_unstable_deselection_wiring.py::TestOracleSoundnessGateStaysUnconditionallyGating`. They
fail only on a real semantic disagreement between the code/-tree implementation and the
reference oracle, never on a timeout or an unresolved formula. A theory being incomplete is a
reason to stop gating on *completeness*; it is not a reason to stop checking whether the theory
is *wrong*.

This split is the whole point: `development` here means "we do not yet require this to pass",
never "we have stopped looking".

Exit path
---------
Delete the hook in `oracle/conftest.py` when bimodal is no longer in development. The marker
registration and gating wiring are shared infrastructure and need no change.
"""

from __future__ import annotations

import os
import subprocess
import sys
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parents[3]
CODE_SRC = REPO_ROOT / "code" / "src"

ORACLE_TESTS = "oracle/bimodal_logic/tests"
DIFFERENTIAL_MODULE = f"{ORACLE_TESTS}/test_cross_oracle_differential.py"

# Every assertion in this file shells out to `pytest --collect-only ... oracle` rooted at the
# repo root, so the oracle tree has to actually be on disk. Same sandbox gap, and same remedy,
# as test_unstable_deselection_wiring.py's `_MISSING_REPO_ROOT_FILES` guard: `nix flake check`'s
# checks.default sets `src = ./code`, which excludes the repo root and therefore `oracle/`
# entirely, so `pytest oracle` there exits 4 ("file or directory not found") and every test in
# this module fails on a sandbox-layout artifact rather than on a marker defect. Without this
# guard the module reported 12 failures under `nix flake check` while passing in
# .github/workflows/tests.yml, whose actions/checkout@v4 provides the full repository.
_ORACLE_TREE = REPO_ROOT / ORACLE_TESTS
if not _ORACLE_TREE.is_dir():
    pytest.skip(
        f"Oracle tree not present in this sandbox ({_ORACLE_TREE}) -- expected under "
        "`nix flake check`'s checks.default, whose `src = ./code` excludes the repo root. "
        "This guard runs in .github/workflows/tests.yml's general-tests job instead, where "
        "actions/checkout@v4 provides the full repository.",
        allow_module_level=True,
    )

# pytest renders node ids relative to the resolved rootdir, which is not stable across the
# invocation shapes below: a single-root `pytest oracle` yields `oracle/bimodal_logic/tests/...`,
# while a mixed-root `pytest oracle code/tests/ci` shifts rootdir and yields the same items as
# `bimodal_logic/tests/...`. Both are accepted. `bimodal_logic/` exists nowhere but under
# `oracle/`, so the shorter prefix cannot match anything outside the oracle tree and the
# containment assertion stays meaningful under either rendering.
_ORACLE_NODEID_PREFIXES = (ORACLE_TESTS, "bimodal_logic/tests")


def _in_oracle_tree(nodeid: str) -> bool:
    return nodeid.startswith(_ORACLE_NODEID_PREFIXES)

# The six classes `.github/workflows/differential-tests.yml`'s gate step selects by node id.
# Kept as an explicit list rather than derived, so that adding a class to that workflow step
# without adding it here (or vice versa) is a visible edit rather than a silent divergence.
_SOUNDNESS_CORE_CLASSES = (
    "TestCIGate",
    "TestFormulaEnumerator",
    "TestDifferentialInfrastructure",
    "TestKnownFormulaBaseline",
    "TestDifferentialComparison",
    "TestDifferentialReport",
)

# The gating `-m` expression both passes of `oracle/run-oracle-suite.sh` carry. Restated here so
# this guard tests the real deselection semantics, not a paraphrase of them.
GATING_EXPR = "not xdist_serial and not slow and not unstable and not development"


def _collect(*args: str) -> list[str]:
    """Return collected node ids from `pytest --collect-only -q <args>`, rooted at the repo root.

    Rooted at the repo root rather than `code/` (the sibling helper in
    `test_development_marker_application.py` uses `code/`) because the oracle tree lives at
    `oracle/`, outside `code/`, and is reachable only from the repo root.

    `-o addopts=--import-mode=importlib` replaces `code/pyproject.toml`'s own `addopts` for the
    subprocess, for the same reason the sibling helper in
    `test_development_marker_application.py` does it: that value's `-v` and this call's `-q`
    cancel each other out (both adjust the same verbosity counter), leaving `--collect-only` at
    default verbosity -- which prints an indented `<Function ...>` tree carrying no `::` at all,
    so every assertion below would silently see an empty list. Single-root `oracle` collection
    does not hit this (rootdir stays outside `code/`, so those `addopts` never apply), which is
    exactly why only the mixed-root assertion exposed it.

    `oracle/` is on PYTHONPATH alongside `code/src`. A single-root `pytest oracle` invocation
    gets `oracle/` onto `sys.path` implicitly (rootdir insertion for its non-package test dirs),
    but a mixed-root collection shifts rootdir to `code/` and drops it, so
    `test_probe_solve_cost.py`'s `from probe_solve_cost import ...` fails to import and
    collection aborts. That is a pre-existing property of this repository's layout, reproducible
    with the `development` blanket removed entirely; setting the path here makes the mixed-root
    assertion below testable rather than papering over a defect introduced by it.

    Exit code 5 ("no tests collected") is legitimate for the deselect-everything invocations
    below and is not treated as a failure. Any other non-zero code means collection itself
    broke, which would make these assertions vacuous.
    """
    env = os.environ.copy()
    env["PYTHONPATH"] = os.pathsep.join([str(CODE_SRC), str(REPO_ROOT / "oracle")])
    completed = subprocess.run(
        [
            sys.executable, "-m", "pytest",
            "-o", "addopts=--import-mode=importlib",
            "--collect-only", "-q", *args,
        ],
        cwd=REPO_ROOT,
        env=env,
        capture_output=True,
        text=True,
    )
    if completed.returncode not in (0, 5):
        pytest.fail(
            f"pytest --collect-only failed (exit {completed.returncode}) for args {args!r}\n"
            f"--- stdout ---\n{completed.stdout}\n--- stderr ---\n{completed.stderr}"
        )
    return [line.strip() for line in completed.stdout.splitlines() if "::" in line]


def _is_soundness_core(nodeid: str) -> bool:
    """Same dual-rendering tolerance as `_in_oracle_tree` above."""
    module_ok = nodeid.startswith(DIFFERENTIAL_MODULE) or nodeid.startswith(
        "bimodal_logic/tests/test_cross_oracle_differential.py"
    )
    return module_ok and any(
        f"::{cls}::" in nodeid or nodeid.endswith(f"::{cls}")
        for cls in _SOUNDNESS_CORE_CLASSES
    )


class TestOracleTreeClaimsDevelopment:
    """Everything in the oracle tree except the soundness core carries `development`."""

    def test_oracle_tree_has_development_marked_tests(self):
        marked = _collect("-m", "development", "oracle")
        assert marked, (
            "no test in the oracle tree carries the `development` marker -- the blanket in "
            "oracle/conftest.py is not being applied, so the whole cross-oracle harness is "
            "still gating on bimodal completeness while bimodal is under construction"
        )

    def test_every_non_core_oracle_test_is_development_marked(self):
        everything = set(_collect("oracle"))
        marked = set(_collect("-m", "development", "oracle"))
        unmarked_non_core = sorted(
            nodeid for nodeid in everything - marked if not _is_soundness_core(nodeid)
        )
        assert unmarked_non_core == [], (
            f"{len(unmarked_non_core)} oracle test(s) outside the soundness core are missing "
            f"the `development` marker, so they still gate release runs on bimodal "
            f"completeness: {unmarked_non_core[:10]}"
        )

    def test_gating_expression_deselects_the_non_core_oracle_tree(self):
        """The property that actually takes the harness off the gate."""
        gating = set(_collect("-m", GATING_EXPR, "oracle"))
        leaked = sorted(nodeid for nodeid in gating if not _is_soundness_core(nodeid))
        assert leaked == [], (
            f"{len(leaked)} non-core oracle test(s) survive the gating `-m` expression and "
            f"would still run in oracle/run-oracle-suite.sh: {leaked[:10]}"
        )

    def test_oracle_tree_is_still_runnable_on_explicit_opt_in(self):
        """Quarantined, not hidden: `-m development` must still reach the harness."""
        assert _collect("-m", "development", "oracle"), (
            "`-m development` collects nothing under oracle/, so the quarantined harness has "
            "become unrunnable rather than merely non-gating"
        )


class TestSoundnessCoreStaysGating:
    """The differential/soundness core is exempt from the blanket and still gates."""

    @pytest.mark.parametrize("cls", _SOUNDNESS_CORE_CLASSES)
    def test_core_class_is_not_development_marked(self, cls):
        marked = _collect("-m", "development", f"{DIFFERENTIAL_MODULE}::{cls}")
        assert marked == [], (
            f"{cls} carries the `development` marker. This class is part of the soundness core "
            f"named by .github/workflows/differential-tests.yml's gate step; quarantining it "
            f"would stop checking whether bimodal is *wrong*, not merely incomplete. "
            f"Offenders: {marked[:10]}"
        )

    def test_soundness_core_survives_the_gating_expression(self):
        gating = _collect("-m", GATING_EXPR, DIFFERENTIAL_MODULE)
        core = [nodeid for nodeid in gating if _is_soundness_core(nodeid)]
        assert core, (
            "the gating `-m` expression collects none of the soundness core -- the blanket has "
            "swallowed the one part of the oracle tree that must stay gating"
        )


class TestOracleBlanketIsContained:
    """The oracle blanket must not leak onto anything outside the oracle tree."""

    def test_no_leakage_outside_oracle_in_a_mixed_root_collection(self):
        """The case a single-root collection cannot see.

        `pytest_collection_modifyitems` is handed the entire session's item list once its
        conftest has been loaded -- it is not scoped to that conftest's directory by pytest. An
        unfiltered loop in oracle/conftest.py would mark every test in a run that collects
        oracle *and* something else, silently dropping the in-package suite from every gating
        run. Mirrors the equivalent assertion in test_development_marker_application.py.
        """
        marked = _collect("-m", "development", "oracle", "code/tests/ci")
        outside = sorted(
            nodeid for nodeid in marked if not _in_oracle_tree(nodeid)
        )
        assert not outside, (
            f"{len(outside)} test(s) outside the oracle tree acquired `development` in a "
            f"mixed-root collection -- oracle/conftest.py's hook is marking items it does not "
            f"own. First offenders: {outside[:10]}"
        )
        assert marked, (
            "the mixed-root collection found no development-marked tests at all, so this "
            "assertion proved nothing -- oracle/conftest.py's hook did not run"
        )
