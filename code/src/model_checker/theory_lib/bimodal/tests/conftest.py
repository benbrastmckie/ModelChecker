"""Pytest configuration and fixtures for bimodal theory tests.

This module provides common test fixtures and configuration for both
example tests and unit tests, matching the conftest.py layout used by the
exclusion and logos theories.

It additionally applies the `development` marker to this theory's whole test tree; see
`pytest_collection_modifyitems` below and `code/docs/core/TESTING_GUIDE.md` section 8.14.
"""

import pathlib

import pytest
from model_checker.theory_lib import bimodal

# This conftest's own directory: the bimodal test tree. Used to scope the `development` marker
# application below to items actually collected from here.
_BIMODAL_TESTS_DIR = pathlib.Path(__file__).parent.resolve()


def pytest_collection_modifyitems(config, items):
    """Apply `development` to every test collected from the bimodal test tree.

    The bimodal theory is under active construction and is deliberately not part of what a
    release run requires to pass. All ten release-gating pytest invocations already carry
    `and not development` in their `-m` expression (enforced by
    `code/tests/ci/test_unstable_deselection_wiring.py`), so claiming the marker here is what
    actually takes bimodal off the gate -- the marker had been registered, wired, and documented
    without any test claiming it.

    **This is a theory-level blanket, which TESTING_GUIDE.md section 8.14 otherwise forbids.**
    It is an explicitly recorded exception, authorized on the grounds that the *whole* theory --
    not a list of individually-incomplete behaviours -- is in development. Section 8.14 records
    the exception, the risk it accepts (a bimodal test that regresses from passing to failing no
    longer turns a gating run red), and the exit path. Two containment properties keep the blast
    radius pinned:

    - Scope is enforced by the explicit path check below, NOT by this file's location. A
      `pytest_collection_modifyitems` implementation in any conftest is handed the *entire*
      session's item list once that conftest has been loaded, so an unfiltered loop here would
      mark every test in the repository as soon as a run touched bimodal at all -- which is
      exactly the shape of the gating drivers' own `pytest tests src/model_checker` invocation.
      `code/tests/ci/test_development_marker_application.py` asserts both halves (complete
      coverage of bimodal, zero leakage outside it) including that mixed-root case.
    - The differential/soundness harness stays fully gating. Bimodal's soundness and
      cross-oracle differential tests live in `oracle/bimodal_logic/tests/`, not here, and
      `development` is deliberately unregistered in `oracle/conftest.py` -- so no soundness
      claim about bimodal can be quarantined by this hook.

    Bimodal remains runnable on demand with `-m development` (see `tests/README.md`); the marker
    quarantines the theory from gating runs without hiding or skipping it.

    **Exit path:** delete this hook when bimodal is no longer in development. Nothing else needs
    to change -- the marker registration and gating wiring are shared infrastructure.
    """
    marker = pytest.mark.development
    for item in items:
        item_path = pathlib.Path(str(item.path)).resolve()
        if _BIMODAL_TESTS_DIR == item_path or _BIMODAL_TESTS_DIR in item_path.parents:
            item.add_marker(marker)


@pytest.fixture
def bimodal_theory():
    """Standard bimodal theory configuration (semantics, proposition, model, operators)."""
    return bimodal.get_theory()


@pytest.fixture
def basic_settings():
    """Standard settings for most tests: the certificate encoding's own segment lengths
    (`back`/`mid`/`fwd`) in place of the retired `N`/`M`/`contingent`/`disjoint` (D4)."""
    return {
        'back': 2,
        'mid': 1,
        'fwd': 2,
        'max_time': 1,
        'expectation': True,
        'iterate': 1,
    }


@pytest.fixture
def minimal_settings():
    """Minimal settings for quick tests: the smallest legal segment lengths
    (`WitnessRegistry.__init__` requires `back >= 1`, `fwd >= 1`; `mid` may be `0`)."""
    return {
        'back': 1,
        'mid': 0,
        'fwd': 1,
        'max_time': 1,
        'expectation': True,
    }


@pytest.fixture
def complex_settings():
    """Settings for more complex tests: larger segment lengths than `basic_settings`."""
    return {
        'back': 3,
        'mid': 2,
        'fwd': 4,
        'max_time': 5,
        'expectation': True,
    }


@pytest.fixture
def witness_registry(basic_settings):
    """Fresh witness registry for tests, over an empty closure (callers needing specific
    closure members should construct their own `WitnessRegistry` directly, matching
    `test_witness_registry.py`'s own convention)."""
    from model_checker.theory_lib.bimodal.semantic.witness_registry import WitnessRegistry
    return WitnessRegistry(
        back=basic_settings['back'],
        mid=basic_settings['mid'],
        fwd=basic_settings['fwd'],
        closure=(),
    )


@pytest.fixture
def constraint_generator(witness_registry):
    """Constraint generator built directly against a `WitnessRegistry` -- the rewritten
    `WitnessConstraintGenerator.__init__(self, registry)` signature (Phase 7), not a
    `BimodalSemantics` instance (the retired encoding's own constructor argument)."""
    from model_checker.theory_lib.bimodal.semantic.witness_constraints import WitnessConstraintGenerator
    return WitnessConstraintGenerator(witness_registry)
