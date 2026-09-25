"""Pytest configuration and fixtures for bimodal theory tests.

This module provides common test fixtures and configuration for both
example tests and unit tests, matching the conftest.py layout used by the
exclusion and logos theories.

**No longer applies the `development` marker.** The witness-family certificate redesign (task
184) restored the speed and semantic-alignment properties the marker's quarantine was covering
for, so bimodal is a gating theory again -- see `code/docs/core/TESTING_GUIDE.md` section 8.14
for the marker's history and this retirement's record. This conftest previously carried a
`pytest_collection_modifyitems` hook that applied `development` to this whole test tree; that
hook is deleted, not merely disabled, per the hook's own documented exit path ("delete this hook
when bimodal is no longer in development. Nothing else needs to change -- the marker
registration and gating wiring are shared infrastructure").
"""

import pytest
from model_checker.theory_lib import bimodal


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
