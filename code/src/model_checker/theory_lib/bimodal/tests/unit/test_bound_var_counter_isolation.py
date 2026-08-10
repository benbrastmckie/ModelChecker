"""Regression tests for cross-test order dependence via the bimodal bound-variable counter.

Root cause (discovered while diagnosing order-dependent failures in
``test_bimodal.py::test_example_cases``): ``operators.py`` names every
quantifier-bound Z3 ``Int`` via a process-global ``itertools.count()``
(``_bound_var_counter``) to guarantee distinct names for the life of the
process -- see that module's docstring for why a plain counter (not
``z3.FreshInt``) is required. ``isolated_z3_context()`` swaps in a brand-new
Z3 ``Context`` for each example (and resets the similarly process-global
``AtomSort`` cache alongside it), but it did NOT reset this counter, so the
*numeric suffix* baked into each bound variable's name still depended on how
many prior examples (in the same process) had already called
``_fresh_bound_int``.

That leaked, run-order-dependent numeric suffix is enough to change Z3's
MBQI-driven quantifier instantiation path and flip BM_CM_4's countermodel
search from success to failure -- confirmed empirically: running BM_CM_4
alone with the counter pre-seeded at 17 (the exact value it reaches after
EX_CM_1, MD_CM_1..6, BM_CM_1, BM_CM_2 in ``test_bimodal.py``'s fixed
parametrize order) reproduces the isolated-run failure deterministically,
while every other tested seed (0, 5, 10, 13, 15, 16, 18, 20, 25, 30) passes.

Since each example already gets a fresh Z3 ``Context`` via
``isolated_z3_context()``, resetting this per-process counter once per fresh
``BimodalSemantics`` instance cannot reintroduce the aliasing bug the counter
exists to prevent: that bug is only possible when two calls resolve to the
same name *within the same Context*, and a freshly reset counter still hands
out strictly increasing, therefore distinct, suffixes for every call made
against that instance's (single) Context.
"""

import itertools

import pytest

from model_checker import ModelConstraints, Syntax, run_test
from model_checker.theory_lib.bimodal import (
    BimodalProposition,
    BimodalSemantics,
    BimodalStructure,
    bimodal_operators,
)
from model_checker.theory_lib.bimodal import operators as bimodal_operators_module
from model_checker.theory_lib.bimodal.examples import countermodel_examples, theorem_examples
from model_checker.utils.context import isolated_z3_context

test_examples = {**countermodel_examples, **theorem_examples}


@pytest.fixture(autouse=True)
def _restore_bound_var_counter():
    """Prevent this file's counter-poisoning tests from leaking into later tests."""
    original = bimodal_operators_module._bound_var_counter
    yield
    bimodal_operators_module._bound_var_counter = original


class TestBoundVarCounterResetOnSemanticsInit:
    """BimodalSemantics construction must reset the process-global counter."""

    def test_fresh_semantics_resets_counter_to_zero(self):
        """Regardless of prior process state, a new BimodalSemantics starts the
        counter back at 0, so bound-variable names are reproducible per example."""
        # Poison the counter, simulating several prior examples in the same process.
        bimodal_operators_module._bound_var_counter = itertools.count(17)

        settings = dict(BimodalSemantics.DEFAULT_EXAMPLE_SETTINGS)
        BimodalSemantics(settings)

        first_value = next(bimodal_operators_module._bound_var_counter)
        assert first_value == 0, (
            "BimodalSemantics.__init__ (via _reset_global_state) must reset "
            "_bound_var_counter so every example's bound-variable names are "
            "independent of how many examples ran earlier in this process; "
            f"got {first_value} instead of 0."
        )


class TestBoundVarCounterOrderIndependence:
    """End-to-end regression: BM_CM_4 must succeed no matter the counter's
    pre-existing value, matching the empirically observed poisoning point."""

    @pytest.mark.slow
    @pytest.mark.parametrize("poisoned_start", [0, 17, 30])
    def test_bm_cm_4_independent_of_prior_counter_state(self, poisoned_start):
        bimodal_operators_module._bound_var_counter = itertools.count(poisoned_start)

        case = test_examples["BM_CM_4"]
        with isolated_z3_context():
            result = run_test(
                case,
                BimodalSemantics,
                BimodalProposition,
                bimodal_operators,
                Syntax,
                ModelConstraints,
                BimodalStructure,
            )

        assert result, (
            f"BM_CM_4 failed with the bound-variable counter pre-seeded at "
            f"{poisoned_start}, demonstrating cross-test order dependence via "
            "the unreset process-global counter."
        )
