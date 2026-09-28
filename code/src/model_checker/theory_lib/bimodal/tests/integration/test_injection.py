"""Test Z3 injection for bimodal, rewritten for the certificate redesign (Phase 18).

`inject_z3_model_values` (`semantic/core.py`) was rewritten in Phase 9/10 for the
certificate encoding's own variable set -- label bits (`WitnessRegistry._bits`), box
guesses (`WitnessRegistry._guesses`), and the target selector
(`WitnessConstraintGenerator._sel`) -- in place of the retired encoding's
world/truth_condition/task_rel variables (`is_world`, `truth_condition`, `task_rel` no
longer exist at all). These tests build a real satisfiable example through the same
pipeline `test_structure.py` uses, then verify injection pins every one of those three
variable families as a concrete constraint matching the found model's own values --
exactly what the model iterator (Phase 15) needs from this method to build a blocking
constraint against a previous solve.
"""

from __future__ import annotations

from unittest.mock import Mock

import z3

from model_checker.models.constraints import ModelConstraints
from model_checker.syntactic import Syntax
from model_checker.theory_lib.bimodal.operators import bimodal_operators
from model_checker.theory_lib.bimodal.semantic.core import BimodalSemantics
from model_checker.theory_lib.bimodal.semantic.model import BimodalStructure
from model_checker.theory_lib.bimodal.semantic.proposition import BimodalProposition
from model_checker.solver import is_true


def _settings(**overrides):
    settings = dict(BimodalSemantics.DEFAULT_EXAMPLE_SETTINGS)
    settings.update(overrides)
    return settings


def _build_solved(premises, conclusions, **setting_overrides):
    """Build and solve one example through the real pipeline, mirroring
    `test_structure.py`'s own `_build` helper."""
    settings = _settings(**setting_overrides)
    syntax = Syntax(premises, conclusions, bimodal_operators)
    model_constraints = ModelConstraints(settings, syntax, BimodalSemantics(settings), BimodalProposition)
    structure = BimodalStructure(model_constraints, settings)
    return structure


class TestInjectZ3ModelValuesExists:
    def test_method_exists_on_semantics(self):
        semantics = BimodalSemantics(_settings())
        assert hasattr(semantics, "inject_z3_model_values")


class TestInjectPinsLabelBitsAndGuesses:
    def test_every_bit_and_guess_pinned_matching_the_found_model(self):
        structure = _build_solved(["A"], ["\\Box A"], back=1, mid=1, fwd=1)
        assert structure.certificate is not None, "expected a countermodel"
        assert structure.z3_model is not None

        registry = structure.semantics.witness_registry
        generator = structure.semantics.constraint_generator
        assert registry._bits, "expected at least one label-bit variable to have been allocated"

        mock_constraints = Mock()
        mock_constraints.frame_constraints = []
        mock_constraints.model_constraints = []
        mock_constraints.premise_constraints = []
        mock_constraints.conclusion_constraints = []

        structure.semantics.inject_z3_model_values(
            structure.z3_model, structure.semantics, mock_constraints
        )

        pinned = mock_constraints.model_constraints
        # One pinned constraint per bit + per guess + per selector variable.
        expected_count = len(registry._bits) + len(registry._guesses) + len(generator._sel)
        assert len(pinned) == expected_count

        # Every pinned constraint must agree with the model's own evaluation: a bare
        # variable when true in the model, `Not(var)` when false.
        pinned_strs = {str(c) for c in pinned}
        for var in list(registry._bits.values()) + list(registry._guesses.values()) + list(
            generator._sel.values()
        ):
            value = structure.z3_model.eval(var, model_completion=True)
            expected = var if is_true(value) else z3.Not(var)
            assert str(expected) in pinned_strs, f"missing pinned constraint for {var}"

    def test_injected_constraints_are_satisfiable_together_with_the_original_model(self):
        """Re-solving with the injected constraints added must still be `sat` -- they pin
        the found model's own values, so they cannot conflict with it."""
        structure = _build_solved(["A"], ["\\Box A"], back=1, mid=1, fwd=1)
        assert structure.certificate is not None

        mock_constraints = Mock()
        mock_constraints.frame_constraints = []
        mock_constraints.model_constraints = []
        mock_constraints.premise_constraints = []
        mock_constraints.conclusion_constraints = []
        structure.semantics.inject_z3_model_values(
            structure.z3_model, structure.semantics, mock_constraints
        )

        solver = z3.Solver()
        solver.add(*mock_constraints.model_constraints)
        assert solver.check() == z3.sat


class TestInjectRequiresARealModel:
    def test_no_countermodel_case_leaves_z3_model_none(self):
        """A theorem example (no certificate) is UNSAT, and `ModelDefaults.solve()` leaves
        `self.z3_model = None` in that case (confirmed directly, not assumed) -- injection
        is only ever called by the model iterator (Phase 15) after a SAT result to build a
        blocking constraint against it, so there is no "UNSAT but inject anyway" case to
        support. This test records the `z3_model is None` precondition so a future change
        to `inject_z3_model_values` cannot silently start assuming a model exists."""
        structure = _build_solved(["A"], ["A"], back=1, mid=1, fwd=1)
        assert structure.certificate is None
        assert structure.z3_model_status is False
        assert structure.z3_model is None
