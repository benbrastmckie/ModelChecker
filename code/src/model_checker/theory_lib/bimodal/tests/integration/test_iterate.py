"""Tests for the BimodalModelIterator implementation under the certificate redesign
(Phase 15): difference/non-isomorphism constraints over label bits and box guesses, and
label/guess-based difference detection and display.

Deliberately not a full live `iterate: N` end-to-end run: `BaseModelIterator.iterate()`
delegates model exclusion to the shared, theory-agnostic `ConstraintGenerator`
(`model_checker/iterate/constraints.py`), which is gated on `hasattr(semantics, 'is_world')`
-- true of the other three theories, false of this one by design (D3/D4 have no
state-existence predicate). This is a genuine, discovered gap in the live loop's exclusion
mechanism for bimodal specifically, recorded in `iterate.py`'s own module docstring and in
this phase's plan section and handoff -- not something these tests can exercise correctly
until (and unless) that shared mechanism grows a theory-specific extension point. What these
tests exercise instead is `BimodalModelIterator`'s own methods directly (interface parity
with the retired encoding's own approach, unaffected by that gap).
"""

from __future__ import annotations

from types import SimpleNamespace
from unittest.mock import Mock, patch

import pytest

from model_checker import z3_shim as z3
from model_checker.builder.example import BuildExample
from model_checker.solver import is_true
from model_checker.theory_lib.bimodal import get_theory
from model_checker.theory_lib.bimodal.examples import (
    BM_CM_1_conclusions,
    BM_CM_1_premises,
    BM_CM_1_settings,
)
from model_checker.theory_lib.bimodal.iterate import (
    BimodalModelIterator,
    iterate_example,
)
from model_checker.theory_lib.bimodal.semantic.certificate import LabelledLasso, WitnessFamily
from model_checker.theory_lib.bimodal.semantic.core import BimodalSemantics
from model_checker.theory_lib.bimodal.semantic.formula import Atom


def _settings(**overrides):
    settings = dict(BimodalSemantics.DEFAULT_EXAMPLE_SETTINGS)
    settings.update(overrides)
    return settings


def _mock_build_example(semantics):
    """A Mock-based `build_example`, matching the construction pattern already used by
    this test module before the redesign: `BaseModelIterator.__init__`'s own
    `ConstraintGenerator` only needs `model_structure.solver` to be a live (possibly
    empty) Z3 solver, `model_constraints.all_constraints`, and `settings`."""
    mock_example = Mock(spec=BuildExample)
    mock_example.model_structure = Mock()
    mock_example.model_structure.z3_model_status = True
    mock_example.model_structure.z3_model = Mock()
    mock_example.model_structure.solver = z3.Solver()
    mock_example.model_structure.z3_model_runtime = 0.1
    mock_example.model_structure._search_duration = 0.1
    mock_example.model_structure._total_search_time = 0.1
    # IterationStatistics.add_model() calls len() on these -- must be real lists, not
    # Mock's auto-created attributes.
    mock_example.model_structure.z3_world_states = []
    mock_example.model_structure.z3_possible_states = []

    mock_example.model_constraints = Mock()
    mock_example.model_constraints.all_constraints = []
    mock_example.model_constraints.semantics = semantics

    mock_example.settings = {'iterate': 1, 'max_time': 5.0}
    return mock_example


class TestConstruction:
    def test_iterator_constructs_against_a_real_bimodal_semantics(self):
        semantics = BimodalSemantics(_settings())
        iterator = BimodalModelIterator(_mock_build_example(semantics))
        assert iterator is not None
        assert iterator.build_example.model_constraints.semantics is semantics


class TestDifferenceConstraintOverLabelsAndGuesses:
    def _solved_model(self, semantics, premise_infix="A", conclusion_infix="B"):
        from model_checker.syntactic import Syntax
        from model_checker.theory_lib.bimodal.operators import bimodal_operators

        premise = Syntax([premise_infix], [], bimodal_operators).premises[0]
        conclusion = Syntax([conclusion_infix], [], bimodal_operators).premises[0]
        premise_constraint = semantics.premise_behavior(premise)
        conclusion_constraint = semantics.conclusion_behavior(conclusion)
        semantics.finalize_certificate()
        solver = z3.Solver()
        for c in semantics.frame_constraints + [premise_constraint, conclusion_constraint]:
            solver.add(c)
        assert solver.check() == z3.sat
        return solver.model()

    def test_create_difference_constraint_is_true_for_the_solved_model_itself(self):
        """A blocking clause built against a model must itself be FALSE when evaluated
        against that same model (every disjunct is `var != var's own value`)."""
        semantics = BimodalSemantics(_settings(back=1, mid=0, fwd=1))
        iterator = BimodalModelIterator(_mock_build_example(semantics))
        model = self._solved_model(semantics)

        constraint = iterator._create_difference_constraint([model])
        result = model.eval(constraint, model_completion=True)
        assert str(result) == "False"

    def test_create_difference_constraint_with_no_variables_is_trivially_true(self):
        semantics = BimodalSemantics(_settings())
        iterator = BimodalModelIterator(_mock_build_example(semantics))
        constraint = iterator._create_difference_constraint([])
        assert str(constraint) == "True"

    def test_create_non_isomorphic_constraint_is_false_against_its_own_model(self):
        semantics = BimodalSemantics(_settings(back=1, mid=0, fwd=1))
        iterator = BimodalModelIterator(_mock_build_example(semantics))
        model = self._solved_model(semantics)

        constraint = iterator._create_non_isomorphic_constraint(model)
        result = model.eval(constraint, model_completion=True)
        assert str(result) == "False"


class TestCalculateDifferences:
    def _certificate(self, atom_in_main):
        main_label = frozenset({atom_in_main}) if atom_in_main else frozenset()
        main = LabelledLasso(back=(frozenset(),), mid=(), fwd=(main_label,))
        return WitnessFamily(bx={}, lassos=(main,))

    def test_label_difference_is_detected_between_two_structures(self):
        semantics = BimodalSemantics(_settings(back=1, mid=0, fwd=1))
        iterator = BimodalModelIterator(_mock_build_example(semantics))

        atom = Atom("A")
        new_structure = SimpleNamespace(
            certificate=self._certificate(atom), target_time=0, semantics=semantics
        )
        previous_structure = SimpleNamespace(
            certificate=self._certificate(None), target_time=0, semantics=semantics
        )

        differences = iterator._calculate_differences(new_structure, previous_structure)
        assert differences["labels"]
        assert 0 in differences["labels"]

    def test_no_certificate_on_either_side_yields_empty_differences(self):
        semantics = BimodalSemantics(_settings())
        iterator = BimodalModelIterator(_mock_build_example(semantics))
        new_structure = SimpleNamespace(certificate=None, target_time=None, semantics=semantics)
        previous_structure = SimpleNamespace(certificate=None, target_time=None, semantics=semantics)
        differences = iterator._calculate_differences(new_structure, previous_structure)
        assert differences["labels"] == {}
        assert differences["box_guesses"] == {}

    def test_display_model_differences_does_not_raise(self, capsys):
        semantics = BimodalSemantics(_settings(back=1, mid=0, fwd=1))
        iterator = BimodalModelIterator(_mock_build_example(semantics))
        atom = Atom("A")
        model_structure = SimpleNamespace(
            model_differences={
                "labels": {0: {0: {"old": ["Atom(...)"], "new": []}}},
                "box_guesses": {"Atom('A')": {"old": True, "new": False}},
                "target_time": {"old": 0, "new": 1},
            }
        )
        iterator.display_model_differences(model_structure, output=__import__("sys").stdout)
        out = capsys.readouterr().out
        assert "DIFFERENCES FROM PREVIOUS MODEL" in out
        assert "Label Changes:" in out
        assert "Box Guess Changes:" in out
        assert "Target Time:" in out


class TestIterateExampleFunction:
    def test_iterate_example_function(self):
        semantics = BimodalSemantics(_settings())
        mock_example = _mock_build_example(semantics)

        with patch.object(BimodalModelIterator, 'iterate', return_value=[mock_example.model_structure]):
            result = iterate_example(mock_example, max_iterations=1)
            assert isinstance(result, list)
            assert len(result) >= 1


def _real_build_example(premises, conclusions, settings, iterate_count):
    """A real, non-mocked `BuildExample` -- no Mock stands in for the solver, the model,
    or the semantics -- matching the construction pattern already used by the other three
    theories' own `test_iterate.py` (`BuildExample(mock_module, semantic_theory,
    example_case)`; only the surrounding `BuildModule` is a Mock, never the model-checking
    path itself)."""
    theory = get_theory()
    general_settings = dict(settings)
    general_settings['iterate'] = iterate_count
    mock_module = Mock()
    mock_module.semantic_theories = {"bimodal": theory}
    mock_module.general_settings = general_settings
    mock_module.raw_general_settings = general_settings
    mock_module.module_flags = SimpleNamespace(
        contingent=False, disjoint=False, non_empty=False, non_null=False,
        print_constraints=False, save_output=False, print_impossible=False,
        print_z3=False, maximize=False,
    )
    example_case = [premises, conclusions, general_settings]
    return BuildExample(mock_module, theory, example_case)


class TestLiveIteration:
    """Live, non-mocked end-to-end `iterate: 3` coverage against a real
    `BuildExample`/`BimodalModelIterator` pair -- the RED test this plan's rest of the
    phases must turn GREEN. Deliberately not mocked at any point on the model-building
    path: this is exactly the path that crashes today with
    `AttributeError: 'BimodalSemantics' object has no attribute 'is_world'`
    (surfaced as `ModelExtractionError`) -- see the task baselines' Defect 1 reproduction.
    """

    def test_iterate_three_yields_three_pairwise_distinct_certificates(self):
        example = _real_build_example(
            BM_CM_1_premises, BM_CM_1_conclusions, BM_CM_1_settings, iterate_count=3
        )
        iterator = BimodalModelIterator(example)

        structures = list(iterator.iterate_generator())

        # (a) no exception raised getting here at all.
        # (b) three model structures yielded (the generator excludes the first model,
        #     which BuildExample already solved; iterate: 3 means 2 more from the generator).
        assert len(structures) == 2
        assert len(iterator.model_structures) == 3

        # (c) each has a non-None certificate.
        all_structures = [example.model_structure] + structures
        for structure in all_structures:
            assert structure.certificate is not None

        # (d) certificates pairwise distinct in at least one label bit or box guess.
        semantics = example.model_constraints.semantics
        registry = semantics.witness_registry
        variables = list(registry._bits.values()) + list(registry._guesses.values())
        models = [example.model_structure.z3_model] + iterator.found_models
        assert len(models) == 3
        for i in range(len(models)):
            for j in range(i + 1, len(models)):
                differs = any(
                    bool(is_true(models[i].eval(var, model_completion=True)))
                    != bool(is_true(models[j].eval(var, model_completion=True)))
                    for var in variables
                )
                assert differs, f"models {i} and {j} agree on every certificate variable"
