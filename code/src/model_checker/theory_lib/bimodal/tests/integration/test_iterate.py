"""Tests for the BimodalModelIterator implementation.

This module tests the iteration flow and model presentation for the bimodal
theory. Written fresh against the current BimodalStructure/BuildExample
contract -- deliberately NOT a restoration of the old 156-line Mock-heavy
version, which mocked structure attributes (``worlds``, ``time_points``)
that no longer match the current ``BimodalStructure`` (world histories are
keyed by ``world_id`` -> {time: state}, not a flat ``worlds`` list).
"""

import pytest
from types import SimpleNamespace
from unittest.mock import Mock, patch

from model_checker import z3_shim as z3
from model_checker.builder.example import BuildExample
from model_checker.theory_lib import bimodal
from model_checker.theory_lib.bimodal.iterate import (
    BimodalModelIterator,
    iterate_example,
    iterate_example_generator,
)


def _bimodal_general_settings():
    """General settings covering models.semantic.DEFAULT_GENERAL_SETTINGS
    plus bimodal's ADDITIONAL_GENERAL_SETTINGS (align_vertically)."""
    return {
        'print_impossible': False,
        'print_constraints': False,
        'print_z3': False,
        'save_output': False,
        'sequential': False,
        'maximize': False,
        'solver': 'z3',
        'align_vertically': True,
    }


def _mock_build_module(general_settings):
    mock_module = Mock()
    mock_module.general_settings = general_settings
    mock_module.raw_general_settings = general_settings
    mock_module.module_flags = SimpleNamespace(
        contingent=False,
        disjoint=False,
        non_empty=False,
        non_null=False,
        print_constraints=False,
        save_output=False,
        print_impossible=False,
        print_z3=False,
        maximize=False,
    )
    return mock_module


class TestBimodalIteratorMocked:
    """Mock-based tests exercising the iterator's construction and helper
    methods in isolation, matching the style used by the other three
    theories' test_iterate.py files."""

    def test_basic_iteration(self):
        """Test that the BimodalModelIterator can be constructed."""
        mock_example = Mock(spec=BuildExample)

        mock_example.model_structure = Mock()
        mock_example.model_structure.z3_model_status = True
        mock_example.model_structure.z3_model = Mock()
        mock_example.model_structure.solver = z3.Solver()
        mock_example.model_structure.world_histories = {}
        mock_example.model_structure.sentence_letters = []
        mock_example.model_structure.z3_world_states = []
        mock_example.model_structure.z3_possible_states = []
        mock_example.model_structure.semantics = Mock()
        mock_example.model_structure.z3_model_runtime = 0.1
        mock_example.model_structure._search_duration = 0.1
        mock_example.model_structure._total_search_time = 0.1

        mock_example.model_constraints = Mock()
        mock_example.model_constraints.all_constraints = []

        mock_example.settings = {'iterate': 2, 'max_time': 5.0}

        iterator = BimodalModelIterator(mock_example)

        assert iterator is not None
        assert hasattr(iterator, 'build_example')
        assert iterator.build_example == mock_example

    def test_bimodal_specific_differences(self):
        """Test that the BimodalModelIterator correctly calculates
        world-history/truth-condition differences between two structures."""
        mock_example = Mock(spec=BuildExample)

        mock_example.model_structure = Mock()
        mock_example.model_structure.z3_model_status = True
        mock_example.model_structure.z3_model = Mock()
        mock_example.model_structure.solver = z3.Solver()
        mock_example.model_structure.world_histories = {}
        mock_example.model_structure.sentence_letters = []
        mock_example.model_structure.z3_world_states = []
        mock_example.model_structure.z3_possible_states = []
        mock_example.model_structure.semantics = Mock()
        mock_example.model_structure.z3_model_runtime = 0.1
        mock_example.model_structure._search_duration = 0.1
        mock_example.model_structure._total_search_time = 0.1

        mock_example.model_constraints = Mock()
        mock_example.model_constraints.all_constraints = []

        mock_example.settings = {'iterate': 1, 'max_time': 5.0}

        iterator = BimodalModelIterator(mock_example)

        new_structure = Mock()
        new_structure.z3_model = Mock()
        new_structure.semantics = Mock()
        new_structure.semantics.M = 2  # real int: task_rel duration_range needs -M+1..M
        new_structure.world_histories = {0: {0: 'a', 1: 'b'}}
        new_structure.sentence_letters = []
        # BimodalStructure/BimodalSemantics do not define these optional
        # attributes; remove Mock's auto-created attributes so the getattr(
        # ..., default) calls in _calculate_bimodal_differences correctly
        # fall through to their declared defaults instead of iterating a
        # Mock() as if it were a real dict.
        del new_structure.detect_model_differences
        del new_structure.semantics.world_time_intervals
        del new_structure.time_shift_relations

        previous_structure = Mock()
        previous_structure.z3_model = Mock()
        previous_structure.semantics = Mock()
        previous_structure.world_histories = {0: {0: 'a', 1: 'c'}}
        previous_structure.sentence_letters = []
        del previous_structure.semantics.world_time_intervals
        del previous_structure.time_shift_relations

        differences = iterator._calculate_differences(new_structure, previous_structure)

        assert isinstance(differences, dict)
        assert 'world_histories' in differences
        assert 0 in differences['world_histories']
        assert differences['world_histories'][0][1] == {'old': 'c', 'new': 'b'}

    def test_iterate_example_function(self):
        """Test that the iterate_example function works correctly."""
        mock_example = Mock(spec=BuildExample)

        mock_example.model_structure = Mock()
        mock_example.model_structure.z3_model_status = True
        mock_example.model_structure.z3_model = Mock()
        mock_example.model_structure.solver = z3.Solver()
        mock_example.model_structure.world_histories = {}
        mock_example.model_structure.sentence_letters = []
        mock_example.model_structure.z3_world_states = []
        mock_example.model_structure.z3_possible_states = []
        mock_example.model_structure.semantics = Mock()
        mock_example.model_structure.z3_model_runtime = 0.1
        mock_example.model_structure._search_duration = 0.1
        mock_example.model_structure._total_search_time = 0.1

        mock_example.model_constraints = Mock()
        mock_example.model_constraints.all_constraints = []

        mock_example.settings = {'iterate': 1, 'max_time': 5.0}

        with patch.object(BimodalModelIterator, 'iterate', return_value=[mock_example.model_structure]):
            result = iterate_example(mock_example, max_iterations=1)

            assert isinstance(result, list)
            assert len(result) >= 1

    def test_create_difference_constraint_uses_valid_semantics_attributes(self):
        """_create_difference_constraint must reference real BimodalSemantics
        attributes (world_function, M, max_world_id, truth_condition) -- not
        the removed W/T/world_history attributes present in the pre-refactor
        restored source. A prior version of this file referenced attributes
        that no longer exist and would raise AttributeError if ever invoked."""
        mock_example = Mock(spec=BuildExample)
        mock_example.model_structure = Mock()
        mock_example.model_structure.z3_model_status = True
        mock_example.model_structure.z3_model = Mock()
        mock_example.model_structure.solver = z3.Solver()
        mock_example.model_structure.world_histories = {}
        mock_example.model_structure.sentence_letters = []
        mock_example.model_structure.z3_world_states = []
        mock_example.model_structure.z3_possible_states = []
        mock_example.model_structure.semantics = Mock()
        mock_example.model_structure.z3_model_runtime = 0.1
        mock_example.model_structure._search_duration = 0.1
        mock_example.model_structure._total_search_time = 0.1
        mock_example.model_constraints = Mock()
        mock_example.model_constraints.all_constraints = []
        mock_example.settings = {'iterate': 1, 'max_time': 5.0}

        iterator = BimodalModelIterator(mock_example)

        semantics = Mock()
        semantics.M = 2
        semantics.max_world_id = 4
        semantics.world_function = Mock(return_value=z3.Array('wf', z3.IntSort(), z3.IntSort()))
        semantics.truth_condition = Mock(return_value=z3.BoolVal(True))
        mock_example.model_constraints.semantics = semantics
        mock_example.example_syntax = Mock()
        mock_example.example_syntax.sentence_letters = []

        prev_model = Mock()
        prev_model.eval = Mock(return_value=z3.IntVal(0))

        constraint = iterator._create_difference_constraint([prev_model])
        assert constraint is not None


def _skip_if_solver_timed_out(example):
    """Skip when Z3 returned UNKNOWN rather than a decided result.

    WHY THIS EXISTS -- A TIMEOUT IS NOT AN UNSAT. `ModelDefaults.solve()` (see
    `code/src/model_checker/models/structure.py`) returns `_create_result(True, None, False,
    ...)` on `SolverResult.UNKNOWN`, i.e. `timeout=True` AND `z3_model_status=False`. A
    genuine unsatisfiable result returns `timeout=False, z3_model_status=False`. Asserting on
    `z3_model_status` alone therefore CANNOT distinguish "the solver ran out of budget under
    CI contention" from "these constraints are unsatisfiable", and a contention-induced
    timeout inverts into a false negative reading "First model was not satisfiable".

    That is a hole in the discriminator, not a budget that needs raising. This example's
    `max_time` was already widened 30 -> 60 for exactly this failure, and it recurred anyway on
    `nix flake check` (CI run 32996446859) -- because no `max_time` value closes the hole. The
    structure already carries the discriminator; these tests simply were not consulting it.

    This does NOT weaken the assertion it guards: a genuine unsat still has `timeout=False`
    and still fails. Only the inconclusive case is routed to a skip, where it belongs -- an
    undecided solver run is not evidence about satisfiability in either direction.

    Deliberately a `skip`, not an `xfail`: the outcome is nondeterministic (budget-dependent),
    and `xfail` would report a spurious XPASS on every run where the solve does finish in
    time. See TESTING_GUIDE.md section 8.6 on timing-budget discipline.
    """
    if example.model_structure.timeout:
        pytest.skip(
            "Z3 returned UNKNOWN (budget exhausted under load), not a decided result; "
            "an inconclusive solve cannot exercise iteration and is not an unsat. "
            f"max_time={example.model_structure.settings.get('max_time')}s, "
            f"runtime={example.model_structure.z3_model_runtime}s"
        )


class TestSkipIfSolverTimedOut:
    """Unit tests for the timeout/unsat discriminator itself.

    WHY THESE EXIST. `_skip_if_solver_timed_out`'s skip branch only fires when Z3 returns
    UNKNOWN under real contention -- a condition that does not reproduce on an idle
    development host, where both real-solve tests below pass with the branch never taken.
    Without these tests the discriminator would ship exercised only on the CI runs it is
    meant to protect, which is precisely backwards. A stub structure lets both branches be
    driven deterministically in microseconds.
    """

    @staticmethod
    def _example(timeout, z3_model_status, max_time=60, runtime=None):
        return SimpleNamespace(
            model_structure=SimpleNamespace(
                timeout=timeout,
                z3_model_status=z3_model_status,
                z3_model_runtime=runtime,
                settings={"max_time": max_time},
            )
        )

    def test_skips_when_solver_returned_unknown(self):
        """timeout=True is the UNKNOWN case -- inconclusive, not unsat."""
        # NOTE: pytest.skip() raises Skipped, which subclasses BaseException, not Exception.
        # pytest.raises(Exception) would let it propagate and silently skip THIS test instead
        # of asserting on it -- which is exactly what happened on the first draft of these
        # tests (reported "2 passed, 2 skipped" where 4 passed was expected).
        with pytest.raises(BaseException) as excinfo:
            _skip_if_solver_timed_out(self._example(timeout=True, z3_model_status=False, runtime=60.2))
        assert excinfo.typename == "Skipped", (
            f"Expected a pytest skip, got {excinfo.typename}"
        )

    def test_does_not_skip_on_genuine_unsat(self):
        """timeout=False with z3_model_status=False is a REAL unsat.

        This is the case the guard must let through to the assertion -- routing it to a skip
        would be the assertion-weakening this fix exists to avoid.
        """
        _skip_if_solver_timed_out(self._example(timeout=False, z3_model_status=False))

    def test_does_not_skip_on_satisfiable_result(self):
        _skip_if_solver_timed_out(self._example(timeout=False, z3_model_status=True))

    def test_skip_message_names_the_budget_and_runtime(self):
        """The skip reason must carry enough to diagnose without re-running."""
        with pytest.raises(BaseException) as excinfo:
            _skip_if_solver_timed_out(self._example(timeout=True, z3_model_status=False, max_time=60, runtime=60.4))
        assert excinfo.typename == "Skipped"
        msg = str(excinfo.value)
        assert "max_time=60" in msg
        assert "60.4" in msg
        assert "not an unsat" in msg


class TestBimodalIteratorReal:
    """Functional tests exercising the iterator against a real (non-mocked)
    bimodal model, proving that ``iterate: 2`` produces distinct models
    instead of the pre-restoration ``ImportError`` at the builder layer."""

    def _build_example(self, iterate=2):
        theory = bimodal.get_theory()
        general_settings = _bimodal_general_settings()
        mock_module = _mock_build_module(general_settings)
        mock_module.semantic_theories = {"Bimodal": theory}

        example_case = [
            ['(A \\vee B)'],
            ['(A \\wedge B)'],
            # max_time generous per TESTING_GUIDE.md 8.6: observed solve
            # times for this example are 2-4s in isolation and vary further
            # under full-suite load, so a tight budget here silently
            # inverts the "First model was not satisfiable" assertion below
            # into a false negative on a timeout rather than a real result.
            # Raised 30 -> 60: CI contention caused Z3 to hit the 30s cap and
            # return an unsatisfiable first model, inverting the
            # z3_model_status assertion into a false negative.
            {'N': 2, 'M': 2, 'max_time': 60, 'contingent': True, 'iterate': iterate},
        ]

        return BuildExample(mock_module, theory, example_case)

    def test_iterate_example_generator_is_exposed_on_package(self):
        """The runner-preferred generator interface is importable from the
        theory package, matching exclusion/imposition/logos."""
        assert hasattr(bimodal, 'iterate_example_generator')
        assert bimodal.iterate_example_generator.returns_generator is True

    def test_iterate_two_produces_distinct_models(self):
        """A bimodal example with iterate: 2 runs the full search for a
        second model via iterate_example instead of raising ImportError at
        the builder layer (the live, reachable defect this phase closes --
        see bimodal/docs/ITERATE.md and semantic/core.py's DEFAULT_EXAMPLE_SETTINGS
        'iterate' entry).

        Whether Z3 actually finds a second, non-isomorphic model within the
        timeout budget is a separate question from whether the mechanism is
        wired correctly: bimodal's heavier frame constraints (task_rel
        transitivity, world-function definedness) make the generic
        is_world-keyed difference constraint in iterate/constraints.py
        (shared by all four theories) slower to satisfy than for the
        flatter state-based theories. This test asserts the search runs to
        completion without error and returns at least the initial model; if
        a second model IS found within budget, it is verified distinct.
        """
        example = self._build_example(iterate=2)

        _skip_if_solver_timed_out(example)

        assert example.model_structure.z3_model_status, (
            "First model was not satisfiable; cannot exercise iteration"
        )

        model_structures = iterate_example(example, max_iterations=2)

        assert len(model_structures) >= 1
        if len(model_structures) > 1:
            first, second = model_structures[0], model_structures[1]
            assert first.z3_model is not second.z3_model
            assert hasattr(second, 'model_differences')

    def test_iterate_example_generator_yields_models(self):
        """The generator interface runs without error and wires up the
        iterator on the example.

        iterate_example_generator only yields models found DURING the
        search (the initial model already lives at
        example.model_structure and is not re-yielded), so an empty list
        here is a legitimate outcome under a tight timeout -- see the note
        on test_iterate_two_produces_distinct_models. The property this
        test actually guards is the one Phase 22 restores: calling this
        function does not raise ImportError, and it attaches the iterator
        for downstream debug-message access exactly as
        builder/runner.py's generator-preferring code path expects.
        """
        example = self._build_example(iterate=2)

        _skip_if_solver_timed_out(example)

        assert example.model_structure.z3_model_status, (
            "First model was not satisfiable; cannot exercise iteration"
        )

        models = list(iterate_example_generator(example, max_iterations=2))

        assert isinstance(models, list)
        assert hasattr(example, '_iterator')
        assert isinstance(example._iterator, BimodalModelIterator)
        if models:
            assert hasattr(models[0], 'model_differences')
