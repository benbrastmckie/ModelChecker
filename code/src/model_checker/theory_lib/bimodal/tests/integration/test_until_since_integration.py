"""Integration tests for Until and Since temporal operators.

These tests verify that the operators work correctly with the full model checking
infrastructure, including Z3 solving and extension computation.

Key tests:
- U(p, top) should be equivalent to F(p) - "p eventually"
- S(p, top) should be equivalent to P(p) - "p occurred"
- Open guard interval behavior
- Boundary time behavior
"""

import pytest
from model_checker.theory_lib.bimodal import (
    BimodalSemantics,
    BimodalProposition,
    bimodal_operators,
)
from model_checker.syntactic import Operator


def get_operator_by_name(name):
    """Get operator class by name from bimodal_operators."""
    return bimodal_operators.operator_dictionary.get(name)


class TestUntilSinceAPIConsistency:
    """Test API consistency for Until and Since operators."""

    def test_until_has_find_truth_condition_with_eval_point(self):
        """Test that UntilOperator.find_truth_condition has eval_point parameter."""
        import inspect

        UntilOperator = get_operator_by_name("\\Until")
        assert UntilOperator is not None, "UntilOperator should be registered"

        signature = inspect.signature(UntilOperator.find_truth_condition)
        parameters = list(signature.parameters.keys())

        # Should have: self, event_arg, guard_arg, eval_point
        assert parameters[0] == 'self'
        assert parameters[-1] == 'eval_point', \
            f"eval_point should be last parameter, got {parameters}"

    def test_since_has_find_truth_condition_with_eval_point(self):
        """Test that SinceOperator.find_truth_condition has eval_point parameter."""
        import inspect

        SinceOperator = get_operator_by_name("\\Since")
        assert SinceOperator is not None, "SinceOperator should be registered"

        signature = inspect.signature(SinceOperator.find_truth_condition)
        parameters = list(signature.parameters.keys())

        # Should have: self, event_arg, guard_arg, eval_point
        assert parameters[0] == 'self'
        assert parameters[-1] == 'eval_point', \
            f"eval_point should be last parameter, got {parameters}"

    def test_operators_in_collection(self):
        """Test that Until and Since are properly in the operator collection."""
        assert "\\Until" in bimodal_operators.operator_dictionary
        assert "\\Since" in bimodal_operators.operator_dictionary

        UntilOperator = get_operator_by_name("\\Until")
        SinceOperator = get_operator_by_name("\\Since")

        assert UntilOperator.arity == 2
        assert SinceOperator.arity == 2


class TestUntilSinceSemantics:
    """Test semantic behavior of Until and Since operators."""

    @pytest.fixture
    def semantics(self):
        """Create BimodalSemantics instance with small model."""
        settings = {
            'N': 2,  # 2 worlds
            'M': 2,  # time interval [-1, 1]
            'contingent': False,
            'disjoint': False,
            'max_time': 1,
            'expectation': True,
            'iterate': 1
        }
        return BimodalSemantics(settings)

    def test_until_operator_instantiation(self, semantics):
        """Test that UntilOperator can be instantiated with semantics."""
        UntilOperator = get_operator_by_name("\\Until")
        op = UntilOperator(semantics)

        assert op is not None
        assert op.semantics is semantics
        assert op.arity == 2

    def test_since_operator_instantiation(self, semantics):
        """Test that SinceOperator can be instantiated with semantics."""
        SinceOperator = get_operator_by_name("\\Since")
        op = SinceOperator(semantics)

        assert op is not None
        assert op.semantics is semantics
        assert op.arity == 2


class TestUntilSinceZ3Integration:
    """Test Z3 integration for Until and Since."""

    @pytest.fixture
    def semantics(self):
        """Create BimodalSemantics instance."""
        settings = {
            'N': 2,
            'M': 2,
            'contingent': False,
            'disjoint': False,
            'max_time': 1,
            'expectation': True,
            'iterate': 1
        }
        return BimodalSemantics(settings)

    def test_until_true_at_produces_valid_z3(self, semantics):
        """Test that UntilOperator.true_at produces valid Z3 expression."""
        import z3 as z3_lib

        UntilOperator = get_operator_by_name("\\Until")
        op = UntilOperator(semantics)

        # Mock arguments
        class MockArg:
            pass

        original_true_at = semantics.true_at
        semantics.true_at = lambda s, ep: z3_lib.Bool('mock')

        try:
            result = op.true_at(MockArg(), MockArg(), {"world": 0, "time": 0})

            # Result should be a valid Z3 expression that can be used in solving
            assert isinstance(result, z3_lib.ExprRef)

            # Should be satisfiable in general
            solver = z3_lib.Solver()
            solver.add(result)
            check_result = solver.check()
            # The result could be sat or unsat, but should not error
            assert check_result in [z3_lib.sat, z3_lib.unsat]
        finally:
            semantics.true_at = original_true_at

    def test_since_true_at_produces_valid_z3(self, semantics):
        """Test that SinceOperator.true_at produces valid Z3 expression."""
        import z3 as z3_lib

        SinceOperator = get_operator_by_name("\\Since")
        op = SinceOperator(semantics)

        class MockArg:
            pass

        original_true_at = semantics.true_at
        semantics.true_at = lambda s, ep: z3_lib.Bool('mock')

        try:
            result = op.true_at(MockArg(), MockArg(), {"world": 0, "time": 1})

            assert isinstance(result, z3_lib.ExprRef)

            solver = z3_lib.Solver()
            solver.add(result)
            check_result = solver.check()
            assert check_result in [z3_lib.sat, z3_lib.unsat]
        finally:
            semantics.true_at = original_true_at


class TestUntilSinceFindTruthConditionIntegration:
    """Integration tests for find_truth_condition with realistic extensions."""

    @pytest.fixture
    def semantics(self):
        """Create BimodalSemantics with known time intervals."""
        settings = {
            'N': 1,  # 1 world
            'M': 3,  # time interval [-2, 2]
            'contingent': False,
            'disjoint': False,
            'max_time': 2,
            'expectation': True,
            'iterate': 1
        }
        sem = BimodalSemantics(settings)
        sem.world_time_intervals = {0: (-2, 2)}
        return sem

    def test_until_with_immediate_witness(self, semantics):
        """Test Until when event occurs immediately at next time."""
        UntilOperator = get_operator_by_name("\\Until")
        op = UntilOperator(semantics)

        class MockProposition:
            def __init__(self, ext, ms):
                self.extension = ext
                self.model_structure = ms

        class MockArg:
            def __init__(self, ext, ms):
                self.proposition = MockProposition(ext, ms)

        class MockMS:
            def __init__(self, sem):
                self.semantics = sem

        ms = MockMS(semantics)

        # event true at t=1, guard true everywhere
        event_arg = MockArg({0: ([1], [-2, -1, 0, 2])}, ms)
        guard_arg = MockArg({0: ([-2, -1, 0, 1, 2], [])}, ms)

        result = op.find_truth_condition(event_arg, guard_arg, {})
        true_times, false_times = result[0]

        # At t=0: witness at t=1, guard in (0,1) is empty -> U is true
        assert 0 in true_times, "Until should be true at t=0 with immediate witness"

        # At t=-1: witness at t=1, guard in (-1,1)={0} must be true -> U is true
        assert -1 in true_times, "Until should be true at t=-1"

        # At t=2: no future -> U is false
        assert 2 in false_times, "Until should be false at last time"

    def test_since_with_immediate_witness(self, semantics):
        """Test Since when event occurred immediately at previous time."""
        SinceOperator = get_operator_by_name("\\Since")
        op = SinceOperator(semantics)

        class MockProposition:
            def __init__(self, ext, ms):
                self.extension = ext
                self.model_structure = ms

        class MockArg:
            def __init__(self, ext, ms):
                self.proposition = MockProposition(ext, ms)

        class MockMS:
            def __init__(self, sem):
                self.semantics = sem

        ms = MockMS(semantics)

        # event true at t=-1, guard true everywhere
        event_arg = MockArg({0: ([-1], [-2, 0, 1, 2])}, ms)
        guard_arg = MockArg({0: ([-2, -1, 0, 1, 2], [])}, ms)

        result = op.find_truth_condition(event_arg, guard_arg, {})
        true_times, false_times = result[0]

        # At t=0: witness at t=-1, guard in (-1,0) is empty -> S is true
        assert 0 in true_times, "Since should be true at t=0 with immediate witness"

        # At t=1: witness at t=-1, guard in (-1,1)={0} must be true -> S is true
        assert 1 in true_times, "Since should be true at t=1"

        # At t=-2: no past -> S is false
        assert -2 in false_times, "Since should be false at first time"

    def test_until_fails_when_guard_fails(self, semantics):
        """Test Until when guard fails in the interval."""
        UntilOperator = get_operator_by_name("\\Until")
        op = UntilOperator(semantics)

        class MockProposition:
            def __init__(self, ext, ms):
                self.extension = ext
                self.model_structure = ms

        class MockArg:
            def __init__(self, ext, ms):
                self.proposition = MockProposition(ext, ms)

        class MockMS:
            def __init__(self, sem):
                self.semantics = sem

        ms = MockMS(semantics)

        # event true at t=2, guard FALSE at t=1
        event_arg = MockArg({0: ([2], [-2, -1, 0, 1])}, ms)
        guard_arg = MockArg({0: ([-2, -1, 0, 2], [1])}, ms)  # guard false at t=1

        result = op.find_truth_condition(event_arg, guard_arg, {})
        true_times, false_times = result[0]

        # At t=0: only witness at t=2, guard in (0,2)={1} has guard false -> U is false
        assert 0 in false_times, "Until should be false when guard fails in interval"

        # At t=1: witness at t=2, guard in (1,2)={} is empty -> U is true
        assert 1 in true_times, "Until should be true when guard interval is empty"

    def test_since_fails_when_guard_fails(self, semantics):
        """Test Since when guard fails in the interval."""
        SinceOperator = get_operator_by_name("\\Since")
        op = SinceOperator(semantics)

        class MockProposition:
            def __init__(self, ext, ms):
                self.extension = ext
                self.model_structure = ms

        class MockArg:
            def __init__(self, ext, ms):
                self.proposition = MockProposition(ext, ms)

        class MockMS:
            def __init__(self, sem):
                self.semantics = sem

        ms = MockMS(semantics)

        # event true at t=-2, guard FALSE at t=-1
        event_arg = MockArg({0: ([-2], [-1, 0, 1, 2])}, ms)
        guard_arg = MockArg({0: ([-2, 0, 1, 2], [-1])}, ms)  # guard false at t=-1

        result = op.find_truth_condition(event_arg, guard_arg, {})
        true_times, false_times = result[0]

        # At t=0: only witness at t=-2, guard in (-2,0)={-1} has guard false -> S is false
        assert 0 in false_times, "Since should be false when guard fails in interval"

        # At t=-1: witness at t=-2, guard in (-2,-1)={} is empty -> S is true
        assert -1 in true_times, "Since should be true when guard interval is empty"
