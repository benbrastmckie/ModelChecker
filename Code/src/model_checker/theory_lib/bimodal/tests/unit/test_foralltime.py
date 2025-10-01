"""Tests for ForAllTime and ExistsTime utilities in BimodalSemantics.

Phase 1: ForAllTime/ExistsTime Utilities (Foundation)
Tests written BEFORE implementation following TDD methodology.
"""

import pytest
import z3
from model_checker.theory_lib.bimodal.semantic import BimodalSemantics


@pytest.fixture
def semantics():
    """Create BimodalSemantics instance for testing."""
    settings = {
        'N': 3,
        'M': 2,
        'contingent': False,
        'disjoint': False,
        'max_time': 1,
        'expectation': True,
        'iterate': 1
    }
    return BimodalSemantics(settings)


class TestForAllTime:
    """Tests for ForAllTime utility method."""

    def test_foralltime_signature(self, semantics):
        """Test that ForAllTime method exists with correct signature."""
        assert hasattr(semantics, 'ForAllTime'), "BimodalSemantics should have ForAllTime method"

        # Test method is callable
        assert callable(semantics.ForAllTime), "ForAllTime should be callable"

        # Test basic invocation works (don't evaluate, just check structure)
        world = z3.Int('test_world')
        time_var = z3.Int('test_time')
        body = z3.Bool('test_body')

        result = semantics.ForAllTime(world, time_var, body)
        assert result is not None, "ForAllTime should return a value"

    def test_foralltime_wraps_validity(self, semantics):
        """Test that ForAllTime wraps body with is_valid_time_for_world check."""
        world = z3.Int('test_world')
        time_var = z3.Int('test_time')
        body = z3.Bool('test_body')

        result = semantics.ForAllTime(world, time_var, body)

        # Convert to string to inspect structure
        result_str = str(result)

        # Should contain ForAll quantifier
        assert 'ForAll' in result_str, "ForAllTime should use z3.ForAll"

        # Should reference the time variable
        assert 'test_time' in result_str, "ForAllTime should reference time variable"

        # Should contain Implies (validity → body)
        assert 'Implies' in result_str or '=>' in result_str or 'Or(Not' in result_str, \
            "ForAllTime should use Implies for validity check"

    def test_foralltime_structure(self, semantics):
        """Test that ForAllTime produces z3.ForAll quantifier."""
        world = z3.Int('test_world')
        time_var = z3.Int('test_time')
        body = z3.Bool('test_body')

        result = semantics.ForAllTime(world, time_var, body)

        # Check it's a Z3 expression
        assert isinstance(result, z3.ExprRef), "ForAllTime should return Z3 expression"

        # Check it's a quantifier expression
        assert z3.is_quantifier(result), "ForAllTime should return a quantifier"


class TestExistsTime:
    """Tests for ExistsTime utility method."""

    def test_existstime_signature(self, semantics):
        """Test that ExistsTime method exists with correct signature."""
        assert hasattr(semantics, 'ExistsTime'), "BimodalSemantics should have ExistsTime method"

        # Test method is callable
        assert callable(semantics.ExistsTime), "ExistsTime should be callable"

        # Test basic invocation works
        world = z3.Int('test_world')
        time_var = z3.Int('test_time')
        body = z3.Bool('test_body')

        result = semantics.ExistsTime(world, time_var, body)
        assert result is not None, "ExistsTime should return a value"

    def test_existstime_wraps_validity(self, semantics):
        """Test that ExistsTime wraps body with is_valid_time_for_world check."""
        world = z3.Int('test_world')
        time_var = z3.Int('test_time')
        body = z3.Bool('test_body')

        result = semantics.ExistsTime(world, time_var, body)

        # Convert to string to inspect structure
        result_str = str(result)

        # Should contain Exists quantifier
        assert 'Exists' in result_str, "ExistsTime should use z3.Exists"

        # Should reference the time variable
        assert 'test_time' in result_str, "ExistsTime should reference time variable"

        # Should contain And (validity ∧ body)
        assert 'And' in result_str, "ExistsTime should use And for validity conjunction"

    def test_existstime_structure(self, semantics):
        """Test that ExistsTime produces z3.Exists quantifier."""
        world = z3.Int('test_world')
        time_var = z3.Int('test_time')
        body = z3.Bool('test_body')

        result = semantics.ExistsTime(world, time_var, body)

        # Check it's a Z3 expression
        assert isinstance(result, z3.ExprRef), "ExistsTime should return Z3 expression"

        # Check it's a quantifier expression
        assert z3.is_quantifier(result), "ExistsTime should return a quantifier"


class TestTemporalOperatorsUsage:
    """Tests that temporal operators use ForAllTime/ExistsTime utilities.

    These tests verify the structure of operator outputs by inspecting
    the Z3 expressions they generate using mock arguments.
    """

    def test_future_operator_structure_uses_quantifier(self, semantics):
        """Test that FutureOperator.true_at() produces quantified formula."""
        from model_checker.theory_lib.bimodal.operators import FutureOperator

        # Create a mock argument structure for testing
        class MockArgument:
            pass

        # Patch semantics.true_at to return a simple Bool for testing structure
        original_true_at = semantics.true_at
        semantics.true_at = lambda sentence, eval_point: z3.Bool('mock_p')

        try:
            future_op = FutureOperator(semantics)
            arg = MockArgument()  # Mock argument
            eval_point = {"world": 0, "time": 0}

            # Call true_at - should use ForAllTime internally
            result = future_op.true_at(arg, eval_point)

            # Verify it returns a Z3 expression
            assert isinstance(result, z3.ExprRef), "FutureOperator.true_at should return Z3 expression"

            # Check structure includes quantifier (from ForAllTime)
            assert z3.is_quantifier(result), "FutureOperator.true_at should use quantifier (ForAllTime)"
        finally:
            semantics.true_at = original_true_at

    def test_future_operator_false_structure_uses_quantifier(self, semantics):
        """Test that FutureOperator.false_at() produces quantified formula."""
        from model_checker.theory_lib.bimodal.operators import FutureOperator

        class MockArgument:
            pass

        # Patch semantics.false_at to return a simple Bool for testing structure
        original_false_at = semantics.false_at
        semantics.false_at = lambda sentence, eval_point: z3.Bool('mock_not_p')

        try:
            future_op = FutureOperator(semantics)
            arg = MockArgument()
            eval_point = {"world": 0, "time": 0}

            # Call false_at - should use ExistsTime internally
            result = future_op.false_at(arg, eval_point)

            # Verify it returns a Z3 expression
            assert isinstance(result, z3.ExprRef), "FutureOperator.false_at should return Z3 expression"

            # Check structure includes quantifier (from ExistsTime)
            assert z3.is_quantifier(result), "FutureOperator.false_at should use quantifier (ExistsTime)"
        finally:
            semantics.false_at = original_false_at

    def test_past_operator_structure_uses_quantifier(self, semantics):
        """Test that PastOperator.true_at() produces quantified formula."""
        from model_checker.theory_lib.bimodal.operators import PastOperator

        class MockArgument:
            pass

        # Patch semantics.true_at to return a simple Bool for testing structure
        original_true_at = semantics.true_at
        semantics.true_at = lambda sentence, eval_point: z3.Bool('mock_p')

        try:
            past_op = PastOperator(semantics)
            arg = MockArgument()
            eval_point = {"world": 0, "time": 1}

            # Call true_at - should use ForAllTime internally
            result = past_op.true_at(arg, eval_point)

            # Verify it returns a Z3 expression
            assert isinstance(result, z3.ExprRef), "PastOperator.true_at should return Z3 expression"

            # Check structure includes quantifier (from ForAllTime)
            assert z3.is_quantifier(result), "PastOperator.true_at should use quantifier (ForAllTime)"
        finally:
            semantics.true_at = original_true_at

    def test_past_operator_false_structure_uses_quantifier(self, semantics):
        """Test that PastOperator.false_at() produces quantified formula."""
        from model_checker.theory_lib.bimodal.operators import PastOperator

        class MockArgument:
            pass

        # Patch semantics.false_at to return a simple Bool for testing structure
        original_false_at = semantics.false_at
        semantics.false_at = lambda sentence, eval_point: z3.Bool('mock_not_p')

        try:
            past_op = PastOperator(semantics)
            arg = MockArgument()
            eval_point = {"world": 0, "time": 1}

            # Call false_at - should use ExistsTime internally
            result = past_op.false_at(arg, eval_point)

            # Verify it returns a Z3 expression
            assert isinstance(result, z3.ExprRef), "PastOperator.false_at should return Z3 expression"

            # Check structure includes quantifier (from ExistsTime)
            assert z3.is_quantifier(result), "PastOperator.false_at should use quantifier (ExistsTime)"
        finally:
            semantics.false_at = original_false_at
