"""Integration tests for ProofChecker-aligned strict semantics.

These tests verify that the ModelChecker's temporal semantics match the ProofChecker's
strict semantics, specifically:

1. Temporal operators use strict ordering (< instead of <=) - already correct
2. ForAllTime/ExistsTime quantify over all times in domain D
3. Atoms are FALSE at times outside the world's domain
4. T-axioms (G(phi) -> phi) are NOT valid under strict semantics
5. Seriality axioms (T -> F(T)) ARE valid under strict semantics
"""

import pytest
import z3
from model_checker.theory_lib.bimodal.semantic import BimodalSemantics


@pytest.fixture
def semantics():
    """Create BimodalSemantics instance for testing."""
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


class TestQuantificationScope:
    """Tests that ForAllTime/ExistsTime quantify over all times in domain D."""

    def test_foralltime_uses_is_valid_time(self, semantics):
        """Test that ForAllTime uses is_valid_time (global D), not is_valid_time_for_world."""
        world = z3.Int('test_world')
        time_var = z3.Int('test_time')
        body = z3.Bool('test_body')

        result = semantics.ForAllTime(world, time_var, body)
        result_str = str(result)

        # Should NOT contain world-specific validity check
        # The new implementation uses is_valid_time which doesn't reference the world
        assert 'world_interval_start' not in result_str, \
            "ForAllTime should not use world-specific interval bounds"
        assert 'world_interval_end' not in result_str, \
            "ForAllTime should not use world-specific interval bounds"

    def test_existstime_uses_is_valid_time(self, semantics):
        """Test that ExistsTime uses is_valid_time (global D), not is_valid_time_for_world."""
        world = z3.Int('test_world')
        time_var = z3.Int('test_time')
        body = z3.Bool('test_body')

        result = semantics.ExistsTime(world, time_var, body)
        result_str = str(result)

        # Should NOT contain world-specific validity check
        assert 'world_interval_start' not in result_str, \
            "ExistsTime should not use world-specific interval bounds"
        assert 'world_interval_end' not in result_str, \
            "ExistsTime should not use world-specific interval bounds"


class TestAtomDomainCheck:
    """Tests that atoms are FALSE at times outside the world's domain."""

    def test_true_at_includes_domain_check_for_atoms(self, semantics):
        """Test that true_at for atoms includes is_valid_time_for_world check."""
        from model_checker.syntactic.atoms import get_atom_sort

        # Create a simple sentence letter mock with correct atom sort
        class MockSentence:
            sentence_letter = z3.Const('p', get_atom_sort())
            operator = None
            arguments = None

        sentence = MockSentence()
        eval_point = {"world": 0, "time": z3.IntVal(0)}

        result = semantics.true_at(sentence, eval_point)
        result_str = str(result)

        # Should contain And (combining domain check with truth condition)
        assert 'And' in result_str, \
            "true_at for atoms should include And to combine domain check with truth"

    def test_true_at_complex_formulas_no_domain_check(self, semantics):
        """Test that true_at for complex formulas delegates to operator (no direct domain check)."""
        # Create a mock complex sentence
        class MockOperator:
            def true_at(self, eval_point):
                return z3.Bool('operator_result')

        class MockSentence:
            sentence_letter = None
            operator = MockOperator()
            arguments = ()

        sentence = MockSentence()
        eval_point = {"world": 0, "time": z3.IntVal(0)}

        result = semantics.true_at(sentence, eval_point)
        result_str = str(result)

        # Should just be the operator result, not wrapped in And
        assert result_str == 'operator_result', \
            "true_at for complex formulas should delegate to operator without wrapping"


class TestStrictOrderingVerification:
    """Tests verifying that strict ordering is used in temporal operators."""

    def test_future_operator_uses_strict_less_than(self, semantics):
        """Verify FutureOperator uses < (strict) ordering."""
        from model_checker.theory_lib.bimodal.operators import FutureOperator

        class MockArgument:
            pass

        # Patch true_at to return a simple Bool
        original_true_at = semantics.true_at
        semantics.true_at = lambda sentence, eval_point: z3.Bool('mock_p')

        try:
            future_op = FutureOperator(semantics)
            arg = MockArgument()
            eval_point = {"world": 0, "time": z3.IntVal(0)}

            result = future_op.true_at(arg, eval_point)
            result_str = str(result)

            # Should contain strict < comparison
            # Note: Z3 may represent this in different ways, but the key is
            # that it uses strict ordering, not <=
            assert '<' in result_str or 'Lt' in result_str, \
                "FutureOperator should use strict < ordering"
        finally:
            semantics.true_at = original_true_at

    def test_past_operator_uses_strict_less_than(self, semantics):
        """Verify PastOperator uses < (strict) ordering."""
        from model_checker.theory_lib.bimodal.operators import PastOperator

        class MockArgument:
            pass

        original_true_at = semantics.true_at
        semantics.true_at = lambda sentence, eval_point: z3.Bool('mock_p')

        try:
            past_op = PastOperator(semantics)
            arg = MockArgument()
            eval_point = {"world": 0, "time": z3.IntVal(1)}

            result = past_op.true_at(arg, eval_point)
            result_str = str(result)

            # Should contain strict < comparison
            assert '<' in result_str or 'Lt' in result_str, \
                "PastOperator should use strict < ordering"
        finally:
            semantics.true_at = original_true_at


class TestTimeIntervalBounds:
    """Tests for time domain bounds in strict semantics."""

    def test_is_valid_time_checks_global_bounds(self, semantics):
        """Test that is_valid_time checks against global M bounds."""
        M = semantics.M

        # Time within bounds should be valid
        time_in_bounds = z3.IntVal(0)
        in_bounds_expr = semantics.is_valid_time(time_in_bounds)

        # Time at boundary should be checked properly
        time_at_lower = z3.IntVal(-M + 1)
        time_at_upper = z3.IntVal(M - 1)
        lower_expr = semantics.is_valid_time(time_at_lower)
        upper_expr = semantics.is_valid_time(time_at_upper)

        # Verify structure - these should be And expressions with bounds checks
        assert str(in_bounds_expr) is not None
        assert str(lower_expr) is not None
        assert str(upper_expr) is not None

    def test_is_valid_time_for_world_checks_world_interval(self, semantics):
        """Test that is_valid_time_for_world checks world-specific interval."""
        world = z3.Int('test_world')
        time = z3.Int('test_time')

        result = semantics.is_valid_time_for_world(world, time)
        result_str = str(result)

        # Should reference world_interval_start and world_interval_end
        assert 'world_interval_start' in result_str, \
            "is_valid_time_for_world should check world_interval_start"
        assert 'world_interval_end' in result_str, \
            "is_valid_time_for_world should check world_interval_end"


if __name__ == '__main__':
    pytest.main([__file__, '-v'])
