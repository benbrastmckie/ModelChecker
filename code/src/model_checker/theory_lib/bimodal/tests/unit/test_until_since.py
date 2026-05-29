"""Tests for Until and Since temporal operators in BimodalSemantics.

These operators implement strict witness semantics with open guard intervals:
- Until: U(event, guard) - event at future time s > t, guard in (t, s)
- Since: S(event, guard) - event at past time s < t, guard in (s, t)

Following Burgess convention: first argument is event, second is guard.
"""

import pytest
import z3
from model_checker.theory_lib.bimodal.semantic import BimodalSemantics
from model_checker.theory_lib.bimodal.operators import UntilOperator, SinceOperator


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


class TestUntilOperatorSignature:
    """Tests for UntilOperator basic structure and interface."""

    def test_until_operator_exists(self):
        """Test that UntilOperator class exists and is importable."""
        assert UntilOperator is not None
        assert hasattr(UntilOperator, 'name')
        assert hasattr(UntilOperator, 'arity')

    def test_until_operator_arity(self):
        """Test that UntilOperator has arity 2 (binary operator)."""
        assert UntilOperator.arity == 2

    def test_until_operator_name(self):
        """Test that UntilOperator has correct name."""
        assert UntilOperator.name == "\\Until"

    def test_until_has_required_methods(self, semantics):
        """Test that UntilOperator has all required operator methods."""
        op = UntilOperator(semantics)
        assert hasattr(op, 'true_at')
        assert hasattr(op, 'false_at')
        assert hasattr(op, 'find_truth_condition')
        assert hasattr(op, 'print_method')

    def test_until_methods_are_callable(self, semantics):
        """Test that UntilOperator methods are callable."""
        op = UntilOperator(semantics)
        assert callable(op.true_at)
        assert callable(op.false_at)
        assert callable(op.find_truth_condition)
        assert callable(op.print_method)


class TestSinceOperatorSignature:
    """Tests for SinceOperator basic structure and interface."""

    def test_since_operator_exists(self):
        """Test that SinceOperator class exists and is importable."""
        assert SinceOperator is not None
        assert hasattr(SinceOperator, 'name')
        assert hasattr(SinceOperator, 'arity')

    def test_since_operator_arity(self):
        """Test that SinceOperator has arity 2 (binary operator)."""
        assert SinceOperator.arity == 2

    def test_since_operator_name(self):
        """Test that SinceOperator has correct name."""
        assert SinceOperator.name == "\\Since"

    def test_since_has_required_methods(self, semantics):
        """Test that SinceOperator has all required operator methods."""
        op = SinceOperator(semantics)
        assert hasattr(op, 'true_at')
        assert hasattr(op, 'false_at')
        assert hasattr(op, 'find_truth_condition')
        assert hasattr(op, 'print_method')

    def test_since_methods_are_callable(self, semantics):
        """Test that SinceOperator methods are callable."""
        op = SinceOperator(semantics)
        assert callable(op.true_at)
        assert callable(op.false_at)
        assert callable(op.find_truth_condition)
        assert callable(op.print_method)


class TestUntilOperatorZ3Structure:
    """Tests that UntilOperator produces correct Z3 structure."""

    def test_until_true_at_returns_z3_expression(self, semantics):
        """Test that UntilOperator.true_at() returns Z3 expression."""
        class MockArgument:
            pass

        original_true_at = semantics.true_at
        semantics.true_at = lambda sentence, eval_point: z3.Bool('mock_p')

        try:
            op = UntilOperator(semantics)
            event_arg = MockArgument()
            guard_arg = MockArgument()
            eval_point = {"world": 0, "time": 0}

            result = op.true_at(event_arg, guard_arg, eval_point)

            assert isinstance(result, z3.ExprRef), "true_at should return Z3 expression"
        finally:
            semantics.true_at = original_true_at

    def test_until_true_at_uses_nested_quantifiers(self, semantics):
        """Test that UntilOperator.true_at() uses nested quantifiers (exists-forall)."""
        class MockArgument:
            pass

        original_true_at = semantics.true_at
        semantics.true_at = lambda sentence, eval_point: z3.Bool('mock_p')

        try:
            op = UntilOperator(semantics)
            event_arg = MockArgument()
            guard_arg = MockArgument()
            eval_point = {"world": 0, "time": 0}

            result = op.true_at(event_arg, guard_arg, eval_point)

            # Should be a quantifier (ExistsTime wraps in z3.Exists)
            assert z3.is_quantifier(result), "true_at should use quantifier"

            # Convert to string to check for nested structure
            result_str = str(result)
            assert 'Exists' in result_str, "Should contain Exists (outer quantifier)"
            # Note: ForAllTime uses ForAll internally
            assert 'ForAll' in result_str or 'Implies' in result_str, \
                "Should contain ForAll or Implies (inner quantifier structure)"
        finally:
            semantics.true_at = original_true_at

    def test_until_false_at_returns_z3_expression(self, semantics):
        """Test that UntilOperator.false_at() returns Z3 expression."""
        class MockArgument:
            pass

        original_false_at = semantics.false_at
        semantics.false_at = lambda sentence, eval_point: z3.Bool('mock_not_p')

        try:
            op = UntilOperator(semantics)
            event_arg = MockArgument()
            guard_arg = MockArgument()
            eval_point = {"world": 0, "time": 0}

            result = op.false_at(event_arg, guard_arg, eval_point)

            assert isinstance(result, z3.ExprRef), "false_at should return Z3 expression"
        finally:
            semantics.false_at = original_false_at

    def test_until_false_at_uses_nested_quantifiers(self, semantics):
        """Test that UntilOperator.false_at() uses nested quantifiers (forall-exists)."""
        class MockArgument:
            pass

        original_false_at = semantics.false_at
        semantics.false_at = lambda sentence, eval_point: z3.Bool('mock_not_p')

        try:
            op = UntilOperator(semantics)
            event_arg = MockArgument()
            guard_arg = MockArgument()
            eval_point = {"world": 0, "time": 0}

            result = op.false_at(event_arg, guard_arg, eval_point)

            assert z3.is_quantifier(result), "false_at should use quantifier"
        finally:
            semantics.false_at = original_false_at


class TestSinceOperatorZ3Structure:
    """Tests that SinceOperator produces correct Z3 structure."""

    def test_since_true_at_returns_z3_expression(self, semantics):
        """Test that SinceOperator.true_at() returns Z3 expression."""
        class MockArgument:
            pass

        original_true_at = semantics.true_at
        semantics.true_at = lambda sentence, eval_point: z3.Bool('mock_p')

        try:
            op = SinceOperator(semantics)
            event_arg = MockArgument()
            guard_arg = MockArgument()
            eval_point = {"world": 0, "time": 1}

            result = op.true_at(event_arg, guard_arg, eval_point)

            assert isinstance(result, z3.ExprRef), "true_at should return Z3 expression"
        finally:
            semantics.true_at = original_true_at

    def test_since_true_at_uses_nested_quantifiers(self, semantics):
        """Test that SinceOperator.true_at() uses nested quantifiers (exists-forall)."""
        class MockArgument:
            pass

        original_true_at = semantics.true_at
        semantics.true_at = lambda sentence, eval_point: z3.Bool('mock_p')

        try:
            op = SinceOperator(semantics)
            event_arg = MockArgument()
            guard_arg = MockArgument()
            eval_point = {"world": 0, "time": 1}

            result = op.true_at(event_arg, guard_arg, eval_point)

            assert z3.is_quantifier(result), "true_at should use quantifier"

            result_str = str(result)
            assert 'Exists' in result_str, "Should contain Exists (outer quantifier)"
        finally:
            semantics.true_at = original_true_at

    def test_since_false_at_returns_z3_expression(self, semantics):
        """Test that SinceOperator.false_at() returns Z3 expression."""
        class MockArgument:
            pass

        original_false_at = semantics.false_at
        semantics.false_at = lambda sentence, eval_point: z3.Bool('mock_not_p')

        try:
            op = SinceOperator(semantics)
            event_arg = MockArgument()
            guard_arg = MockArgument()
            eval_point = {"world": 0, "time": 1}

            result = op.false_at(event_arg, guard_arg, eval_point)

            assert isinstance(result, z3.ExprRef), "false_at should return Z3 expression"
        finally:
            semantics.false_at = original_false_at


class TestUntilVariableNaming:
    """Tests that UntilOperator uses unique variable names to prevent collision."""

    def test_until_true_at_variable_names(self, semantics):
        """Test that true_at uses unique variable names."""
        class MockArgument:
            pass

        original_true_at = semantics.true_at
        semantics.true_at = lambda sentence, eval_point: z3.Bool('mock_p')

        try:
            op = UntilOperator(semantics)
            event_arg = MockArgument()
            guard_arg = MockArgument()
            eval_point = {"world": 0, "time": 0}

            result = op.true_at(event_arg, guard_arg, eval_point)
            result_str = str(result)

            # Should use until_ prefix for variable names
            assert 'until_witness_time' in result_str, \
                "Should use 'until_witness_time' variable name"
            assert 'until_guard_time' in result_str, \
                "Should use 'until_guard_time' variable name"
        finally:
            semantics.true_at = original_true_at

    def test_until_false_at_variable_names(self, semantics):
        """Test that false_at uses unique variable names."""
        class MockArgument:
            pass

        original_false_at = semantics.false_at
        semantics.false_at = lambda sentence, eval_point: z3.Bool('mock_not_p')

        try:
            op = UntilOperator(semantics)
            event_arg = MockArgument()
            guard_arg = MockArgument()
            eval_point = {"world": 0, "time": 0}

            result = op.false_at(event_arg, guard_arg, eval_point)
            result_str = str(result)

            # Should use until_false_ prefix for variable names
            assert 'until_false_witness_time' in result_str, \
                "Should use 'until_false_witness_time' variable name"
            assert 'until_false_guard_time' in result_str, \
                "Should use 'until_false_guard_time' variable name"
        finally:
            semantics.false_at = original_false_at


class TestSinceVariableNaming:
    """Tests that SinceOperator uses unique variable names to prevent collision."""

    def test_since_true_at_variable_names(self, semantics):
        """Test that true_at uses unique variable names."""
        class MockArgument:
            pass

        original_true_at = semantics.true_at
        semantics.true_at = lambda sentence, eval_point: z3.Bool('mock_p')

        try:
            op = SinceOperator(semantics)
            event_arg = MockArgument()
            guard_arg = MockArgument()
            eval_point = {"world": 0, "time": 1}

            result = op.true_at(event_arg, guard_arg, eval_point)
            result_str = str(result)

            # Should use since_ prefix for variable names
            assert 'since_witness_time' in result_str, \
                "Should use 'since_witness_time' variable name"
            assert 'since_guard_time' in result_str, \
                "Should use 'since_guard_time' variable name"
        finally:
            semantics.true_at = original_true_at

    def test_since_false_at_variable_names(self, semantics):
        """Test that false_at uses unique variable names."""
        class MockArgument:
            pass

        original_false_at = semantics.false_at
        semantics.false_at = lambda sentence, eval_point: z3.Bool('mock_not_p')

        try:
            op = SinceOperator(semantics)
            event_arg = MockArgument()
            guard_arg = MockArgument()
            eval_point = {"world": 0, "time": 1}

            result = op.false_at(event_arg, guard_arg, eval_point)
            result_str = str(result)

            # Should use since_false_ prefix for variable names
            assert 'since_false_witness_time' in result_str, \
                "Should use 'since_false_witness_time' variable name"
            assert 'since_false_guard_time' in result_str, \
                "Should use 'since_false_guard_time' variable name"
        finally:
            semantics.false_at = original_false_at


class TestUntilFindTruthCondition:
    """Tests for UntilOperator.find_truth_condition method."""

    def test_until_find_truth_condition_returns_dict(self, semantics):
        """Test that find_truth_condition returns a dictionary."""

        # Create mock arguments with proposition and extension
        class MockProposition:
            def __init__(self, extension, model_structure):
                self.extension = extension
                self.model_structure = model_structure

        class MockArgument:
            def __init__(self, extension, model_structure):
                self.proposition = MockProposition(extension, model_structure)

        class MockModelStructure:
            def __init__(self, semantics):
                self.semantics = semantics

        # Setup: event true at time 1, guard true at all times
        model_structure = MockModelStructure(semantics)
        semantics.world_time_intervals = {0: (-1, 1)}

        event_extension = {0: ([1], [-1, 0])}  # event true at t=1
        guard_extension = {0: ([-1, 0, 1], [])}  # guard true everywhere

        event_arg = MockArgument(event_extension, model_structure)
        guard_arg = MockArgument(guard_extension, model_structure)

        op = UntilOperator(semantics)
        result = op.find_truth_condition(event_arg, guard_arg, {})

        assert isinstance(result, dict), "find_truth_condition should return dict"
        assert 0 in result, "Result should have entry for world 0"

    def test_until_find_truth_condition_basic_case(self, semantics):
        """Test Until with event at future time and guard always true."""

        class MockProposition:
            def __init__(self, extension, model_structure):
                self.extension = extension
                self.model_structure = model_structure

        class MockArgument:
            def __init__(self, extension, model_structure):
                self.proposition = MockProposition(extension, model_structure)

        class MockModelStructure:
            def __init__(self, semantics):
                self.semantics = semantics

        model_structure = MockModelStructure(semantics)
        semantics.world_time_intervals = {0: (-1, 1)}

        # event true at t=1, guard true at all times
        event_extension = {0: ([1], [-1, 0])}
        guard_extension = {0: ([-1, 0, 1], [])}

        event_arg = MockArgument(event_extension, model_structure)
        guard_arg = MockArgument(guard_extension, model_structure)

        op = UntilOperator(semantics)
        result = op.find_truth_condition(event_arg, guard_arg, {})

        true_times, false_times = result[0]

        # At t=-1: witness at t=1, guard in (-1, 1)={0} must be true -> U is true
        # At t=0: witness at t=1, guard in (0, 1)={} is vacuously true -> U is true
        # At t=1: no witness exists (no future time) -> U is false
        assert -1 in true_times, "U should be true at t=-1"
        assert 0 in true_times, "U should be true at t=0"
        assert 1 in false_times, "U should be false at t=1 (no future)"

    def test_until_vacuously_false_at_boundary(self, semantics):
        """Test that Until is vacuously false when no future times exist."""

        class MockProposition:
            def __init__(self, extension, model_structure):
                self.extension = extension
                self.model_structure = model_structure

        class MockArgument:
            def __init__(self, extension, model_structure):
                self.proposition = MockProposition(extension, model_structure)

        class MockModelStructure:
            def __init__(self, semantics):
                self.semantics = semantics

        model_structure = MockModelStructure(semantics)
        semantics.world_time_intervals = {0: (0, 2)}

        # event true everywhere, guard true everywhere
        event_extension = {0: ([0, 1, 2], [])}
        guard_extension = {0: ([0, 1, 2], [])}

        event_arg = MockArgument(event_extension, model_structure)
        guard_arg = MockArgument(guard_extension, model_structure)

        op = UntilOperator(semantics)
        result = op.find_truth_condition(event_arg, guard_arg, {})

        true_times, false_times = result[0]

        # At t=2: no future time exists, so Until is false
        assert 2 in false_times, "U should be false at last time (no future)"


class TestSinceFindTruthCondition:
    """Tests for SinceOperator.find_truth_condition method."""

    def test_since_find_truth_condition_returns_dict(self, semantics):
        """Test that find_truth_condition returns a dictionary."""

        class MockProposition:
            def __init__(self, extension, model_structure):
                self.extension = extension
                self.model_structure = model_structure

        class MockArgument:
            def __init__(self, extension, model_structure):
                self.proposition = MockProposition(extension, model_structure)

        class MockModelStructure:
            def __init__(self, semantics):
                self.semantics = semantics

        model_structure = MockModelStructure(semantics)
        semantics.world_time_intervals = {0: (-1, 1)}

        event_extension = {0: ([-1], [0, 1])}  # event true at t=-1
        guard_extension = {0: ([-1, 0, 1], [])}  # guard true everywhere

        event_arg = MockArgument(event_extension, model_structure)
        guard_arg = MockArgument(guard_extension, model_structure)

        op = SinceOperator(semantics)
        result = op.find_truth_condition(event_arg, guard_arg, {})

        assert isinstance(result, dict), "find_truth_condition should return dict"
        assert 0 in result, "Result should have entry for world 0"

    def test_since_find_truth_condition_basic_case(self, semantics):
        """Test Since with event at past time and guard always true."""

        class MockProposition:
            def __init__(self, extension, model_structure):
                self.extension = extension
                self.model_structure = model_structure

        class MockArgument:
            def __init__(self, extension, model_structure):
                self.proposition = MockProposition(extension, model_structure)

        class MockModelStructure:
            def __init__(self, semantics):
                self.semantics = semantics

        model_structure = MockModelStructure(semantics)
        semantics.world_time_intervals = {0: (-1, 1)}

        # event true at t=-1, guard true at all times
        event_extension = {0: ([-1], [0, 1])}
        guard_extension = {0: ([-1, 0, 1], [])}

        event_arg = MockArgument(event_extension, model_structure)
        guard_arg = MockArgument(guard_extension, model_structure)

        op = SinceOperator(semantics)
        result = op.find_truth_condition(event_arg, guard_arg, {})

        true_times, false_times = result[0]

        # At t=-1: no past time exists -> S is false
        # At t=0: witness at t=-1, guard in (-1, 0)={} is vacuously true -> S is true
        # At t=1: witness at t=-1, guard in (-1, 1)={0} must be true -> S is true
        assert -1 in false_times, "S should be false at t=-1 (no past)"
        assert 0 in true_times, "S should be true at t=0"
        assert 1 in true_times, "S should be true at t=1"

    def test_since_vacuously_false_at_boundary(self, semantics):
        """Test that Since is vacuously false when no past times exist."""

        class MockProposition:
            def __init__(self, extension, model_structure):
                self.extension = extension
                self.model_structure = model_structure

        class MockArgument:
            def __init__(self, extension, model_structure):
                self.proposition = MockProposition(extension, model_structure)

        class MockModelStructure:
            def __init__(self, semantics):
                self.semantics = semantics

        model_structure = MockModelStructure(semantics)
        semantics.world_time_intervals = {0: (0, 2)}

        # event true everywhere, guard true everywhere
        event_extension = {0: ([0, 1, 2], [])}
        guard_extension = {0: ([0, 1, 2], [])}

        event_arg = MockArgument(event_extension, model_structure)
        guard_arg = MockArgument(guard_extension, model_structure)

        op = SinceOperator(semantics)
        result = op.find_truth_condition(event_arg, guard_arg, {})

        true_times, false_times = result[0]

        # At t=0: no past time exists, so Since is false
        assert 0 in false_times, "S should be false at first time (no past)"


class TestOperatorRegistration:
    """Tests that Until and Since are properly registered in bimodal_operators."""

    def test_operators_in_bimodal_operators(self):
        """Test that UntilOperator and SinceOperator are in bimodal_operators."""
        from model_checker.theory_lib.bimodal.operators import bimodal_operators

        # Get operator names from collection
        operator_names = bimodal_operators.operator_dictionary.keys()

        # Check UntilOperator is registered
        assert "\\Until" in operator_names, "UntilOperator should be in bimodal_operators"

        # Check SinceOperator is registered
        assert "\\Since" in operator_names, "SinceOperator should be in bimodal_operators"
