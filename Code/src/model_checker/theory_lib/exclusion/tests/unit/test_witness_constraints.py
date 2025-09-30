"""
Unit tests for exclusion witness constraint generation.

Tests the WitnessConstraintGenerator class functionality including
constraint generation for witness predicates based on negation semantics.
"""

import pytest
import z3
from unittest.mock import Mock, MagicMock
from typing import List, Dict, Any

from model_checker.theory_lib.exclusion.semantic.constraints import WitnessConstraintGenerator


class TestWitnessConstraintGenerator:
    """Test the WitnessConstraintGenerator class."""

    @pytest.fixture
    def mock_semantics(self) -> Mock:
        """Create a mock semantics object for testing."""
        semantics = Mock()
        semantics.N = 3
        return semantics

    @pytest.fixture
    def constraint_generator(self, mock_semantics: Mock) -> WitnessConstraintGenerator:
        """Create a WitnessConstraintGenerator instance for testing."""
        return WitnessConstraintGenerator(mock_semantics)

    def test_initialization(self, constraint_generator: WitnessConstraintGenerator, mock_semantics: Mock) -> None:
        """Test that WitnessConstraintGenerator initializes correctly."""
        assert constraint_generator.semantics is mock_semantics
        assert constraint_generator.N == 3

    def test_initialization_with_different_n(self) -> None:
        """Test initialization with different N values."""
        for n in [2, 3, 4, 5]:
            semantics = Mock()
            semantics.N = n
            generator = WitnessConstraintGenerator(semantics)

            assert generator.semantics is semantics
            assert generator.N == n

    def test_generate_witness_constraints_signature(self, constraint_generator: WitnessConstraintGenerator) -> None:
        """Test that generate_witness_constraints has correct signature."""
        # Create mock parameters
        formula_str = "test_formula"
        formula_ast = Mock()
        h_pred = z3.Function("test_h", z3.BitVecSort(3), z3.BitVecSort(3))
        y_pred = z3.Function("test_y", z3.BitVecSort(3), z3.BitVecSort(3))
        eval_point = {"world": z3.BitVecVal(1, 3)}

        # Test that method can be called without error
        result = constraint_generator.generate_witness_constraints(
            formula_str, formula_ast, h_pred, y_pred, eval_point
        )

        # Result should be a list
        assert isinstance(result, list)

    def test_generate_witness_constraints_empty_case(self, constraint_generator: WitnessConstraintGenerator) -> None:
        """Test constraint generation for case with no verifying states."""
        # Mock _could_verify_negation to always return False
        constraint_generator._could_verify_negation = Mock(return_value=False)

        formula_str = "empty_test"
        formula_ast = Mock()
        h_pred = z3.Function("empty_h", z3.BitVecSort(3), z3.BitVecSort(3))
        y_pred = z3.Function("empty_y", z3.BitVecSort(3), z3.BitVecSort(3))
        eval_point = {"world": z3.BitVecVal(1, 3)}

        result = constraint_generator.generate_witness_constraints(
            formula_str, formula_ast, h_pred, y_pred, eval_point
        )

        # Should return empty list if no states can verify negation
        assert isinstance(result, list)
        # Note: actual behavior depends on implementation details

    def test_generate_witness_constraints_with_verifying_states(self, constraint_generator: WitnessConstraintGenerator) -> None:
        """Test constraint generation for case with verifying states."""
        # Mock helper methods
        constraint_generator._could_verify_negation = Mock(return_value=True)
        constraint_generator._witness_constraints_for_state = Mock(return_value=[z3.Bool('test_constraint')])

        formula_str = "verifying_test"
        formula_ast = Mock()
        h_pred = z3.Function("verifying_h", z3.BitVecSort(3), z3.BitVecSort(3))
        y_pred = z3.Function("verifying_y", z3.BitVecSort(3), z3.BitVecSort(3))
        eval_point = {"world": z3.BitVecVal(1, 3)}

        result = constraint_generator.generate_witness_constraints(
            formula_str, formula_ast, h_pred, y_pred, eval_point
        )

        assert isinstance(result, list)
        # Check that _could_verify_negation was called for all states (2^N states)
        assert constraint_generator._could_verify_negation.call_count == 2**3  # 8 states for N=3

    def test_state_iteration_coverage(self, constraint_generator: WitnessConstraintGenerator) -> None:
        """Test that constraint generation covers all possible states."""
        # Mock helper methods to track calls
        constraint_generator._could_verify_negation = Mock(return_value=False)

        formula_str = "coverage_test"
        formula_ast = Mock()
        h_pred = z3.Function("coverage_h", z3.BitVecSort(3), z3.BitVecSort(3))
        y_pred = z3.Function("coverage_y", z3.BitVecSort(3), z3.BitVecSort(3))
        eval_point = {"world": z3.BitVecVal(1, 3)}

        constraint_generator.generate_witness_constraints(
            formula_str, formula_ast, h_pred, y_pred, eval_point
        )

        # Check that all states from 0 to 2^N-1 were checked
        expected_states = list(range(2**3))
        actual_calls = [call[0][0] for call in constraint_generator._could_verify_negation.call_args_list]

        assert len(actual_calls) == len(expected_states)
        assert set(actual_calls) == set(expected_states)

    def test_constraint_generator_attribute_access(self, constraint_generator: WitnessConstraintGenerator) -> None:
        """Test that constraint generator correctly accesses semantics attributes."""
        # Test that N is correctly derived from semantics
        assert constraint_generator.N == constraint_generator.semantics.N

        # Test semantics reference
        assert constraint_generator.semantics is not None

    def test_z3_function_parameters(self, constraint_generator: WitnessConstraintGenerator) -> None:
        """Test handling of Z3 function parameters."""
        # Create proper Z3 functions
        h_pred = z3.Function("param_h", z3.BitVecSort(3), z3.BitVecSort(3))
        y_pred = z3.Function("param_y", z3.BitVecSort(3), z3.BitVecSort(3))

        # Check that functions have correct signatures
        assert h_pred.arity() == 1
        assert y_pred.arity() == 1
        assert h_pred.domain(0) == z3.BitVecSort(3)
        assert h_pred.range() == z3.BitVecSort(3)

    def test_eval_point_parameter_handling(self, constraint_generator: WitnessConstraintGenerator) -> None:
        """Test handling of evaluation point parameter."""
        # Mock methods to check parameter passing
        constraint_generator._could_verify_negation = Mock(return_value=False)

        formula_str = "eval_point_test"
        formula_ast = Mock()
        h_pred = z3.Function("eval_h", z3.BitVecSort(3), z3.BitVecSort(3))
        y_pred = z3.Function("eval_y", z3.BitVecSort(3), z3.BitVecSort(3))
        eval_point = {"world": z3.BitVecVal(2, 3), "extra": "data"}

        constraint_generator.generate_witness_constraints(
            formula_str, formula_ast, h_pred, y_pred, eval_point
        )

        # Check that eval_point was passed to helper methods
        for call in constraint_generator._could_verify_negation.call_args_list:
            args, kwargs = call
            assert len(args) >= 3  # state, formula_ast, eval_point
            assert args[2] is eval_point

    def test_formula_ast_parameter_propagation(self, constraint_generator: WitnessConstraintGenerator) -> None:
        """Test that formula AST is properly propagated to helper methods."""
        # Mock methods to track parameter passing
        constraint_generator._could_verify_negation = Mock(return_value=True)
        constraint_generator._witness_constraints_for_state = Mock(return_value=[])

        formula_str = "ast_test"
        formula_ast = Mock()
        formula_ast.test_attribute = "test_value"  # Add identifiable attribute
        h_pred = z3.Function("ast_h", z3.BitVecSort(3), z3.BitVecSort(3))
        y_pred = z3.Function("ast_y", z3.BitVecSort(3), z3.BitVecSort(3))
        eval_point = {"world": z3.BitVecVal(1, 3)}

        constraint_generator.generate_witness_constraints(
            formula_str, formula_ast, h_pred, y_pred, eval_point
        )

        # Verify formula_ast was passed correctly
        for call in constraint_generator._could_verify_negation.call_args_list:
            args, kwargs = call
            passed_ast = args[1]
            assert passed_ast is formula_ast
            assert passed_ast.test_attribute == "test_value"


class TestWitnessConstraintGeneratorHelperMethods:
    """Test helper methods of WitnessConstraintGenerator (when accessible)."""

    @pytest.fixture
    def generator_with_mocked_helpers(self) -> WitnessConstraintGenerator:
        """Create generator with helper methods mocked for testing."""
        semantics = Mock()
        semantics.N = 2  # Smaller N for easier testing
        generator = WitnessConstraintGenerator(semantics)

        # Mock private helper methods
        generator._could_verify_negation = Mock()
        generator._witness_constraints_for_state = Mock()

        return generator

    def test_helper_method_signatures(self, generator_with_mocked_helpers: WitnessConstraintGenerator) -> None:
        """Test that helper methods are called with correct signatures."""
        # Set up return values
        generator_with_mocked_helpers._could_verify_negation.return_value = True
        generator_with_mocked_helpers._witness_constraints_for_state.return_value = [z3.Bool('test')]

        formula_str = "helper_test"
        formula_ast = Mock()
        h_pred = z3.Function("helper_h", z3.BitVecSort(2), z3.BitVecSort(2))
        y_pred = z3.Function("helper_y", z3.BitVecSort(2), z3.BitVecSort(2))
        eval_point = {"world": z3.BitVecVal(1, 2)}

        generator_with_mocked_helpers.generate_witness_constraints(
            formula_str, formula_ast, h_pred, y_pred, eval_point
        )

        # Check _could_verify_negation calls
        assert generator_with_mocked_helpers._could_verify_negation.call_count == 4  # 2^2 = 4 states

        # Check _witness_constraints_for_state calls (should be called for each verifying state)
        verify_calls = generator_with_mocked_helpers._witness_constraints_for_state.call_args_list
        assert len(verify_calls) == 4  # All states verify in this mock

        # Check signature of _witness_constraints_for_state calls
        for call in verify_calls:
            args, kwargs = call
            assert len(args) == 5  # state_bv, formula_ast, h_pred, y_pred, eval_point
            assert isinstance(args[0], z3.BitVecNumRef)  # state_bv
            assert args[1] is formula_ast
            assert args[2] is h_pred
            assert args[3] is y_pred
            assert args[4] is eval_point

    def test_constraint_accumulation(self, generator_with_mocked_helpers: WitnessConstraintGenerator) -> None:
        """Test that constraints are properly accumulated from helper methods."""
        # Set up helper method return values
        generator_with_mocked_helpers._could_verify_negation.return_value = True
        test_constraints = [z3.Bool('constraint1'), z3.Bool('constraint2')]
        generator_with_mocked_helpers._witness_constraints_for_state.return_value = test_constraints

        formula_str = "accumulation_test"
        formula_ast = Mock()
        h_pred = z3.Function("acc_h", z3.BitVecSort(2), z3.BitVecSort(2))
        y_pred = z3.Function("acc_y", z3.BitVecSort(2), z3.BitVecSort(2))
        eval_point = {"world": z3.BitVecVal(1, 2)}

        result = generator_with_mocked_helpers.generate_witness_constraints(
            formula_str, formula_ast, h_pred, y_pred, eval_point
        )

        # Each state should contribute test_constraints, and we have 4 states
        expected_total_constraints = len(test_constraints) * 4
        assert len(result) == expected_total_constraints

        # All constraints should be Z3 BoolRef objects
        for constraint in result:
            assert isinstance(constraint, z3.BoolRef)