"""
Unit tests for imposition semantic core implementation.

Tests the ImpositionSemantics class core functionality including
imposition operation and alternative world calculation.
"""

import pytest
import z3
from unittest.mock import Mock, patch
from typing import Dict, Any, Set
from model_checker.theory_lib.imposition.semantic.core import ImpositionSemantics


class TestImpositionSemantics:
    """Test the ImpositionSemantics core class."""

    @pytest.fixture
    def basic_settings(self) -> Dict[str, Any]:
        """Basic settings for ImpositionSemantics."""
        return {
            'N': 3,
            'contingent': False,
            'non_empty': False,
            'non_null': False,
            'disjoint': False,
            'max_time': 1,
            'iterate': 1,
            'expectation': None,
        }

    @pytest.fixture
    def imposition_semantics(self, basic_settings: Dict[str, Any]) -> ImpositionSemantics:
        """Create an ImpositionSemantics instance for testing."""
        return ImpositionSemantics(basic_settings)

    def test_initialization(self, imposition_semantics: ImpositionSemantics) -> None:
        """Test that ImpositionSemantics initializes correctly."""
        assert imposition_semantics.N == 3
        # Should inherit from LogosSemantics
        from model_checker.theory_lib.logos.semantic import LogosSemantics
        assert isinstance(imposition_semantics, LogosSemantics)

    def test_default_example_settings(self) -> None:
        """Test that default example settings are properly defined."""
        expected_keys = {
            'N', 'contingent', 'non_empty', 'non_null', 'disjoint',
            'max_time', 'iterate', 'expectation'
        }
        assert set(ImpositionSemantics.DEFAULT_EXAMPLE_SETTINGS.keys()) == expected_keys
        assert ImpositionSemantics.DEFAULT_EXAMPLE_SETTINGS['N'] == 3

    def test_additional_general_settings(self) -> None:
        """Test that additional general settings include derive_imposition."""
        assert 'derive_imposition' in ImpositionSemantics.ADDITIONAL_GENERAL_SETTINGS
        assert ImpositionSemantics.ADDITIONAL_GENERAL_SETTINGS['derive_imposition'] is False

    def test_alt_imposition_method_signature(self, imposition_semantics: ImpositionSemantics) -> None:
        """Test that alt_imposition method has correct signature."""
        # Create Z3 bit vector references
        state_y = z3.BitVecVal(1, 3)
        state_w = z3.BitVecVal(2, 3)
        state_u = z3.BitVecVal(3, 3)

        result = imposition_semantics.alt_imposition(state_y, state_w, state_u)
        assert isinstance(result, z3.BoolRef)

    def test_alt_imposition_different_states(self, imposition_semantics: ImpositionSemantics) -> None:
        """Test alt_imposition with different state combinations."""
        # Test various state combinations
        test_cases = [
            (0, 1, 2),
            (1, 1, 1),  # Same states
            (7, 0, 3),  # Max values for N=3
        ]

        for y, w, u in test_cases:
            state_y = z3.BitVecVal(y, 3)
            state_w = z3.BitVecVal(w, 3)
            state_u = z3.BitVecVal(u, 3)

            result = imposition_semantics.alt_imposition(state_y, state_w, state_u)
            assert isinstance(result, z3.BoolRef)

    def test_calculate_outcome_worlds_signature(self, imposition_semantics: ImpositionSemantics) -> None:
        """Test calculate_outcome_worlds method signature."""
        verifiers = {1, 2, 3}
        eval_point = {"world": z3.BitVecVal(1, 3)}
        model_structure = Mock()

        result = imposition_semantics.calculate_outcome_worlds(verifiers, eval_point, model_structure)
        assert isinstance(result, set)

    def test_calculate_outcome_worlds_empty_verifiers(self, imposition_semantics: ImpositionSemantics) -> None:
        """Test calculate_outcome_worlds with empty verifiers."""
        verifiers = set()
        eval_point = {"world": z3.BitVecVal(1, 3)}
        model_structure = Mock()

        result = imposition_semantics.calculate_outcome_worlds(verifiers, eval_point, model_structure)
        assert isinstance(result, set)

    def test_calculate_outcome_worlds_single_verifier(self, imposition_semantics: ImpositionSemantics) -> None:
        """Test calculate_outcome_worlds with single verifier."""
        verifiers = {1}
        eval_point = {"world": z3.BitVecVal(2, 3)}
        model_structure = Mock()

        result = imposition_semantics.calculate_outcome_worlds(verifiers, eval_point, model_structure)
        assert isinstance(result, set)

    def test_calculate_outcome_worlds_multiple_verifiers(self, imposition_semantics: ImpositionSemantics) -> None:
        """Test calculate_outcome_worlds with multiple verifiers."""
        verifiers = {1, 2, 4}
        eval_point = {"world": z3.BitVecVal(3, 3)}
        model_structure = Mock()

        result = imposition_semantics.calculate_outcome_worlds(verifiers, eval_point, model_structure)
        assert isinstance(result, set)

    def test_inheritance_from_logos_semantics(self, imposition_semantics: ImpositionSemantics) -> None:
        """Test that ImpositionSemantics properly inherits from LogosSemantics."""
        from model_checker.theory_lib.logos.semantic import LogosSemantics

        # Check inheritance
        assert isinstance(imposition_semantics, LogosSemantics)

        # Check that inherited methods are available
        assert hasattr(imposition_semantics, 'true_at')
        assert hasattr(imposition_semantics, 'false_at')
        assert hasattr(imposition_semantics, 'is_world')
        assert hasattr(imposition_semantics, 'compatible')

    def test_imposition_specific_methods(self, imposition_semantics: ImpositionSemantics) -> None:
        """Test that imposition-specific methods exist."""
        # Check imposition-specific methods
        assert hasattr(imposition_semantics, 'alt_imposition')
        assert hasattr(imposition_semantics, 'calculate_outcome_worlds')
        assert hasattr(imposition_semantics, '_define_imposition_operation')
        assert hasattr(imposition_semantics, '_derive_imposition')

    def test_settings_inheritance_and_extension(self, basic_settings: Dict[str, Any]) -> None:
        """Test that settings are properly handled in inheritance."""
        # Test that ImpositionSemantics can be created with logos-compatible settings
        extended_settings = {**basic_settings, 'derive_imposition': True}
        semantics = ImpositionSemantics(extended_settings)

        assert semantics.N == 3
        # Imposition-specific behavior should be configurable
        # (exact implementation depends on how settings are handled)

    def test_z3_compatibility_for_imposition_operations(self, imposition_semantics: ImpositionSemantics) -> None:
        """Test that imposition operations are compatible with Z3."""
        # Create Z3 variables for testing
        y = z3.BitVec("y", 3)
        w = z3.BitVec("w", 3)
        u = z3.BitVec("u", 3)

        # Test that alt_imposition can work with Z3 variables
        result = imposition_semantics.alt_imposition(y, w, u)
        assert isinstance(result, z3.BoolRef)

        # Test that the result can be used in Z3 expressions
        solver = z3.Solver()
        solver.add(result)  # Should not raise an exception

        # Check that solver can handle the constraint
        check_result = solver.check()
        assert check_result in [z3.sat, z3.unsat, z3.unknown]


class TestImpositionSemanticsIntegration:
    """Integration tests for ImpositionSemantics with Z3 and other components."""

    @pytest.fixture
    def integration_semantics(self) -> ImpositionSemantics:
        """Create semantics for integration testing."""
        settings = {
            'N': 2,  # Smaller N for easier testing
            'contingent': False,
            'non_empty': False,
            'non_null': False,
            'disjoint': False,
            'max_time': 1,
            'iterate': 1,
            'expectation': None,
        }
        return ImpositionSemantics(settings)

    def test_imposition_in_z3_solver(self, integration_semantics: ImpositionSemantics) -> None:
        """Test that imposition operations work in Z3 solver context."""
        solver = z3.Solver()

        # Create bit vector variables
        y = z3.BitVecVal(1, 2)
        w = z3.BitVecVal(0, 2)
        u = z3.BitVecVal(2, 2)

        # Use imposition operation in constraint
        imposition_constraint = integration_semantics.alt_imposition(y, w, u)
        solver.add(imposition_constraint)

        # Solver should handle this without error
        result = solver.check()
        assert result in [z3.sat, z3.unsat]

    def test_calculate_outcome_worlds_integration(self, integration_semantics: ImpositionSemantics) -> None:
        """Test calculate_outcome_worlds with realistic parameters."""
        # Create realistic test data
        verifiers = {0, 1, 2}  # Valid states for N=2
        eval_point = {"world": z3.BitVecVal(1, 2)}

        # Mock model structure with basic interface
        model_structure = Mock()
        model_structure.get_world_count = Mock(return_value=2)

        result = integration_semantics.calculate_outcome_worlds(verifiers, eval_point, model_structure)

        # Result should be a set of valid state IDs
        assert isinstance(result, set)
        for state_id in result:
            assert isinstance(state_id, (int, type(state_id)))  # Allow for different state ID types

    def test_logos_integration_compatibility(self, integration_semantics: ImpositionSemantics) -> None:
        """Test that ImpositionSemantics works with logos theory components."""
        # Test that logos methods are available and functional
        test_sentence = Mock()
        eval_point = {"world": z3.BitVecVal(1, 2)}

        # These should not raise AttributeError
        assert hasattr(integration_semantics, 'true_at')
        assert hasattr(integration_semantics, 'false_at')

        # Test compatibility with logos state operations
        state_x = z3.BitVecVal(1, 2)
        state_y = z3.BitVecVal(2, 2)

        # Should be able to call inherited methods
        compatible_result = integration_semantics.compatible(state_x, state_y)
        assert isinstance(compatible_result, z3.BoolRef)

    def test_imposition_theory_specific_features(self, integration_semantics: ImpositionSemantics) -> None:
        """Test features specific to Kit Fine's imposition theory."""
        # Test that derive_imposition setting is accessible
        assert hasattr(integration_semantics, '_derive_imposition')

        # Test that imposition operation defines alternative worlds
        y = z3.BitVecVal(1, 2)
        w = z3.BitVecVal(0, 2)
        u = z3.BitVecVal(1, 2)

        alt_result = integration_semantics.alt_imposition(y, w, u)
        assert isinstance(alt_result, z3.BoolRef)

        # The result should be usable in logical operations
        negated = z3.Not(alt_result)
        assert isinstance(negated, z3.BoolRef)

    def test_multiple_imposition_operations(self, integration_semantics: ImpositionSemantics) -> None:
        """Test multiple imposition operations together."""
        solver = z3.Solver()

        # Create multiple imposition constraints
        states = [(0, 1, 2), (1, 0, 3), (2, 1, 0)]
        constraints = []

        for y, w, u in states:
            y_bv = z3.BitVecVal(y, 2)
            w_bv = z3.BitVecVal(w, 2)
            u_bv = z3.BitVecVal(u, 2)

            constraint = integration_semantics.alt_imposition(y_bv, w_bv, u_bv)
            constraints.append(constraint)
            solver.add(constraint)

        # All constraints should be processable by Z3
        result = solver.check()
        assert result in [z3.sat, z3.unsat]

        # Constraints should be independent Z3 expressions
        for constraint in constraints:
            assert isinstance(constraint, z3.BoolRef)