"""
Unit tests for theory library error handling.

Tests the standardized error hierarchy and error handling patterns
implemented across all theory modules.
"""

import pytest
import z3
from unittest.mock import Mock, patch

from model_checker.theory_lib.errors import (
    TheoryError,
    WitnessSemanticError,
    WitnessRegistryError,
    WitnessPredicateError,
    WitnessConstraintError,
    ImpositionSemanticError,
    ImpositionOperationError,
    ImpositionHelperError,
    LogosSubtheoryError,
    LogosProtocolError,
    Z3IntegrationError,
    Z3TimeoutError
)


class TestTheoryErrorHierarchy:
    """Test the base error hierarchy."""

    def test_theory_error_basic_creation(self):
        """Test basic TheoryError creation."""
        error = TheoryError("Test error message")
        assert str(error) == "Test error message"
        assert error.theory is None
        assert error.context == {}

    def test_theory_error_with_context(self):
        """Test TheoryError with context and suggestion."""
        context = {"param1": "value1", "param2": 42}
        error = TheoryError(
            "Test error",
            theory="test",
            context=context,
            suggestion="Try this fix"
        )

        error_str = str(error)
        assert "Test error" in error_str
        assert "Theory: test" in error_str
        assert "Suggestion: Try this fix" in error_str
        assert error.context == context


class TestWitnessErrorHandling:
    """Test witness theory (exclusion) error handling."""

    def test_witness_semantic_error_inherits_theory(self):
        """Test that WitnessSemanticError sets theory correctly."""
        error = WitnessSemanticError("Test witness error")
        assert error.theory == "exclusion"

    def test_witness_predicate_error_construction(self):
        """Test WitnessPredicateError construction."""
        error = WitnessPredicateError("test_formula", "registration")

        assert "test_formula" in str(error)
        assert "registration" in str(error)
        assert error.context['predicate_name'] == "test_formula"
        assert error.context['operation'] == "registration"

    def test_witness_registry_error_basic(self):
        """Test basic WitnessRegistryError."""
        error = WitnessRegistryError("Registry operation failed")
        assert error.theory == "exclusion"
        assert "Registry operation failed" in str(error)

    def test_witness_constraint_error_basic(self):
        """Test basic WitnessConstraintError."""
        error = WitnessConstraintError("Constraint generation failed")
        assert error.theory == "exclusion"
        assert "Constraint generation failed" in str(error)


class TestImpositionErrorHandling:
    """Test imposition theory error handling."""

    def test_imposition_semantic_error_inherits_theory(self):
        """Test that ImpositionSemanticError sets theory correctly."""
        error = ImpositionSemanticError("Test imposition error")
        assert error.theory == "imposition"

    def test_imposition_operation_error_basic(self):
        """Test basic ImpositionOperationError."""
        error = ImpositionOperationError("Imposition operation failed")
        assert error.theory == "imposition"
        assert "Imposition operation failed" in str(error)

    def test_imposition_helper_error_construction(self):
        """Test ImpositionHelperError construction."""
        error = ImpositionHelperError("safe_bitvec_as_long")

        assert "safe_bitvec_as_long" in str(error)
        assert error.context['function_name'] == "safe_bitvec_as_long"


class TestLogosErrorHandling:
    """Test logos theory error handling."""

    def test_logos_subtheory_error_basic(self):
        """Test basic LogosSubtheoryError."""
        error = LogosSubtheoryError("Subtheory error", subtheory_name="test_sub")
        assert error.theory == "logos"
        assert error.subtheory_name == "test_sub"

    def test_logos_protocol_error_construction(self):
        """Test LogosProtocolError construction."""
        error = LogosProtocolError("TestProtocol", "missing method")

        assert "TestProtocol" in str(error)
        assert "missing method" in str(error)
        assert error.context['protocol_name'] == "TestProtocol"
        assert error.context['compliance_issue'] == "missing method"


class TestZ3IntegrationErrorHandling:
    """Test Z3 integration error handling."""

    def test_z3_integration_error_with_status(self):
        """Test Z3IntegrationError with Z3 status."""
        error = Z3IntegrationError("Z3 operation failed", z3_status="unsat")
        assert error.context['z3_status'] == "unsat"

    def test_z3_timeout_error_construction(self):
        """Test Z3TimeoutError construction."""
        error = Z3TimeoutError(30.5)

        assert "30.5 seconds" in str(error)
        assert error.context['timeout_seconds'] == 30.5
        assert "increasing max_time" in error.suggestion


class TestErrorHandlingIntegration:
    """Test error handling integration with actual modules."""

    def test_witness_registry_error_on_invalid_formula(self):
        """Test that WitnessRegistry raises errors appropriately."""
        from model_checker.theory_lib.exclusion.semantic.registry import WitnessRegistry

        registry = WitnessRegistry(3)

        # Test with invalid formula string
        with pytest.raises(WitnessPredicateError) as exc_info:
            registry.register_witness_predicates("")

        assert "registration" in str(exc_info.value)
        assert exc_info.value.theory == "exclusion"

    def test_witness_registry_error_on_duplicate_registration(self):
        """Test that WitnessRegistry raises error on duplicate registration."""
        from model_checker.theory_lib.exclusion.semantic.registry import WitnessRegistry

        registry = WitnessRegistry(3)

        # First registration should succeed
        registry.register_witness_predicates("test_formula")

        # Second registration should fail
        with pytest.raises(WitnessRegistryError) as exc_info:
            registry.register_witness_predicates("test_formula")

        assert "already registered" in str(exc_info.value)
        assert exc_info.value.theory == "exclusion"

    def test_witness_registry_error_on_missing_retrieval(self):
        """Test that WitnessRegistry raises error when retrieving non-existent predicates."""
        from model_checker.theory_lib.exclusion.semantic.registry import WitnessRegistry

        registry = WitnessRegistry(3)

        with pytest.raises(WitnessPredicateError) as exc_info:
            registry.get_witness_predicates("nonexistent_formula")

        assert "retrieval" in str(exc_info.value)
        assert exc_info.value.theory == "exclusion"

    def test_imposition_helper_error_on_invalid_bitvec(self):
        """Test that imposition helpers raise errors appropriately."""
        from model_checker.theory_lib.imposition.semantic.helpers import safe_bitvec_as_long

        # Mock an object that will fail on .as_long()
        mock_bitvec = Mock()
        mock_bitvec.as_long.side_effect = AttributeError("Invalid bitvec")

        with pytest.raises(ImpositionHelperError) as exc_info:
            safe_bitvec_as_long(mock_bitvec)

        assert "safe_bitvec_as_long" in str(exc_info.value)
        assert exc_info.value.theory == "imposition"

    def test_imposition_operation_error_on_null_parameters(self):
        """Test that imposition operations raise errors on null parameters."""
        from model_checker.theory_lib.imposition.semantic.core import ImpositionSemantics

        # Create minimal settings
        settings = {
            'N': 2,
            'max_time': 1,
            'iterate': 1
        }

        semantics = ImpositionSemantics(settings)

        # Test with None parameters
        with pytest.raises(ImpositionOperationError) as exc_info:
            semantics.alt_imposition(None, z3.BitVecVal(1, 2), z3.BitVecVal(2, 2))

        assert "Invalid state parameters" in str(exc_info.value)
        assert exc_info.value.theory == "imposition"

    def test_witness_constraint_error_on_invalid_formula(self):
        """Test that constraint generation raises errors appropriately."""
        from model_checker.theory_lib.exclusion.semantic.constraints import WitnessConstraintGenerator

        # Mock semantics
        mock_semantics = Mock()
        mock_semantics.N = 3

        generator = WitnessConstraintGenerator(mock_semantics)

        # Test with empty formula string
        with pytest.raises(WitnessConstraintError) as exc_info:
            generator.generate_witness_constraints(
                "", Mock(), Mock(), Mock(), {}
            )

        assert "empty formula" in str(exc_info.value)
        assert exc_info.value.theory == "exclusion"

    def test_witness_constraint_error_on_null_predicates(self):
        """Test constraint generation with null predicates."""
        from model_checker.theory_lib.exclusion.semantic.constraints import WitnessConstraintGenerator

        mock_semantics = Mock()
        mock_semantics.N = 3

        generator = WitnessConstraintGenerator(mock_semantics)

        # Test with null predicates
        with pytest.raises(WitnessConstraintError) as exc_info:
            generator.generate_witness_constraints(
                "test_formula", Mock(), None, Mock(), {}
            )

        assert "Invalid witness predicates" in str(exc_info.value)
        assert exc_info.value.theory == "exclusion"


class TestErrorContextAndSuggestions:
    """Test that errors provide useful context and suggestions."""

    def test_error_context_preservation(self):
        """Test that error context is preserved through the hierarchy."""
        original_context = {'key1': 'value1', 'key2': 42}

        error = WitnessSemanticError(
            "Test error",
            context=original_context,
            suggestion="Test suggestion"
        )

        assert error.context == original_context
        assert error.suggestion == "Test suggestion"
        assert error.theory == "exclusion"

    def test_error_chaining_preserves_context(self):
        """Test that error chaining preserves context from original errors."""
        try:
            # Simulate an inner error
            raise ValueError("Original error")
        except ValueError as e:
            # Chain with theory error
            theory_error = ImpositionSemanticError(
                "Wrapper error",
                context={'wrapper_info': 'test'},
                suggestion="Check the original error"
            )
            theory_error.__cause__ = e

            assert theory_error.__cause__ is e
            assert theory_error.context['wrapper_info'] == 'test'
            assert theory_error.theory == "imposition"

    def test_error_suggestions_are_actionable(self):
        """Test that error suggestions provide actionable guidance."""
        timeout_error = Z3TimeoutError(60.0)
        assert "increasing max_time" in timeout_error.suggestion

        predicate_error = WitnessPredicateError("test", "registration")
        # Should have either a default suggestion or one from construction
        assert predicate_error.suggestion is None or len(predicate_error.suggestion) > 0