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
    WitnessError,
    WitnessRegistryError,
    WitnessPredicateError,
    WitnessConstraintError,
    SemanticError,
    Z3IntegrationError,
    Z3TimeoutError
)

# NOTE: theory-specific subclasses that this file previously imported
# (ImpositionSemanticError, ImpositionOperationError, ImpositionHelperError,
# LogosSubtheoryError, LogosProtocolError) do not exist anywhere in
# model_checker.theory_lib.errors or in the imposition/logos packages (which
# only use the generic SemanticError/SubtheoryError bases). Tests exercising
# those fictional classes were removed rather than repaired; see task 121's
# implementation summary for the per-file decision record.


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
    """Test witness error handling.

    The witness error hierarchy (WitnessError and its subclasses) is shared by
    the exclusion and bimodal theories, both of which raise these classes from
    their own witness-registry and witness-constraint modules. It carries no
    default theory tag; callers that know their theory pass it explicitly via
    the `theory=` keyword.
    """

    def test_witness_error_construction(self):
        """Test that WitnessError (the base witness exception) can be constructed
        with an explicit theory (the class itself does not default theory)."""
        error = WitnessError("Test witness error", theory="exclusion")
        assert error.theory == "exclusion"

    def test_witness_predicate_error_construction(self):
        """Test WitnessPredicateError construction."""
        error = WitnessPredicateError("test_formula", "registration")

        assert "test_formula" in str(error)
        assert "registration" in str(error)
        assert error.context['predicate_name'] == "test_formula"
        assert error.context['operation'] == "registration"

    def test_witness_registry_error_basic(self):
        """Test WitnessRegistryError constructed with an explicit theory.

        The class itself deliberately sets no theory default: it is shared by
        the exclusion and bimodal theories, both of which raise it from their
        own witness-registry modules (exclusion's `registry.py` and bimodal's
        `witness_registry.py`), so a baked-in theory label would mislabel one
        of them. Callers that know their theory pass it in.
        """
        error = WitnessRegistryError("Registry operation failed", theory="exclusion")
        assert error.theory == "exclusion"
        assert "Registry operation failed" in str(error)

    def test_witness_constraint_error_basic(self):
        """Test WitnessConstraintError constructed with an explicit theory.

        The class itself deliberately sets no theory default: it is shared by
        the exclusion and bimodal theories, both of which raise it from their
        own witness-constraint modules (exclusion's `constraints.py` and
        bimodal's `witness_constraints.py`), so a baked-in theory label would
        mislabel one of them. Callers that know their theory pass it in.
        """
        error = WitnessConstraintError("Constraint generation failed", theory="exclusion")
        assert error.theory == "exclusion"
        assert "Constraint generation failed" in str(error)


class TestImpositionErrorHandling:
    """Test imposition theory error handling using the generic SemanticError
    base (the imposition package's own modules only ever import/raise
    SemanticError from theory_lib.errors; no Imposition-specific subclasses
    exist in the current codebase)."""

    def test_semantic_error_with_imposition_theory(self):
        """Test that SemanticError carries an explicit imposition theory tag."""
        error = SemanticError("Test imposition error", theory="imposition")
        assert error.theory == "imposition"
        assert "Test imposition error" in str(error)


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


class TestErrorContextAndSuggestions:
    """Test that errors provide useful context and suggestions."""

    def test_error_context_preservation(self):
        """Test that error context is preserved through the hierarchy."""
        original_context = {'key1': 'value1', 'key2': 42}

        error = WitnessError(
            "Test error",
            theory="exclusion",
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
            theory_error = SemanticError(
                "Wrapper error",
                theory="imposition",
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