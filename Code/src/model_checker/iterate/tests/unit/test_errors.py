"""Unit tests for iterate package error classes."""

import pytest
from model_checker.iterate.errors import (
    IterateError,
    IterationLimitError,
    IterationStateError,
    ModelExtractionError,
    ConstraintGenerationError,
    IsomorphismCheckError,
    IterationTimeoutError,
    ModelValidationError
)


class TestIterateError:
    """Test base IterateError class."""
    
    def test_basic_error_creation(self):
        """Test creating basic error with message."""
        error = IterateError("Test error message")
        assert str(error) == "Test error message"
        assert error.context == {}
    
    def test_error_with_context(self):
        """Test creating error with context."""
        context = {"key": "value", "number": 42}
        error = IterateError("Test error", context)
        assert "Test error" in str(error)
        assert "key=value" in str(error)
        assert "number=42" in str(error)
        assert error.context == context
    
    def test_error_string_representation(self):
        """Test string representation with context."""
        error = IterateError("Message", {"a": 1, "b": "test"})
        result = str(error)
        assert "Message" in result
        assert "[Context:" in result
        assert "a=1" in result
        assert "b=test" in result


class TestIterationLimitError:
    """Test IterationLimitError class."""
    
    def test_basic_limit_error(self):
        """Test basic limit error."""
        error = IterationLimitError(limit=5, found=3)
        assert "limit of 5" in str(error)
        assert "found 3" in str(error)
        assert error.context["limit"] == 5
        assert error.context["found"] == 3
    
    def test_limit_error_with_reason(self):
        """Test limit error with reason."""
        error = IterationLimitError(limit=10, found=7, reason="timeout occurred")
        assert "limit of 10" in str(error)
        assert "found 7" in str(error)
        assert "timeout occurred" in str(error)
        assert error.context["reason"] == "timeout occurred"


class TestIterationStateError:
    """Test IterationStateError class."""
    
    def test_basic_state_error(self):
        """Test basic state error."""
        error = IterationStateError(
            state="initialization",
            reason="missing model"
        )
        assert "Invalid iteration state 'initialization'" in str(error)
        assert "missing model" in str(error)
        assert error.context["state"] == "initialization"
        assert error.context["reason"] == "missing model"
    
    def test_state_error_with_suggestion(self):
        """Test state error with suggestion."""
        error = IterationStateError(
            state="settings_validation",
            reason="invalid timeout",
            suggestion="Set timeout to a positive value"
        )
        assert "Invalid iteration state 'settings_validation'" in str(error)
        assert "invalid timeout" in str(error)
        assert "Set timeout to a positive value" in str(error)
        assert error.context["suggestion"] == "Set timeout to a positive value"


class TestModelExtractionError:
    """Test ModelExtractionError class."""
    
    def test_basic_extraction_error(self):
        """Test basic extraction error."""
        error = ModelExtractionError(
            model_num=3,
            reason="Z3 solver failed"
        )
        assert "Failed to extract model 3" in str(error)
        assert "Z3 solver failed" in str(error)
        assert error.context["model_num"] == 3
    
    def test_extraction_error_with_suggestion(self):
        """Test extraction error with suggestion."""
        error = ModelExtractionError(
            model_num=5,
            reason="incomplete model",
            suggestion="Check constraint satisfaction"
        )
        assert "model 5" in str(error)
        assert "incomplete model" in str(error)
        assert "Check constraint satisfaction" in str(error)


class TestConstraintGenerationError:
    """Test ConstraintGenerationError class."""
    
    def test_basic_constraint_error(self):
        """Test basic constraint error."""
        error = ConstraintGenerationError(
            constraint_type="exclusion",
            reason="invalid formula"
        )
        assert "Failed to generate exclusion constraint" in str(error)
        assert "invalid formula" in str(error)
        assert error.context["type"] == "exclusion"
    
    def test_constraint_error_with_model_num(self):
        """Test constraint error with model number."""
        error = ConstraintGenerationError(
            constraint_type="difference",
            reason="state mismatch",
            model_num=7
        )
        assert "difference constraint for model 7" in str(error)
        assert "state mismatch" in str(error)
        assert error.context["model_num"] == 7


class TestIsomorphismCheckError:
    """Test IsomorphismCheckError class."""
    
    def test_isomorphism_error(self):
        """Test isomorphism check error."""
        error = IsomorphismCheckError(
            model1=2,
            model2=4,
            reason="graph construction failed"
        )
        assert "Isomorphism check failed between models 2 and 4" in str(error)
        assert "graph construction failed" in str(error)
        assert error.context["model1"] == 2
        assert error.context["model2"] == 4
        assert error.context["reason"] == "graph construction failed"


class TestIterationTimeoutError:
    """Test IterationTimeoutError class."""
    
    def test_timeout_error(self):
        """Test timeout error."""
        error = IterationTimeoutError(
            timeout=30.0,
            elapsed=35.5,
            models_found=3
        )
        assert "timeout (30.0s)" in str(error)
        assert "35.50s" in str(error)
        assert "3 models found" in str(error)
        assert error.context["timeout"] == 30.0
        assert error.context["elapsed"] == 35.5
        assert error.context["models_found"] == 3


class TestModelValidationError:
    """Test ModelValidationError class."""
    
    def test_validation_error(self):
        """Test model validation error."""
        error = ModelValidationError(
            model_num=6,
            validation_error="no world states"
        )
        assert "Model 6 failed validation" in str(error)
        assert "no world states" in str(error)
        assert error.context["model_num"] == 6
        assert error.context["validation_error"] == "no world states"