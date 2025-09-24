"""
Theory library error handling framework.

Follows ERROR_HANDLING.md standards for user-friendly messages
and actionable error context.
"""

from enum import Enum
from typing import Dict, Any, Optional, List





class ErrorSeverity(Enum):
    """Error severity levels."""
    WARNING = "warning"
    ERROR = "error"
    CRITICAL = "critical"


class TheoryError(Exception):
    """
    Base exception for theory library.

    Provides rich context for debugging and recovery following
    the user-friendly error message standards from CODE_STANDARDS.md.
    """
    def __init__(
        self,
        message: str,
        theory: Optional[str] = None,
        severity: ErrorSeverity = ErrorSeverity.ERROR,
        context: Optional[Dict[str, Any]] = None,
        suggestion: Optional[str] = None,
        related_errors: Optional[List[Exception]] = None
    ):
        super().__init__(message)
        self.theory = theory
        self.severity = severity
        self.context = context or {}
        self.suggestion = suggestion
        self.related_errors = related_errors or []

    def __str__(self) -> str:
        """Format error with context and suggestions per standards."""
        parts = [str(self.args[0])]
        if self.theory:
            parts.append(f"Theory: {self.theory}")
        if self.severity != ErrorSeverity.ERROR:
            parts.append(f"Severity: {self.severity.value}")
        if self.suggestion:
            parts.append(f"Suggestion: {self.suggestion}")
        return " | ".join(parts)


# Specific error hierarchy following single responsibility principle
class TheoryLoadError(TheoryError):
    """Theory cannot be loaded."""
    pass


class TheoryNotFoundError(TheoryLoadError):
    """Theory module not found with helpful suggestion."""

    def __init__(self, theory_name: str, available_theories: Optional[List[str]] = None):
        context = {"requested_theory": theory_name}
        if available_theories:
            context["available_theories"] = available_theories
            suggestion = f"Available theories: {', '.join(available_theories)}"
        else:
            suggestion = "Check theory name spelling and ensure it's installed"

        super().__init__(
            f"Theory '{theory_name}' not found",
            context=context,
            suggestion=suggestion
        )


class TheoryConfigurationError(TheoryError):
    """Theory misconfiguration with specific guidance."""
    pass


# Semantic Errors
class SemanticError(TheoryError):
    """Base for semantic errors."""
    pass


class SemanticValidationError(SemanticError):
    """Semantic validation failed with actionable feedback."""
    pass


class ModelConstructionError(SemanticError):
    """Model construction failed with construction context."""
    pass


# Formula Errors
class FormulaError(TheoryError):
    """Base for formula errors."""
    pass


class FormulaParsingError(FormulaError):
    """Formula parsing failed with syntax guidance."""
    pass


class FormulaValidationError(FormulaError):
    """Formula validation failed with correction suggestions."""
    pass


# Operator Errors following clear error pattern
class OperatorError(TheoryError):
    """Base for operator errors."""
    pass


class UnknownOperatorError(OperatorError):
    """Unknown operator with available operators list."""

    def __init__(self, operator: str, available_operators: Optional[List[str]] = None):
        context = {"unknown_operator": operator}
        if available_operators:
            context["available_operators"] = available_operators
            suggestion = f"Use one of: {', '.join(available_operators)}"
        else:
            suggestion = "Check operator spelling or theory documentation"

        super().__init__(
            f"Unknown operator '{operator}'",
            context=context,
            suggestion=suggestion
        )


class OperatorArityError(OperatorError):
    """Wrong number of arguments with expected arity."""
    pass


# Theory-specific errors
class SubtheoryError(TheoryError):
    """Base for subtheory errors."""
    pass


class SubtheoryLoadError(SubtheoryError):
    """Subtheory loading failed."""
    pass


class SubtheoryConflictError(SubtheoryError):
    """Subtheory conflict detected."""
    pass


class WitnessError(TheoryError):
    """Base for witness errors (exclusion-specific)."""
    pass


class WitnessNotFoundError(WitnessError):
    """Required witness not found."""
    pass


class ConstraintError(TheoryError):
    """Base for constraint errors."""
    pass


class UnsatisfiableError(ConstraintError):
    """Constraints are unsatisfiable."""
    pass