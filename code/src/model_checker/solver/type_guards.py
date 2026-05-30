"""Runtime type checking for solver expressions.

This module provides assertions to catch type mismatches between solver
backends early. When a Z3 expression is accidentally passed to a CVC5
solver (or vice versa), these guards produce clear error messages that
help diagnose cache invalidation issues.

Usage:
    from model_checker.solver.type_guards import assert_backend_types

    # In CVC5SolverAdapter.add():
    def add(self, constraint):
        assert_backend_types(constraint, "cvc5")
        self._solver.add(constraint)
"""

from typing import Any


def assert_backend_types(constraint: Any, expected_backend: str) -> None:
    """Assert that constraint was built with expected backend types.

    This is a debugging aid that catches type mismatches early. When
    constraints are built with one backend's types (e.g., z3.BoolRef)
    but passed to another backend's solver (e.g., cvc5), this function
    raises a clear TypeError.

    Args:
        constraint: The constraint expression to check.
        expected_backend: The expected backend ("z3" or "cvc5").

    Raises:
        TypeError: If constraint was built with wrong backend types.
            The error message includes debugging hints about cache
            invalidation.

    Example:
        >>> import z3
        >>> from model_checker.solver.type_guards import assert_backend_types
        >>> constraint = z3.Bool('x')
        >>> assert_backend_types(constraint, "cvc5")
        TypeError: CVC5 backend received Z3 expression: BoolRef. ...
    """
    if expected_backend == "cvc5":
        _check_not_z3_type(constraint)
    elif expected_backend == "z3":
        _check_not_cvc5_type(constraint)


def _check_not_z3_type(constraint: Any) -> None:
    """Check that constraint is not a Z3 type.

    Args:
        constraint: Expression to check.

    Raises:
        TypeError: If constraint is a Z3 expression type.
    """
    try:
        import z3
    except ImportError:
        # Z3 not installed, so constraint can't be a Z3 type
        return

    # Check for common Z3 expression types
    z3_types = (
        z3.ExprRef,
        z3.BoolRef,
        z3.ArithRef,
        z3.BitVecRef,
    )

    # Also check SortRef for type declarations
    if hasattr(z3, 'SortRef'):
        z3_types = z3_types + (z3.SortRef,)

    if isinstance(constraint, z3_types):
        raise TypeError(
            f"CVC5 backend received Z3 expression: {type(constraint).__name__}. "
            "This indicates stale cached types from a previous backend session. "
            "Call lifecycle.set_backend_with_invalidation() to clear caches "
            "before switching backends."
        )


def _check_not_cvc5_type(constraint: Any) -> None:
    """Check that constraint is not a CVC5 type.

    Args:
        constraint: Expression to check.

    Raises:
        TypeError: If constraint is a CVC5 expression type.
    """
    try:
        import cvc5.pythonic as cvc5
    except ImportError:
        # CVC5 not installed, so constraint can't be a CVC5 type
        return

    # Check for CVC5 pythonic expression types
    cvc5_types = []

    if hasattr(cvc5, 'ExprRef'):
        cvc5_types.append(cvc5.ExprRef)
    if hasattr(cvc5, 'BoolRef'):
        cvc5_types.append(cvc5.BoolRef)
    if hasattr(cvc5, 'ArithRef'):
        cvc5_types.append(cvc5.ArithRef)
    if hasattr(cvc5, 'BitVecRef'):
        cvc5_types.append(cvc5.BitVecRef)
    if hasattr(cvc5, 'SortRef'):
        cvc5_types.append(cvc5.SortRef)

    if cvc5_types and isinstance(constraint, tuple(cvc5_types)):
        raise TypeError(
            f"Z3 backend received CVC5 expression: {type(constraint).__name__}. "
            "This indicates stale cached types from a previous backend session. "
            "Call lifecycle.set_backend_with_invalidation() to clear caches "
            "before switching backends."
        )


def is_z3_type(obj: Any) -> bool:
    """Check if object is a Z3 expression type.

    Args:
        obj: Object to check.

    Returns:
        True if obj is a Z3 expression type, False otherwise.
    """
    try:
        import z3
        return isinstance(obj, (z3.ExprRef, z3.SortRef))
    except ImportError:
        return False


def is_cvc5_type(obj: Any) -> bool:
    """Check if object is a CVC5 expression type.

    Args:
        obj: Object to check.

    Returns:
        True if obj is a CVC5 expression type, False otherwise.
    """
    try:
        import cvc5.pythonic as cvc5
        types_to_check = []
        if hasattr(cvc5, 'ExprRef'):
            types_to_check.append(cvc5.ExprRef)
        if hasattr(cvc5, 'SortRef'):
            types_to_check.append(cvc5.SortRef)
        return types_to_check and isinstance(obj, tuple(types_to_check))
    except ImportError:
        return False


def get_expression_backend(obj: Any) -> str:
    """Determine which backend an expression was created with.

    Args:
        obj: Expression to check.

    Returns:
        "z3", "cvc5", or "unknown" based on the expression type.
    """
    if is_z3_type(obj):
        return "z3"
    if is_cvc5_type(obj):
        return "cvc5"
    return "unknown"
