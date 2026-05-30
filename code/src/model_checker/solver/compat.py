"""Cross-solver compatibility helpers.

This module provides helper functions that work correctly with both
Z3 and cvc5 backends, handling API differences transparently.
"""

from typing import Any, Optional, TYPE_CHECKING

if TYPE_CHECKING:
    from .protocols import ModelProtocol


def _get_backend() -> str:
    """Get the active backend, using registry if no explicit backend provided."""
    from .registry import get_active_backend
    return get_active_backend()


def is_true(val: Any, backend: Optional[str] = None) -> bool:
    """Check if a value represents boolean true.

    Args:
        val: Value to check (from model evaluation or expression).
        backend: The active backend ("z3" or "cvc5"). Auto-detected if None.

    Returns:
        True if the value represents boolean true.
    """
    if backend is None:
        backend = _get_backend()
    if backend == "z3":
        import z3
        if isinstance(val, z3.BoolRef):
            return z3.is_true(val)
        return bool(val)
    elif backend == "cvc5":
        # cvc5 pythonic returns Python bools or cvc5 BoolVal
        try:
            from cvc5.pythonic import is_true as cvc5_is_true
            return cvc5_is_true(val)
        except (ImportError, AttributeError):
            # Fallback to direct comparison
            return bool(val)
    return bool(val)


def is_false(val: Any, backend: Optional[str] = None) -> bool:
    """Check if a value represents boolean false.

    Args:
        val: Value to check (from model evaluation or expression).
        backend: The active backend ("z3" or "cvc5"). Auto-detected if None.

    Returns:
        True if the value represents boolean false.
    """
    if backend is None:
        backend = _get_backend()
    if backend == "z3":
        import z3
        if isinstance(val, z3.BoolRef):
            return z3.is_false(val)
        return not bool(val)
    elif backend == "cvc5":
        try:
            from cvc5.pythonic import is_false as cvc5_is_false
            return cvc5_is_false(val)
        except (ImportError, AttributeError):
            return not bool(val)
    return not bool(val)


def simplify(expr: Any, backend: Optional[str] = None) -> Any:
    """Simplify an expression.

    Args:
        expr: Expression to simplify.
        backend: The active backend ("z3" or "cvc5"). Auto-detected if None.

    Returns:
        Simplified expression.
    """
    if backend is None:
        backend = _get_backend()
    if backend == "z3":
        import z3
        return z3.simplify(expr)
    elif backend == "cvc5":
        # cvc5 pythonic provides simplify
        try:
            from cvc5.pythonic import simplify as cvc5_simplify
            return cvc5_simplify(expr)
        except (ImportError, AttributeError):
            # cvc5 may not have simplify in all versions
            return expr
    return expr


def eval_model(model: "ModelProtocol", expr: Any, backend: Optional[str] = None,
               model_completion: bool = False) -> Any:
    """Evaluate an expression in a model.

    Handles API differences between Z3's model.eval() and cvc5's model.evaluate().

    Args:
        model: The solver model.
        expr: Expression to evaluate.
        backend: The active backend ("z3" or "cvc5"). Auto-detected if None.
        model_completion: If True, provide values for unassigned variables.

    Returns:
        The value of the expression in the model.
    """
    if backend is None:
        backend = _get_backend()
    if backend == "z3":
        return model.eval(expr, model_completion=model_completion)
    elif backend == "cvc5":
        # cvc5 pythonic uses evaluate() or direct indexing
        if hasattr(model, 'evaluate'):
            return model.evaluate(expr)
        elif hasattr(model, '__getitem__'):
            return model[expr]
        return model.eval(expr)
    return model.eval(expr)


def get_bitvec_value(val: Any, backend: Optional[str] = None) -> int:
    """Extract an integer value from a bitvector constant.

    Args:
        val: A bitvector value from model evaluation.
        backend: The active backend ("z3" or "cvc5"). Auto-detected if None.

    Returns:
        Integer value of the bitvector.
    """
    if backend is None:
        backend = _get_backend()
    if backend == "z3":
        import z3
        if isinstance(val, z3.BitVecNumRef):
            return val.as_long()
        return int(str(val))
    elif backend == "cvc5":
        # cvc5 pythonic bitvectors have as_long() method
        if hasattr(val, 'as_long'):
            return val.as_long()
        # Try string conversion fallback
        val_str = str(val)
        if val_str.startswith("#x"):
            return int(val_str[2:], 16)
        elif val_str.startswith("#b"):
            return int(val_str[2:], 2)
        return int(val_str)
    return int(str(val))


def substitute(expr: Any, substitutions: dict, backend: Optional[str] = None) -> Any:
    """Substitute variables in an expression.

    Args:
        expr: Expression to substitute in.
        substitutions: Dict mapping variables to replacement expressions.
        backend: The active backend ("z3" or "cvc5"). Auto-detected if None.

    Returns:
        Expression with substitutions applied.
    """
    if backend is None:
        backend = _get_backend()
    if backend == "z3":
        import z3
        pairs = [(old, new) for old, new in substitutions.items()]
        return z3.substitute(expr, pairs)
    elif backend == "cvc5":
        try:
            from cvc5.pythonic import substitute as cvc5_substitute
            pairs = [(old, new) for old, new in substitutions.items()]
            return cvc5_substitute(expr, pairs)
        except (ImportError, AttributeError):
            # May need different approach for cvc5
            pass
    return expr
