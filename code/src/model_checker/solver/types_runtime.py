"""Runtime type references from the active solver backend.

This module provides runtime-importable type aliases that resolve to
the correct backend's types. Unlike types.py (which uses TYPE_CHECKING
guards for static analysis), these are actual classes usable with
isinstance() checks and exception handling at runtime.

Usage:
    from model_checker.solver.types_runtime import BoolRef, ExprRef, SolverException

    if isinstance(expr, BoolRef):
        ...

    try:
        solver.check()
    except SolverException:
        ...
"""

from typing import Any


def _get_backend_module():
    """Get the appropriate backend module."""
    from .registry import get_active_backend
    backend = get_active_backend()
    if backend == "z3":
        import z3
        return z3
    elif backend == "cvc5":
        try:
            import cvc5.pythonic as cvc5_pythonic
            return cvc5_pythonic
        except ImportError:
            raise ImportError("cvc5 not installed. Install with: pip install cvc5")
    raise ValueError(f"Unknown backend: {backend}")


class _LazyType:
    """Descriptor that lazily resolves to a backend type.

    Allows isinstance() checks and exception handling to work
    with the active backend's types.
    """

    def __init__(self, z3_name: str, cvc5_name: str = None):
        self._z3_name = z3_name
        self._cvc5_name = cvc5_name or z3_name

    def _resolve(self):
        from .registry import get_active_backend
        backend = get_active_backend()
        if backend == "z3":
            import z3
            return getattr(z3, self._z3_name)
        elif backend == "cvc5":
            try:
                import cvc5.pythonic as cvc5_p
                return getattr(cvc5_p, self._cvc5_name, type(None))
            except ImportError:
                return type(None)
        return type(None)


# We use module-level __getattr__ for lazy resolution of type references.
# This allows `from model_checker.solver.types_runtime import BoolRef` to work,
# and isinstance(expr, BoolRef) to resolve at call time.

_TYPE_MAP = {
    # Expression reference types
    "BoolRef": ("BoolRef", "BoolRef"),
    "BitVecRef": ("BitVecRef", "BitVecRef"),
    "BitVecNumRef": ("BitVecNumRef", "BitVecNumRef"),
    "ExprRef": ("ExprRef", "ExprRef"),
    "ArithRef": ("ArithRef", "ArithRef"),
    "ArrayRef": ("ArrayRef", "ArrayRef"),
    "SeqRef": ("SeqRef", "SeqRef"),
    # Sort reference types
    "SortRef": ("SortRef", "SortRef"),
    "BitVecSortRef": ("BitVecSortRef", "BitVecSortRef"),
    "BoolSortRef": ("BoolSortRef", "BoolSortRef"),
    # Function and model types
    "FuncDeclRef": ("FuncDeclRef", "FuncDeclRef"),
    "ModelRef": ("ModelRef", "ModelRef"),
    # Result type
    "CheckSatResult": ("CheckSatResult", "CheckSatResult"),
    # Quantifier type
    "QuantifierRef": ("QuantifierRef", "QuantifierRef"),
}

# Exception mapping
_EXCEPTION_MAP = {
    "Z3Exception": "Z3Exception",
}


class SolverException(Exception):
    """Backend-agnostic solver exception.

    Wraps Z3Exception and cvc5 exceptions into a unified type.
    Can also be used directly in except clauses alongside the
    native backend exception.
    """
    pass


def get_native_exception():
    """Get the native exception class for the active backend.

    Returns:
        The exception class (z3.Z3Exception or cvc5 equivalent).
    """
    from .registry import get_active_backend
    backend = get_active_backend()
    if backend == "z3":
        import z3
        return z3.Z3Exception
    elif backend == "cvc5":
        try:
            import cvc5.pythonic as cvc5_p
            return getattr(cvc5_p, "CVC5Exception", Exception)
        except ImportError:
            return Exception
    return Exception


def __getattr__(name: str) -> Any:
    """Lazily resolve type references from the active backend.

    This allows:
        from model_checker.solver.types_runtime import BoolRef
        isinstance(expr, BoolRef)  # works at runtime
    """
    if name in _TYPE_MAP:
        z3_name, cvc5_name = _TYPE_MAP[name]
        from .registry import get_active_backend
        backend = get_active_backend()
        if backend == "z3":
            import z3
            return getattr(z3, z3_name)
        elif backend == "cvc5":
            try:
                import cvc5.pythonic as cvc5_p
                return getattr(cvc5_p, cvc5_name, type(None))
            except ImportError:
                return type(None)
        return type(None)

    if name == "Z3Exception":
        return get_native_exception()

    raise AttributeError(f"module {__name__!r} has no attribute {name!r}")
