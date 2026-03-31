"""Transitional import shim for z3 module.

This module enables gradual migration from direct z3 imports to the
solver abstraction layer. Replace:
    from z3 import And, Or, BitVec
with:
    from model_checker.z3_shim import And, Or, BitVec

The actual implementation comes from either z3 or cvc5.pythonic
depending on the active backend.

Note: This shim is transitional. After migration is complete,
imports should use model_checker.solver.expressions instead.
"""

from model_checker.solver import get_active_backend
import importlib
from typing import Any

_backend_module: Any = None


def __getattr__(name: str) -> Any:
    """Lazily load attributes from the active backend module.

    This allows 'from model_checker.z3_shim import X' to work
    for any name X that exists in the backend module.

    Args:
        name: The attribute name to look up.

    Returns:
        The attribute from the active backend module.

    Raises:
        AttributeError: If the attribute doesn't exist in the backend.
    """
    global _backend_module

    if _backend_module is None:
        backend = get_active_backend()
        if backend == "z3":
            _backend_module = importlib.import_module("z3")
        elif backend == "cvc5":
            _backend_module = importlib.import_module("cvc5.pythonic")
        else:
            raise ValueError(f"Unknown solver backend: {backend}")

    return getattr(_backend_module, name)


def __dir__() -> list:
    """Return list of available attributes.

    This makes tab-completion work in interactive environments.

    Returns:
        List of attribute names from z3 module (for documentation).
    """
    import z3
    return dir(z3)


def _reset_backend() -> None:
    """Reset the cached backend module.

    This is called by the lifecycle system when backends are switched.
    It can also be used directly in testing.
    """
    global _backend_module
    _backend_module = None


# Register cache invalidation with lifecycle system
# This ensures _reset_backend is called when backend is switched
from model_checker.solver.lifecycle import register_cache_hook
register_cache_hook(_reset_backend)
