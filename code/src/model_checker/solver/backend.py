"""Centralized backend module access.

This module provides a single source of truth for accessing the active
solver backend module (z3 or cvc5.pythonic). It caches the module for
performance and registers with the lifecycle system for automatic
cache invalidation when backends are switched.

Usage:
    from model_checker.solver.backend import get_backend_module

    # Get the active backend module
    backend = get_backend_module()

    # Use it like z3 or cvc5.pythonic
    solver = backend.Solver()
    x = backend.BitVec('x', 32)
"""

from typing import Any, Optional
import importlib

# Cached backend module and the backend name it was cached for
_cached_module: Optional[Any] = None
_cached_backend: Optional[str] = None


def get_backend_module() -> Any:
    """Get the backend module (z3 or cvc5.pythonic), caching for performance.

    This function lazily loads and caches the appropriate backend module
    based on the currently active backend. The cache is automatically
    invalidated when the backend is switched via lifecycle hooks.

    Returns:
        The z3 module or cvc5.pythonic module, depending on active backend.

    Raises:
        ImportError: If the required backend module cannot be imported.
    """
    global _cached_module, _cached_backend

    # Import here to avoid circular imports
    from .registry import get_active_backend

    backend = get_active_backend()

    # Return cached module if backend hasn't changed
    if _cached_module is not None and _cached_backend == backend:
        return _cached_module

    # Load the appropriate module
    if backend == "z3":
        _cached_module = importlib.import_module("z3")
    elif backend == "cvc5":
        _cached_module = importlib.import_module("cvc5.pythonic")
    else:
        raise ValueError(f"Unknown solver backend: {backend}")

    _cached_backend = backend
    return _cached_module


def reset_backend_cache() -> None:
    """Reset the cached backend module.

    This is called by the lifecycle system when backends are switched.
    It should not typically be called directly; use
    lifecycle.set_backend_with_invalidation() instead.
    """
    global _cached_module, _cached_backend
    _cached_module = None
    _cached_backend = None


def get_cached_backend_name() -> Optional[str]:
    """Get the name of the currently cached backend (for debugging).

    Returns:
        The backend name ("z3" or "cvc5") if cached, None otherwise.
    """
    return _cached_backend


# Register with lifecycle system
# This import is at module scope, so it happens on first import of this module
from .lifecycle import register_cache_hook
register_cache_hook(reset_backend_cache)
