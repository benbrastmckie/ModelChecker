"""Backend lifecycle management for clean solver switching.

This module provides a hook-based system for cache invalidation when
the solver backend changes. Modules with cached backend-specific state
register their reset functions during import, and all hooks are called
atomically when set_backend_with_invalidation() is used.

Architecture:
    CLI/Settings -> set_backend_with_invalidation()
                        |
                        v
                    invalidate_all_caches()
                        |
        +---------------+---------------+
        |               |               |
        v               v               v
    z3_shim         atoms.py        backend.py
    reset hook      reset hook      reset hook
"""

from typing import Callable, List

# Registry of cache invalidation hooks
_cache_hooks: List[Callable[[], None]] = []


def register_cache_hook(hook: Callable[[], None]) -> None:
    """Register a function to call when backend changes.

    Modules with cached backend-specific state should register
    their reset function during import. The hook will be called
    whenever the backend is switched via set_backend_with_invalidation().

    Args:
        hook: A zero-argument function that resets cached state.

    Example:
        # In z3_shim.py
        from model_checker.solver.lifecycle import register_cache_hook

        def _reset_backend():
            global _backend_module
            _backend_module = None

        register_cache_hook(_reset_backend)
    """
    if hook not in _cache_hooks:
        _cache_hooks.append(hook)


def unregister_cache_hook(hook: Callable[[], None]) -> None:
    """Remove a registered cache hook (useful for testing).

    Args:
        hook: The hook function to remove.
    """
    if hook in _cache_hooks:
        _cache_hooks.remove(hook)


def invalidate_all_caches() -> None:
    """Invalidate all registered expression caches.

    Calls each registered hook in registration order. This is called
    automatically by set_backend_with_invalidation(), but can also be
    called directly if needed.
    """
    for hook in _cache_hooks:
        hook()


def set_backend_with_invalidation(backend: str) -> None:
    """Set backend and invalidate all caches atomically.

    This is the primary entry point for backend switching from CLI
    flags, settings, or any other source. It ensures that:
    1. All cached backend-specific state is cleared first
    2. Then the backend is switched in the registry

    Args:
        backend: The backend name ("z3" or "cvc5").

    Raises:
        ValueError: If backend is not a valid name.
    """
    # Invalidate caches BEFORE switching backend to ensure
    # no stale types are used after the switch
    invalidate_all_caches()

    # Import here to avoid circular imports
    from .registry import set_cli_backend
    set_cli_backend(backend)


def get_registered_hooks() -> List[Callable[[], None]]:
    """Get list of registered hooks (useful for testing/debugging).

    Returns:
        List of registered hook functions.
    """
    return list(_cache_hooks)


def clear_all_hooks() -> None:
    """Clear all registered hooks (useful for testing).

    Warning: This should only be used in test teardown, never in
    production code.
    """
    _cache_hooks.clear()
