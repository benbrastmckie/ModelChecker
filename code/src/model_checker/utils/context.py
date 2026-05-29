"""
Z3 context management utilities.

This module provides centralized management of Z3 solver contexts to ensure
proper isolation between different solver instances. The primary interface is
``isolated_z3_context()``, a context manager that swaps ``z3.z3._main_ctx``
to a fresh ``z3.Context()`` for the duration of a ``with`` block, providing
true C-level isolation between examples.
"""

from contextlib import contextmanager
from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from model_checker import z3_shim as z3


@contextmanager
def isolated_z3_context():
    """Context manager that provides a fresh Z3 C-level context for each example.

    Swaps ``z3.z3._main_ctx`` (the actual C-level context pointer) to a brand-new
    ``z3.Context()`` on entry, then restores the original on exit. This is the
    authoritative fix for Z3 solver state leakage: learned lemmas, caches, and
    heuristic seeds accumulated inside the ``with`` block are discarded when the
    block exits, ensuring deterministic results across examples.

    The ``AtomSort`` cache is cleared both before yielding (to avoid using a
    stale sort tied to the old context) and after restoring (to clear any sort
    created inside the fresh context that must not escape).

    Usage::

        with isolated_z3_context():
            process_example(...)
    """
    import z3 as _z3_pkg
    import z3.z3 as _z3_inner

    # Import reset_atom_sort, tolerating early-bootstrap absence
    try:
        from model_checker.syntactic.atoms import reset_atom_sort
    except (ImportError, AttributeError):
        reset_atom_sort = None

    # Save the current C-level context
    saved_ctx = _z3_inner._main_ctx

    # Create a fresh context and install it
    fresh_ctx = _z3_pkg.Context()
    _z3_inner._main_ctx = fresh_ctx

    # Clear AtomSort so it is rebuilt inside the fresh context
    if reset_atom_sort is not None:
        reset_atom_sort()

    try:
        yield
    finally:
        # Clear AtomSort created inside the fresh context before restoring
        if reset_atom_sort is not None:
            reset_atom_sort()
        # Restore the original context
        _z3_inner._main_ctx = saved_ctx


class Z3ContextManager:
    """Provides centralized management of Z3 solver contexts.
    
    This class ensures proper isolation between different solver instances by explicitly
    resetting the Z3 global context when needed. It implements a fail-fast approach
    and enforces deterministic behavior by preventing state leakage between examples.
    """
    
    def reset_context(self) -> None:
        """Explicitly reset the Z3 global context.
        
        This method forces Z3 to create a fresh context for the next solver instance,
        ensuring complete isolation between different examples.
        
        Note: Z3 stores its context in either '_main_ctx' or 'main_ctx' depending on
        the Z3 version. This method handles both cases for maximum compatibility.
        """
        from model_checker import z3_shim as z3

        # Handle both possible attribute names for Z3 context
        if hasattr(z3, '_main_ctx'):
            # Reset the context completely
            z3._main_ctx = None
            
        elif hasattr(z3, 'main_ctx'):
            z3.main_ctx = None
            
        # Try to clear other Z3 caches that might persist
        if hasattr(z3, 'clear_parser_cache'):
            z3.clear_parser_cache()
            
        # Re-import z3 to use the new context
        import importlib
        importlib.reload(z3)


def reset_z3_context() -> None:
    """Explicitly reset the Z3 global context.

    This function forces Z3 to create a fresh context for the next solver instance,
    ensuring complete isolation between different examples.

    Note: Z3 stores its context in either '_main_ctx' or 'main_ctx' depending on
    the Z3 version. This function handles both cases for maximum compatibility.

    This function is now a thin wrapper around reset_solver_context() for
    backwards compatibility.
    """
    reset_solver_context()


def reset_solver_context() -> None:
    """Reset solver context for complete isolation between examples.

    This unified function handles context reset for all supported backends (z3, cvc5).
    It also resets the AtomSort cache to ensure fresh sorts are created after backend
    switching.
    """
    from model_checker.solver.registry import get_active_backend

    backend = get_active_backend()

    # Backend-specific reset
    if backend == "z3":
        import z3

        # Handle both possible attribute names for Z3 context
        if hasattr(z3, '_main_ctx'):
            z3._main_ctx = None
        elif hasattr(z3, 'main_ctx'):
            z3.main_ctx = None

        # Try to clear other Z3 caches that might persist
        if hasattr(z3, 'clear_parser_cache'):
            z3.clear_parser_cache()

        # Re-import z3 to use the new context
        import importlib
        importlib.reload(z3)
    elif backend == "cvc5":
        # cvc5 typically doesn't need explicit context reset
        # The TermManager handles its own state
        pass

    # Reset AtomSort cache for fresh sort creation after backend switch
    try:
        from model_checker.syntactic.atoms import reset_atom_sort
        reset_atom_sort()
    except (ImportError, AttributeError):
        # reset_atom_sort may not exist yet during early bootstrap
        pass