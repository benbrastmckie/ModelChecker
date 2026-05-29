"""
Z3 context management utilities.

This module provides ``isolated_z3_context()``, a context manager that swaps
``z3.z3._main_ctx`` to a fresh ``z3.Context()`` for the duration of a ``with``
block, providing true C-level isolation between examples. This is the
authoritative approach to preventing Z3 state leakage.
"""

from contextlib import contextmanager


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
