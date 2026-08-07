"""Single-threaded-only model-construction guard.

Model construction (semantics, constraints, and solving) builds Z3 AST
nodes against the single process-global Z3 context (``z3.main_ctx()``)
with no locking anywhere in the call path. Every theory's semantics
class -- and ``ModelConstraints``/``ModelDefaults`` after it -- makes bare
``z3.*`` calls that resolve through that one shared context, so two
threads constructing models at the same time corrupt Z3's
context-internal hash-consing/reference-count tables and can abort the
interpreter with a segmentation fault. Nothing in this codebase's
production call path (``builder/runner.py``'s sequential ``for`` loop
over examples/theories) ever constructs models from more than one
thread; concurrent construction has never been a supported pattern.

This module declares that contract explicitly and enforces it with a
process-global, fail-fast, thread-reentrant guard: the *same* thread may
re-enter freely (so nested construction, e.g. model iteration building a
fresh ``ModelConstraints``/``ModelDefaults`` while an outer structure is
still alive, keeps working exactly as before), but a *different* thread
attempting to acquire the guard while it is held raises
:class:`ConcurrentConstructionError` immediately instead of racing on the
shared Z3 context. This converts an intermittent, catastrophic, hard-to
-debug C-level crash into a deterministic, documented Python exception,
consistent with the project's fail-fast philosophy.

This module is intentionally dependency-free (no ``z3``, no
``model_checker.models.semantic``/``structure``) so it can be imported
from anywhere without pulling in the rest of the package.
"""

from __future__ import annotations

import functools
import threading
from typing import Any, Callable, Optional, TypeVar

_F = TypeVar("_F", bound=Callable[..., Any])


class ConcurrentConstructionError(RuntimeError):
    """Raised when model construction is attempted from a second thread
    while another construction is already in progress on a different
    thread.

    Model construction is single-threaded-only: every theory's semantics
    constructor, plus ``ModelConstraints`` and ``ModelDefaults``, builds
    Z3 AST nodes against the single process-global Z3 context
    (``z3.main_ctx()``) with no per-thread isolation. Concurrent
    construction from multiple threads corrupts that shared context and
    can crash the interpreter (segfault) rather than raising a Python
    exception; this error is what a violation deterministically raises
    instead.

    To build multiple models at once, build them sequentially on one
    thread, or use a process pool with one model per process -- Z3
    contexts are not shared across processes, so process-level
    parallelism is safe.
    """


class _ConstructionGuard:
    """Process-global, thread-reentrant, fail-fast guard.

    Ownership state (``_owner``, ``_depth``) is protected by a plain
    ``threading.Lock`` used only for the short check-and-set on
    acquire/release -- it is never held across the guarded work itself,
    so it cannot itself become a bottleneck or deadlock source.
    """

    def __init__(self) -> None:
        self._lock = threading.Lock()
        self._owner: Optional[int] = None
        self._depth: int = 0

    def acquire(self) -> None:
        current = threading.get_ident()
        with self._lock:
            if self._owner is None:
                self._owner = current
                self._depth = 1
                return
            if self._owner == current:
                self._depth += 1
                return
            raise ConcurrentConstructionError(
                "Concurrent model construction is not supported: model "
                "construction is single-threaded-only because every "
                "theory builds Z3 AST nodes against the single "
                "process-global Z3 context with no per-thread isolation. "
                "Another thread is already constructing a model. Build "
                "models sequentially on one thread instead, or use one "
                "model per process (a process pool) rather than per "
                "thread."
            )

    def release(self) -> None:
        current = threading.get_ident()
        with self._lock:
            if self._owner != current:
                # Should be unreachable given correct acquire/release
                # pairing, but never silently corrupt guard state.
                raise RuntimeError(
                    "single_threaded_construction() guard released by a "
                    "thread that does not hold it -- this indicates a "
                    "mismatched acquire/release pair, not contention."
                )
            self._depth -= 1
            if self._depth <= 0:
                self._owner = None
                self._depth = 0


# Module-level, process-wide guard instance. All callers share this one
# guard -- that is the point: it serializes construction across the
# *entire process*, not per-class or per-instance.
_guard = _ConstructionGuard()


class single_threaded_construction:
    """Context manager enforcing the single-threaded-only construction
    contract for the wrapped block.

    Reentrant on the acquiring thread (nested ``with`` blocks on the same
    thread succeed and only release the guard when the outermost block
    exits); raises :class:`ConcurrentConstructionError` immediately if a
    different thread holds the guard. Always releases on exit, including
    when the guarded block raises.
    """

    def __enter__(self) -> "single_threaded_construction":
        _guard.acquire()
        return self

    def __exit__(self, exc_type, exc_value, traceback) -> None:
        _guard.release()


def guard_construction(func: _F) -> _F:
    """Decorator applying :class:`single_threaded_construction` around a
    function call.

    Used to wrap constructors (``__init__`` methods) so the guarded
    window spans the whole call, including whatever the wrapped function
    itself raises. Reentrant and exception-safe exactly like the context
    manager it is built on.
    """

    @functools.wraps(func)
    def wrapper(*args: Any, **kwargs: Any) -> Any:
        with single_threaded_construction():
            return func(*args, **kwargs)

    return wrapper  # type: ignore[return-value]
