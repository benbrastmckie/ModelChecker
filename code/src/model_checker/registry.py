"""Core theory registry.

Single source of truth for which theories are registered with the core system. Core
modules query this registry instead of hardcoding theory names or importing
`theory_lib` directly -- `theory_lib` is the only package that calls
`register_theory()` (see `theory_lib/__init__.py`), which keeps the core ->
`theory_lib` dependency strictly one-way (see
`theory_lib/docs/THEORY_ARCHITECTURE.md`'s Layering section).

This module contains no theory-name string literals: it is a generic mechanism,
not a catalog. The catalog lives in `theory_lib/__init__.py`, the one place
permitted to name theories.

Lazy resolution: `semantics`, `proposition`, `model`, and `operators` may each be
supplied either as a direct value (typically a class) or as a zero-argument
callable that resolves the value on first access. `theory_lib/__init__.py` uses the
callable form so that registering a theory never forces it to import eagerly --
resolution happens only when a caller actually reads e.g. `entry.semantics`.
"""

from typing import Any, Callable, Dict, Iterator, List, Optional, Union

__all__ = [
    "register_theory",
    "get_registered",
    "get_theory_entry",
    "iter_theories",
    "set_adapter",
    "set_default_theory",
    "get_default_theory",
    "TheoryEntry",
]

_LazyOrValue = Union[Any, Callable[[], Any]]


class TheoryEntry:
    """A single registered theory's identity plus its lazily-resolved components."""

    __slots__ = ("name", "module_path", "adapter", "_loaders", "_resolved")

    def __init__(
        self,
        name: str,
        *,
        module_path: str,
        semantics: _LazyOrValue,
        proposition: _LazyOrValue,
        model: _LazyOrValue,
        operators: _LazyOrValue,
        adapter: Optional[Any] = None,
    ) -> None:
        self.name = name
        self.module_path = module_path
        self.adapter = adapter
        self._loaders: Dict[str, _LazyOrValue] = {
            "semantics": semantics,
            "proposition": proposition,
            "model": model,
            "operators": operators,
        }
        self._resolved: Dict[str, Any] = {}

    def _resolve(self, key: str) -> Any:
        if key not in self._resolved:
            value = self._loaders[key]
            # A class is callable too (it constructs instances); only invoke plain
            # zero-arg callables (functions/lambdas/bound methods) as lazy thunks.
            if callable(value) and not isinstance(value, type):
                value = value()
            self._resolved[key] = value
        return self._resolved[key]

    @property
    def semantics(self) -> Any:
        return self._resolve("semantics")

    @property
    def proposition(self) -> Any:
        return self._resolve("proposition")

    @property
    def model(self) -> Any:
        return self._resolve("model")

    @property
    def operators(self) -> Any:
        return self._resolve("operators")

    def as_theory_dict(self) -> Dict[str, Any]:
        """Return the classic `get_theory()`-shaped dict for this entry."""
        return {
            "semantics": self.semantics,
            "proposition": self.proposition,
            "model": self.model,
            "operators": self.operators,
        }

    def __repr__(self) -> str:  # pragma: no cover - debugging aid only
        return f"TheoryEntry(name={self.name!r}, module_path={self.module_path!r})"


_REGISTRY: Dict[str, TheoryEntry] = {}
_ORDER: List[str] = []
_DEFAULT_THEORY: Optional[str] = None


def register_theory(
    name: str,
    *,
    module_path: str,
    semantics: _LazyOrValue,
    proposition: _LazyOrValue,
    model: _LazyOrValue,
    operators: _LazyOrValue,
    adapter: Optional[Any] = None,
) -> TheoryEntry:
    """Register a theory under `name`.

    Args:
        name: The registered theory's public name (e.g. 'bimodal').
        module_path: The dotted import path to the theory's package
            (e.g. 'model_checker.theory_lib.bimodal').
        semantics, proposition, model, operators: Each either the direct value or a
            zero-argument callable resolving it lazily on first access.
        adapter: Optional theory-specific adapter object (e.g. for jupyter/), or
            None to fall back to a caller-supplied default.

    Returns:
        The newly-created `TheoryEntry`.

    Raises:
        ValueError: If `name` is already registered. Registration is fail-fast:
            a duplicate name is always a programming error, never a valid update.
    """
    if name in _REGISTRY:
        raise ValueError(
            f"Theory '{name}' is already registered; duplicate registration is not allowed"
        )
    entry = TheoryEntry(
        name,
        module_path=module_path,
        semantics=semantics,
        proposition=proposition,
        model=model,
        operators=operators,
        adapter=adapter,
    )
    _REGISTRY[name] = entry
    _ORDER.append(name)
    return entry


def get_registered() -> List[str]:
    """Return the registered theory names in registration order."""
    return list(_ORDER)


def get_theory_entry(name: str) -> TheoryEntry:
    """Look up a registered theory's entry by name.

    Raises:
        ValueError: If `name` is not registered. The message includes the list of
            currently-available theory names for a fast, informative failure.
    """
    try:
        return _REGISTRY[name]
    except KeyError:
        available = ", ".join(_ORDER) if _ORDER else "(none registered)"
        raise ValueError(f"Unknown theory '{name}'. Available theories: {available}") from None


def set_adapter(name: str, adapter: Any) -> None:
    """Attach (or replace) an already-registered theory's `adapter`.

    Unlike `register_theory()`, this is not fail-fast on repeat calls for the same name --
    an upper-layer package (e.g. `jupyter/`) updating its own adapter registration is not the
    same kind of bug as a genuine duplicate `register_theory()` call, since `register_theory()`
    itself has no way to know about upper-layer-only concerns like display adapters at the
    point `theory_lib` registers each theory (see `theory_lib/__init__.py`'s
    `_register_theories()`, which always passes `adapter=None`).

    Raises:
        ValueError: If `name` is not registered yet.
    """
    entry = get_theory_entry(name)
    entry.adapter = adapter


def set_default_theory(name: str) -> None:
    """Mark `name` as the default theory for callers that need a sensible fallback without
    naming any theory themselves.

    Raises:
        ValueError: If `name` is not registered yet.
    """
    get_theory_entry(name)  # validates registration; raises ValueError if unknown
    global _DEFAULT_THEORY
    _DEFAULT_THEORY = name


def get_default_theory() -> Optional[str]:
    """Return the name marked via `set_default_theory()`, or None if never set."""
    return _DEFAULT_THEORY


def iter_theories() -> Iterator[TheoryEntry]:
    """Iterate over registered theory entries in registration order."""
    for name in _ORDER:
        yield _REGISTRY[name]


def _reset_registry_for_testing() -> None:
    """Clear all registrations. Test-only helper -- not part of the public API."""
    global _DEFAULT_THEORY
    _REGISTRY.clear()
    _ORDER.clear()
    _DEFAULT_THEORY = None
