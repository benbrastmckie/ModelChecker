"""
Z3/cvc5 atom integration for syntactic representation.

This module provides the core solver integration for atomic propositions,
defining the AtomSort type and AtomVal factory function used throughout
the model checker for representing atomic values in logical formulas.

AtomSort uses lazy initialization to support backend switching - the actual
sort is created on first access using the currently active backend.
"""

from typing import Union, Any

from model_checker.solver.expressions import DeclareSort, Const
from .types import AtomType


# Lazy initialization for AtomSort to support backend switching
_atom_sort = None


def get_atom_sort() -> Any:
    """Get the AtomSort, creating it lazily for the current backend.

    This function ensures the AtomSort is created using the currently active
    solver backend, enabling proper backend switching support.

    Returns:
        The AtomSort for the current backend.
    """
    global _atom_sort
    if _atom_sort is None:
        _atom_sort = DeclareSort("AtomSort")
    return _atom_sort


def reset_atom_sort() -> None:
    """Reset AtomSort when backend changes.

    This should be called when switching solver backends to ensure the AtomSort
    is recreated for the new backend.
    """
    global _atom_sort
    _atom_sort = None


# Backwards compatibility - module attribute access
# This allows `from syntactic.atoms import AtomSort` to continue working
def __getattr__(name: str) -> Any:
    if name == "AtomSort":
        return get_atom_sort()
    raise AttributeError(f"module {__name__!r} has no attribute {name!r}")


def AtomVal(i: Union[int, str]) -> AtomType:
    """Create a constant of AtomSort with the given index.

    This helper function creates atomic proposition values for use in semantics.
    These atoms serve as the basic building blocks for logical formulas, with
    each atom representing a distinct propositional variable.

    Args:
        i: The index for the atomic proposition (int or str identifier)

    Returns:
        Solver datatype reference for the atom

    Examples:
        >>> atom0 = AtomVal(0)  # First atomic proposition
        >>> atom1 = AtomVal(1)  # Second atomic proposition
        >>> atom_p = AtomVal("p")  # Named atomic proposition
        >>> # These can be used in solver constraints and semantic definitions
    """
    return Const(f"AtomSort!val!{i}", get_atom_sort())