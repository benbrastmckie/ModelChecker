"""
Z3 atom integration for syntactic representation.

This module provides the core Z3 integration for atomic propositions,
defining the AtomSort type and AtomVal factory function used throughout
the model checker for representing atomic values in logical formulas.
"""

from typing import Union
from z3 import DeclareSort, Const
from .types import AtomType


# Declare the Z3 sort for atomic propositions
AtomSort = DeclareSort("AtomSort")


def AtomVal(i: Union[int, str]) -> AtomType:
    """Create a constant of AtomSort with the given index.
    
    This helper function creates atomic proposition values for use in semantics.
    These atoms serve as the basic building blocks for logical formulas, with
    each atom representing a distinct propositional variable.
    
    Args:
        i: The index for the atomic proposition (int or str identifier)
        
    Returns:
        Z3 datatype reference for the atom
        
    Examples:
        >>> atom0 = AtomVal(0)  # First atomic proposition
        >>> atom1 = AtomVal(1)  # Second atomic proposition
        >>> atom_p = AtomVal("p")  # Named atomic proposition
        >>> # These can be used in Z3 constraints and semantic definitions
    """
    return Const(f"AtomSort!val!{i}", AtomSort)