"""
Z3 atom integration for syntactic representation.

This module provides the core Z3 integration for atomic propositions,
defining the AtomSort type and AtomVal factory function used throughout
the model checker for representing atomic values in logical formulas.
"""

from z3 import DeclareSort, Const


# Declare the Z3 sort for atomic propositions
AtomSort = DeclareSort("AtomSort")


def AtomVal(i):
    """Create a constant of AtomSort with the given index.
    
    This helper function creates atomic proposition values for use in semantics.
    These atoms serve as the basic building blocks for logical formulas, with
    each atom representing a distinct propositional variable.
    
    Args:
        i (int): The index for the atomic proposition
        
    Returns:
        Const: A Z3 constant of AtomSort with a unique identifier
        
    Example:
        >>> atom0 = AtomVal(0)  # First atomic proposition
        >>> atom1 = AtomVal(1)  # Second atomic proposition
        >>> # These can be used in Z3 constraints and semantic definitions
    """
    return Const(f"AtomSort!val!{i}", AtomSort)