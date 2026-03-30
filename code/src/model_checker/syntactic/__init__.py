"""
Syntactic package for the ModelChecker framework.

This package contains the core components for logical syntax handling including
sentence representation, operator definitions, and formula parsing.

Note: AtomSort is dynamically resolved via __getattr__ to support backend switching.
Direct access to syntactic.AtomSort will call get_atom_sort() to return the current
backend's sort. For explicit control, import get_atom_sort from syntactic.atoms.
"""
from typing import Any

# Phase 3.2 - Import atoms from the new module (AtomSort resolved dynamically)
from .atoms import AtomVal, get_atom_sort, reset_atom_sort

# Phase 3.3 - Import Sentence from the new module
from .sentence import Sentence

# Phase 3.4 - Import Operator classes from the new module
from .operators import Operator, DefinedOperator

# Phase 3.5 - Import OperatorCollection from the new module
from .collection import OperatorCollection

# Phase 3.6 - Import Syntax from the new module
from .syntax import Syntax

# First-order term algebra
from .terms import Term, Variable, Constant, FunctionApplication

# First-order variable assignments
from .assignments import VariableAssignment

# Formula-level operations
from .formulas import compute_formula_free_variables, is_syntactically_wff

__all__ = [
    # Atoms (AtomSort resolved dynamically via __getattr__)
    'AtomSort',
    'AtomVal',
    'get_atom_sort',
    'reset_atom_sort',
    # From old module
    'Sentence',
    'Operator',
    'DefinedOperator',
    'OperatorCollection',
    'Syntax',
    # First-order terms
    'Term',
    'Variable',
    'Constant',
    'FunctionApplication',
    # First-order assignments
    'VariableAssignment',
    # Formula operations
    'compute_formula_free_variables',
    'is_syntactically_wff',
]


def __getattr__(name: str) -> Any:
    """Dynamic attribute resolution for backend-dependent objects.

    AtomSort is resolved dynamically to support backend switching between z3 and cvc5.
    When the backend changes (via reset_atom_sort()), subsequent accesses to AtomSort
    return the sort for the new backend.

    Args:
        name: The attribute name being accessed.

    Returns:
        The requested attribute value.

    Raises:
        AttributeError: If the attribute is not found.
    """
    if name == "AtomSort":
        return get_atom_sort()
    raise AttributeError(f"module {__name__!r} has no attribute {name!r}")