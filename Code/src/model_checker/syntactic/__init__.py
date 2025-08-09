"""
Syntactic package for the ModelChecker framework.

This package contains the core components for logical syntax handling including
sentence representation, operator definitions, and formula parsing.
"""

# Phase 3.2 - Import atoms from the new module
from .atoms import AtomSort, AtomVal

# Phase 3.3 - Import Sentence from the new module
from .sentence import Sentence

# Phase 3.4 - Import Operator classes from the new module
from .operators import Operator, DefinedOperator

# Phase 3.5 - Import OperatorCollection from the new module
from .collection import OperatorCollection

# Phase 3.6 - Import Syntax from the new module
from .syntax import Syntax

__all__ = [
    # Atoms
    'AtomSort',
    'AtomVal',
    # From old module
    'Sentence',
    'Operator',
    'DefinedOperator',
    'OperatorCollection',
    'Syntax',
]