r"""
Modal Subtheory for Logos Theory

This subtheory implements modal logical operators:
- Necessity (□)
- Possibility (◇)
- Counterfactual Necessity (\CFBox)
- Counterfactual Possibility (\CFDiamond)

API:
    get_operators(): Returns dictionary of operator name -> operator class mappings
    get_examples(): Returns example formulas demonstrating the operators
    Individual operator classes can be imported directly for type checking
"""

from .operators import (
    get_operators,
    NecessityOperator,
    PossibilityOperator,
    CFNecessityOperator,
    CFPossibilityOperator
)
from .examples import get_examples

__all__ = [
    'get_operators',
    'get_examples', 
    'NecessityOperator',
    'PossibilityOperator',
    'CFNecessityOperator',
    'CFPossibilityOperator'
]