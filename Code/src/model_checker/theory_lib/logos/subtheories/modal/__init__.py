from .examples import modal_cm_examples, modal_th_examples, modal_def_examples, unit_tests
from .operators import (
    get_operators,
    NecessityOperator,
    PossibilityOperator,
    CFNecessityOperator,
    CFPossibilityOperator
)

def get_examples():
    """
    Get all modal examples.

    Returns:
        dict: Dictionary containing all modal examples
    """
    return {
        'countermodels': modal_cm_examples,
        'theorems': modal_th_examples,
        'definitions': modal_def_examples,
        'all': unit_tests
    }

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


__all__ = [
    'get_operators',
    'get_examples', 
    'NecessityOperator',
    'PossibilityOperator',
    'CFNecessityOperator',
    'CFPossibilityOperator'
]