"""
Counterfactual Subtheory for Logos Theory

This subtheory implements counterfactual logical operators:
- Counterfactual Conditional (□→)
- Might Counterfactual (◇→)
- Imposition (◦)
- Might Imposition (◯)

API:
    get_operators(): Returns dictionary of operator name -> operator class mappings
    get_examples(): Returns example formulas demonstrating the operators
    Individual operator classes can be imported directly for type checking
"""

from .operators import (
    get_operators,
    CounterfactualOperator,
    MightCounterfactualOperator,
    ImpositionOperator,
    MightImpositionOperator
)
from .examples import get_examples

__all__ = [
    'get_operators',
    'get_examples',
    'CounterfactualOperator',
    'MightCounterfactualOperator',
    'ImpositionOperator',
    'MightImpositionOperator'
]