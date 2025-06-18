"""
Extensional Subtheory for Logos Theory

This subtheory implements truth-functional (extensional) logical operators:
- Negation (¬)
- Conjunction (∧) 
- Disjunction (∨)
- Material Implication (→)
- Biconditional (↔)
- Top (⊤)
- Bottom (⊥)

API:
    get_operators(): Returns dictionary of operator name -> operator class mappings
    get_examples(): Returns example formulas demonstrating the operators
    Individual operator classes can be imported directly for type checking
"""

from .operators import (
    get_operators,
    NegationOperator,
    AndOperator,
    OrOperator,
    ConditionalOperator,
    BiconditionalOperator,
    TopOperator,
    BotOperator
)
from .examples import get_examples

__all__ = [
    'get_operators',
    'get_examples',
    'NegationOperator',
    'AndOperator', 
    'OrOperator',
    'ConditionalOperator',
    'BiconditionalOperator',
    'TopOperator',
    'BotOperator'
]