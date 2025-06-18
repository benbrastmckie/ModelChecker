"""
Relevance Subtheory for Logos Theory

This subtheory implements relevance logic operators:
- Relevance (≼)

Note: This module imports from constitutive for operator dependencies.

API:
    get_operators(): Returns dictionary of operator name -> operator class mappings
    get_examples(): Returns example formulas demonstrating the operators
    RelevanceOperator: Direct access to the relevance operator class
"""

from .operators import get_operators, RelevanceOperator
from .examples import get_examples

__all__ = [
    'get_operators',
    'get_examples',
    'RelevanceOperator'
]