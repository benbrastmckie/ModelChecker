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

from .examples import relevance_cm_examples, relevance_th_examples, unit_tests
from .operators import get_operators, RelevanceOperator

def get_examples():
    """
    Get all relevance examples.

    Returns:
        dict: Dictionary containing all relevance examples
    """
    return {
        'countermodels': relevance_cm_examples,
        'theorems': relevance_th_examples,
        'all': unit_tests
    }





__all__ = [
    'get_operators',
    'get_examples',
    'RelevanceOperator'
]