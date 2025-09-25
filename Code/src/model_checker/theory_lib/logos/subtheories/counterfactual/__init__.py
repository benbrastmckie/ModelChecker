"""
Counterfactual Subtheory for Logos Theory

This subtheory implements counterfactual logical operators:
- Counterfactual Conditional (□→)
- Might Counterfactual (◇→)

API:
    get_operators(): Returns dictionary of operator name -> operator class mappings
    get_examples(): Returns example formulas demonstrating the operators
    Individual operator classes can be imported directly for type checking
"""

from .operators import (
    get_operators,
    CounterfactualOperator,
    MightCounterfactualOperator,
)

def get_examples():
    """
    Get all counterfactual examples (lazy loaded to avoid circular imports).

    Returns:
        dict: Dictionary containing all counterfactual examples
    """
    # Lazy import to avoid circular dependency
    from .examples import counterfactual_cm_examples, counterfactual_th_examples, unit_tests
    return {
        'countermodels': counterfactual_cm_examples,
        'theorems': counterfactual_th_examples,
        'all': unit_tests
    }

__all__ = [
    'get_operators',
    'get_examples',
    'CounterfactualOperator',
    'MightCounterfactualOperator',
]