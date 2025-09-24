"""
Constitutive Subtheory for Logos Theory

This subtheory implements constitutive logical operators:
- Identity (≡)
- Ground (≤)
- Essence (⊑)
- Relevance (≼)
- Reduction (⇒)

API:
    get_operators(): Returns dictionary of operator name -> operator class mappings
    get_examples(): Returns example formulas demonstrating the operators
    Individual operator classes can be imported directly for type checking
"""

from .examples import constitutive_cm_examples, constitutive_th_examples, unit_tests
from .operators import (
    get_operators,
    IdentityOperator,
    GroundOperator,
    EssenceOperator,
    RelevanceOperator,
    ReductionOperator
)

def get_examples():
    """
    Get all constitutive examples.

    Returns:
        dict: Dictionary containing all constitutive examples
    """
    return {
        'countermodels': constitutive_cm_examples,
        'theorems': constitutive_th_examples,
        'all': unit_tests
    }

__all__ = [
    'get_operators',
    'get_examples',
    'IdentityOperator',
    'GroundOperator',
    'EssenceOperator',
    'RelevanceOperator',
    'ReductionOperator'
]
