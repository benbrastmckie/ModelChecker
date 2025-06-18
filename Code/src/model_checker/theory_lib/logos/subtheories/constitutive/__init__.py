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

from .operators import (
    get_operators,
    IdentityOperator,
    GroundOperator,
    EssenceOperator,
    RelevanceOperator,
    ReductionOperator
)
from .examples import get_examples

__all__ = [
    'get_operators',
    'get_examples',
    'IdentityOperator',
    'GroundOperator',
    'EssenceOperator',
    'RelevanceOperator',
    'ReductionOperator'
]
