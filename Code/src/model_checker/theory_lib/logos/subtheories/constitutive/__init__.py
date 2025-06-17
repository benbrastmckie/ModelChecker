"""
Constitutive Subtheory for Logos Theory

This subtheory implements constitutive logical operators:
- Identity (≡)
- Ground (≤)
- Essence (⊑)
- Relevance (≼)
- Reduction (⇒)
"""

from .operators import get_operators

__all__ = ['get_operators']
