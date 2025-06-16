"""
Constitutive Subtheory for Logos Theory

This subtheory implements constitutive logical operators:
- Identity (a)
- Ground (d)
- Essence (‘)
- Relevance (|)
- Reduction (\reduction)
"""

from .operators import get_operators

__all__ = ['get_operators']