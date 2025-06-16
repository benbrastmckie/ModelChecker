"""
Modal Subtheory for Logos Theory

This subtheory implements modal logical operators:
- Necessity (¡)
- Possibility (Ç)
- Counterfactual Necessity (\CFBox)
- Counterfactual Possibility (\CFDiamond)
"""

from .operators import get_operators

__all__ = ['get_operators']