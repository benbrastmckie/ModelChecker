"""
Extensional Subtheory for Logos Theory

This subtheory implements truth-functional (extensional) logical operators:
- Negation (¬)
- Conjunction (') 
- Disjunction (()
- Material Implication (’)
- Biconditional (”)
- Top (¤)
- Bottom (¥)
"""

from .operators import get_operators

__all__ = ['get_operators']