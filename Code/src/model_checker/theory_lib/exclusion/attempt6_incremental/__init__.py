"""
Incremental exclusion theory implementation.

This attempt addresses the fundamental architectural issue in exclusion semantics
by maintaining persistent computational context across the three levels of
programmatic semantics: Syntax → Truth-Conditions → Extensions.
"""

from .semantic import ExclusionSemantics, UnilateralProposition
from .operators import exclusion_operators

__all__ = ['ExclusionSemantics', 'UnilateralProposition', 'exclusion_operators']