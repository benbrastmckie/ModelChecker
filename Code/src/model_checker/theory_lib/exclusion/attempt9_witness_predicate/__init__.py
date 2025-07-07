"""
Witness predicate exclusion theory implementation.

This module implements Strategy E1: Witnesses as Model Predicates, which makes
witness functions first-class citizens of the model structure. Instead of trying
to extract or reconstruct witness functions, they simply exist as queryable
predicates alongside verify and exclude.
"""

from .semantic import WitnessPredicateSemantics, PredicateModelAdapter
from .operators import witness_predicate_operators

# For ModelChecker discovery
DefaultSemantics = WitnessPredicateSemantics

__all__ = ['WitnessPredicateSemantics', 'witness_predicate_operators', 'DefaultSemantics']