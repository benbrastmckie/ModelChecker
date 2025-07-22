"""
Witness uninegation theory implementation.

This module implements Strategy E1: Witnesses as Model Predicates, which makes
witness functions first-class citizens of the model structure. Instead of trying
to extract or reconstruct witness functions, they simply exist as queryable
predicates alongside verify and exclude.
"""

from .semantic import WitnessSemantics, WitnessModelAdapter, WitnessProposition, WitnessStructure, WitnessAwareModel, WitnessRegistry, WitnessConstraintGenerator
from .operators import witness_operators
from .iterate import ExclusionModelIterator, iterate_example

# For ModelChecker discovery
DefaultSemantics = WitnessSemantics

# Legacy alias for compatibility
ExclusionStructure = WitnessStructure

__all__ = [
    'WitnessSemantics', 
    'WitnessModelAdapter', 
    'WitnessProposition', 
    'WitnessStructure',
    'WitnessAwareModel',
    'WitnessRegistry',
    'WitnessConstraintGenerator',
    'witness_operators', 
    'DefaultSemantics',
    'ExclusionStructure',  # Legacy alias
    'ExclusionModelIterator',
    'iterate_example'
]