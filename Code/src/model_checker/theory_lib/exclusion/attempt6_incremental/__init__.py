"""
Incremental model checking implementation for exclusion theory.

This module implements a three-level integration architecture that maintains
continuous interaction between Syntax, Truth-Conditions, and Extensions levels
to solve the false premise problem in exclusion semantics.
"""

from .incremental_core import (
    WitnessStore,
    TruthCache,
    IncrementalVerifier,
    ThreeLevelIntegrator
)

__all__ = [
    'WitnessStore',
    'TruthCache', 
    'IncrementalVerifier',
    'ThreeLevelIntegrator'
]