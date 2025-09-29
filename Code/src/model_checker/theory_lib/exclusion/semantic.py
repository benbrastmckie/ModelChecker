"""
Witness predicate semantics implementation.

This module maintains backward compatibility by re-exporting all classes
from the new modular semantic package structure. The implementation has been
refactored from a monolithic file into focused modules while preserving
the witness-based semantic paradigm.

All classes that were previously in this file are now properly organized
in the semantic/ package but remain importable from this location.
"""

# Re-export all classes from the new modular structure
from .semantic import (
    WitnessAwareModel,
    WitnessConstraintGenerator,
    WitnessModelAdapter,
    WitnessProposition,
    WitnessRegistry,
    WitnessSemantics,
    WitnessStructure,
)

# Maintain backward compatibility - all original exports still work
__all__ = [
    'WitnessSemantics',
    'WitnessAwareModel',
    'WitnessRegistry',
    'WitnessConstraintGenerator',
    'WitnessModelAdapter',
    'WitnessStructure',
    'WitnessProposition',
]