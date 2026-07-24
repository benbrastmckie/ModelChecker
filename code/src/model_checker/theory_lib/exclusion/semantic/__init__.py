"""
Witness semantics module.

This package implements witness-based negation semantics by breaking up
the original monolithic semantic.py file into focused modules while
preserving all functionality and backward compatibility.

Re-export-only per docs/THEORY_ARCHITECTURE.md's Theory Contract: the actual class bodies
live in core.py (WitnessSemantics), model.py (WitnessAwareModel, WitnessModelAdapter,
WitnessStructure), proposition.py (WitnessProposition), constraints.py
(WitnessConstraintGenerator), and registry.py (WitnessRegistry).
"""

# Import all classes from their respective modules
from .core import WitnessSemantics
from .constraints import WitnessConstraintGenerator
from .model import WitnessAwareModel, WitnessModelAdapter, WitnessStructure
from .proposition import WitnessProposition
from .registry import WitnessRegistry

# Re-export all classes for backward compatibility
__all__ = [
    'WitnessSemantics',
    'WitnessAwareModel',
    'WitnessRegistry',
    'WitnessConstraintGenerator',
    'WitnessModelAdapter',
    'WitnessStructure',
    'WitnessProposition',
]
