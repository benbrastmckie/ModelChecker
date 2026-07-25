"""
Shared semantic framework for the logos theory.

This package implements the core semantic foundation for all logos subtheories,
providing unified classes for semantics, propositions, and model structures --
split from a single monolithic semantic.py into focused modules.

Re-export-only per docs/THEORY_ARCHITECTURE.md's Theory Contract: the actual class bodies
live in core.py (LogosSemantics), proposition.py (LogosProposition), and model.py
(LogosModelStructure).
"""

from .core import LogosSemantics
from .proposition import LogosProposition
from .model import LogosModelStructure

__all__ = [
    'LogosSemantics',
    'LogosProposition',
    'LogosModelStructure',
]
