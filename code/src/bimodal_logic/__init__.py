"""bimodal_logic - Public facade for the bimodal logic oracle.

This package provides the public API for the Z3-based bimodal logic oracle,
which implements temporal and modal reasoning for the bimodal_harness.

Stub modules translation.py and serialization.py will be filled in by task 102.
The Z3OracleProvider class will be fully implemented in task 103.
"""

from __future__ import annotations

from .provider import Z3OracleProvider

__all__ = ["Z3OracleProvider"]
