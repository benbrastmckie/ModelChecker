"""bimodal_logic - Public facade for the bimodal logic oracle.

This package provides the public API for the Z3-based bimodal logic oracle,
which implements temporal and modal reasoning for the bimodal_harness.

The Z3OracleProvider class will be fully implemented in task 103.
"""

from __future__ import annotations

from .provider import Z3OracleProvider
from .translation import (
    json_to_prefix,
    temporal_depth,
    prefix_to_infix,
    unfold_formula,
    fold_formula,
    normalize_formula,
)

__all__ = [
    "Z3OracleProvider",
    "json_to_prefix",
    "temporal_depth",
    "prefix_to_infix",
    "unfold_formula",
    "fold_formula",
    "normalize_formula",
]
