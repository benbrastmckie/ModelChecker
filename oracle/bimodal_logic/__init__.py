"""bimodal_logic - Public facade for the bimodal logic oracle.

This package provides the public API for the Z3-based bimodal logic oracle,
which implements temporal and modal reasoning for the bimodal_harness.

`Z3OracleProvider` (see `provider.py`) is fully implemented: it searches for
witness-family certificates over discrete (Z) time, matching the in-package
`model_checker.theory_lib.bimodal` witness-family certificate redesign (see
`code/src/model_checker/theory_lib/bimodal/docs/ADEQUACY.md` for the design
this provider sits on top of).
"""

from __future__ import annotations

from .errors import OracleTimeoutError
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
    "OracleTimeoutError",
    "Z3OracleProvider",
    "json_to_prefix",
    "temporal_depth",
    "prefix_to_infix",
    "unfold_formula",
    "fold_formula",
    "normalize_formula",
]
