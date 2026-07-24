"""
Model Checker - A Python package for modal logic model checking and verification.

This package provides tools and utilities for building and analyzing modal logic
models, with support for various modal logics including standard modal logic
and bimodal logic.

Key Features:
    - Model construction and verification
    - Support for different modal logic theories
    - Syntactic parsing and model building
    - Built-in example models and theories
    - Integration with Z3 theorem prover

Basic Usage:
    >>> from model_checker import ModelConstraints, Syntax

For more examples and detailed documentation, please see:
https://github.com/benbrastmckie/ModelChecker
"""

from .utils import get_model_checker_version

__version__ = get_model_checker_version()

# Define the public API of the package
__all__ = [
    "model", "syntactic",                           # modules
    "ForAll", "Exists", "bitvec_to_substates",      # utils.py
    "get_example", "get_theory", "run_test",
    "ModelConstraints",
    "Syntax",
]

# Import model components
from .models.constraints import ModelConstraints

# Import syntactic as a whole
from .syntactic import (
    Syntax,
)

# Import specific items from utils
from .utils import (
    ForAll,
    Exists,
    bitvec_to_substates,
    get_example,
    run_test,
)

# get_theory is the theory-aware entry point (auto-loads a theory's semantic_theories mapping
# from theory_lib by name); it lives in the upper-layer model_checker/api.py, not utils/, since
# utils/ is core and must never import theory_lib. This keeps the top-level model_checker.get_theory
# public surface byte-identical to before the split -- only its implementation module moved.
from .api import get_theory

# Bootstrap the core theory registry (upper layer -> theory_lib, the one direction the
# layering contract permits outside theory_lib itself; see
# theory_lib/docs/THEORY_ARCHITECTURE.md's Layering section). Importing theory_lib here runs
# its registration of all theories into `model_checker.registry` as a side effect, so core
# consumers that query the registry get correct results even if nothing else has imported
# theory_lib yet. This performs no eager per-theory loading: each theory's
# semantics/proposition/model/operators are registered as lazy thunks resolved only on first
# actual access (see theory_lib/__init__.py's `_register_theories()`).
from . import theory_lib as _theory_lib  # noqa: F401

