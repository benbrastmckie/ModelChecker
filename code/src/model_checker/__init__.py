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
    get_theory,
    get_example,
    run_test,
)

