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
    >>> from model_checker import BuildExample, get_theory
    >>> theory = get_theory("default")
    >>> model = BuildExample("simple_modal", theory)
    >>> model.check_formula("\\Box p -> p")

For more examples and detailed documentation, please see:
https://github.com/benbrastmckie/ModelChecker
"""

from importlib.metadata import version
try:
    __version__ = version("model-checker")
except ImportError:
    __version__ = "unknown"

# Define the public API of the package
__all__ = [
    "model", "syntactic",                           # modules
    "ParseFileFlags",                               # main.py
    "ForAll", "Exists", "bitvec_to_substates",      # utils.py
    "get_example", "get_theory", "run_test",
    "BuildModule", "BuildProject", "BuildExample",  # builder.py
    "BuildModule", "BuildExample", "main",
    "ModelConstraints",
    "Syntax",
]

# Import model as a whole
from .model import (
    ModelConstraints,
)

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

# Import specific items from utils
from .builder import (
    BuildModule,
    BuildProject,
    BuildExample,
)

# Import specific items from __main__
from .__main__ import (
    ParseFileFlags,
    main,
)
