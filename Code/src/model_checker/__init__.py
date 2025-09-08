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
    - Jupyter notebook integration

Basic Usage:
    >>> from model_checker import check_formula
    >>> # Check if a counterfactual formula is valid
    >>> result = check_formula("(A \\boxright B)", theory_name="logos")
    >>> print(f"Valid: {result}")

For more examples and detailed documentation, please see:
https://github.com/benbrastmckie/ModelChecker
"""

from .utils import get_model_checker_version

__version__ = get_model_checker_version()

# Define the public API of the package
__all__ = [
    "model", "syntactic", "jupyter",                # modules
    "ParseFileFlags",                               # main.py
    "ForAll", "Exists", "bitvec_to_substates",      # utils.py
    "get_example", "get_theory", "run_test",
    "BuildModule", "BuildProject", "BuildExample",  # builder.py
    "BuildModule", "main",
    "ModelConstraints",
    "Syntax",
]

# Add jupyter components to API only if dependencies are available
try:
    # Use the function from jupyter module to check dependencies
    from .jupyter import has_jupyter_dependencies
    
    if has_jupyter_dependencies():
        __all__.extend([
            "check_formula", "find_countermodel", "explore_formula",
            "ModelExplorer", "FormulaChecker",
        ])
except ImportError:
    # If we can't import, don't add jupyter components to __all__
    pass

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

# Import specific items from builder
from .builder import (
    BuildModule,
    BuildProject,
)
# Import BuildExample directly for notebooks
from .builder.example import BuildExample

# Import specific items from __main__
from .__main__ import (
    ParseFileFlags,
    main,
)

# Import jupyter components if they are available
try:
    # First import has_jupyter_dependencies to check for dependencies
    from .jupyter import has_jupyter_dependencies
    
    # Then conditionally import the components if dependencies are available
    if has_jupyter_dependencies():
        from .jupyter import (
            check_formula,
            find_countermodel,
            explore_formula,
            ModelExplorer,
            FormulaChecker,
        )
    else:
        # Import stub implementations instead
        from .jupyter import (
            check_formula,  # This is already the stub version that raises error
            find_countermodel,
            explore_formula,
        )
        # ModelExplorer and FormulaChecker will not be imported
except ImportError:
    # If jupyter module itself can't be imported, just pass
    pass
