"""Model checker theory library.

This module provides access to various logical theories through lazy loading.
It also includes utility functions for accessing examples from each theory.

Theories:
- default: Standard bilateral truthmaker semantics
- exclusion: Unilateral semantics with exclusion relations
- imposition: Semantics with imposition relations
- bimodal: Bimodal semantics for counterfactuals and imposition

Examples access:
- get_examples(theory_name): Access examples from a specific theory
- get_test_examples(theory_name): Access test examples from a theory
- get_semantic_theories(theory_name): Access semantic theory implementations
"""

import importlib
import os

# Registry of available theories
# Add new theories to this list when implementing them
AVAILABLE_THEORIES = [
    'default',
    'exclusion',
    'imposition',
    # 'bimodal',
    # Add new theories here
]

# IMPORTANT NOTE FOR DEVELOPERS:
# When adding a new theory to AVAILABLE_THEORIES above,
# you must also manually add it to the __all__ list below
# to avoid linter errors and ensure proper exports.

# Dictionary to cache loaded theory modules
_theory_modules = {}

def get_examples(theory_name):
    """Access examples from a specific theory without circular imports.
    
    Args:
        theory_name (str): Name of the theory ('default', 'exclusion', etc.)
        
    Returns:
        dict: A dictionary of example cases for model checking
        
    Raises:
        ValueError: If the theory name is not recognized
    """
    if theory_name not in AVAILABLE_THEORIES:
        raise ValueError(f"Unknown theory: {theory_name}")
    
    try:
        module = importlib.import_module(f".{theory_name}.examples", package=__name__)
        return module.example_range
    except (ImportError, AttributeError) as e:
        raise ValueError(f"Could not load examples for theory '{theory_name}': {str(e)}")

def get_test_examples(theory_name):
    """Access test examples from a specific theory without circular imports.
    
    Args:
        theory_name (str): Name of the theory ('default', 'exclusion', etc.)
        
    Returns:
        dict: A dictionary of test example cases for unit testing
        
    Raises
        ValueError: If the theory name is not recognized
    """
    if theory_name not in AVAILABLE_THEORIES:
        raise ValueError(f"Unknown theory: {theory_name}")
    
    try:
        module = importlib.import_module(f".{theory_name}.examples", package=__name__)
        return module.test_example_range
    except (ImportError, AttributeError) as e:
        raise ValueError(f"Could not load test examples for theory '{theory_name}': {str(e)}")

def get_semantic_theories(theory_name):
    """Access semantic theory implementations from a specific theory.
    
    Args:
        theory_name (str): Name of the theory ('default', 'exclusion', etc.)
        
    Returns:
        dict: A dictionary mapping theory names to implementations
        
    Raises:
        ValueError: If the theory name is not recognized
    """
    if theory_name not in AVAILABLE_THEORIES:
        raise ValueError(f"Unknown theory: {theory_name}")
    
    try:
        module = importlib.import_module(f".{theory_name}.examples", package=__name__)
        return module.semantic_theories
    except (ImportError, AttributeError) as e:
        raise ValueError(f"Could not load semantic theories for theory '{theory_name}': {str(e)}")

def discover_theories():
    """Automatically discover available theories based on directory structure.
    
    This function is for development and debugging purposes.
    In production, use the AVAILABLE_THEORIES list.
    
    Returns:
        list: List of discovered theory names
    """
    current_dir = os.path.dirname(os.path.abspath(__file__))
    theories = []
    
    # Look for directories that contain both examples.py and operators.py
    for item in os.listdir(current_dir):
        if os.path.isdir(os.path.join(current_dir, item)) and not item.startswith('__'):
            # Check if this has the structure of a theory module
            examples_path = os.path.join(current_dir, item, 'examples.py')
            operators_path = os.path.join(current_dir, item, 'operators.py')
            if os.path.exists(examples_path) and os.path.exists(operators_path):
                theories.append(item)
    
    return sorted(theories)

# Create a dictionary of placeholder attributes for lazy loading
_placeholders = {name: None for name in AVAILABLE_THEORIES}

# Only include utility functions and registry in __all__
# This avoids linter errors about missing modules
__all__ = [
    # Registry
    'AVAILABLE_THEORIES',
    
    # Utility functions
    'get_examples',
    'get_test_examples',
    'get_semantic_theories',
    'discover_theories',
]

# NOTE: For linting purposes, the following code helps the linter understand
# that these modules can be imported from theory_lib, even though they're
# actually loaded on-demand by __getattr__ for better performance.
# This is a common Python pattern for modules that want lazy loading.

# Recommended approach for importing:
# from model_checker.theory_lib import get_examples  # Utility function
# from model_checker.theory_lib import default       # Specific theory module

# We don't include theories in __all__ to avoid linter errors with "missing modules",
# but they ARE importable at runtime.

# No dynamic imports here - let __getattr__ handle them as needed

def __getattr__(name):
    """Lazy load theory modules when accessed."""
    if name in AVAILABLE_THEORIES:
        if name not in _theory_modules:
            # Import the theory module
            module = importlib.import_module(f".{name}", package=__name__)
            _theory_modules[name] = module
        return _theory_modules[name]
    
    raise AttributeError(f"module '{__name__}' has no attribute '{name}'")
