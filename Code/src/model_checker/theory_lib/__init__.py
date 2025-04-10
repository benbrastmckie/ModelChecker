"""Model checker theory library.

This module provides access to various logical theories implementing programmatic 
semantics for modal, counterfactual, and hyperintensional operators. Theories are
loaded on-demand through lazy loading for better performance.

Each theory implements:
- Semantic model structures with state fusion, part-hood relations, etc.
- Logical operators with specific verification and falsification conditions
- Proposition evaluation within the semantic framework
- Example models demonstrating the theory's principles

Available Theories:
- default: Standard bilateral truthmaker semantics
- exclusion: Unilateral semantics with exclusion relations 
- imposition: Semantics with imposition relations
- bimodal: Bimodal semantics for counterfactuals and imposition (experimental)

The module supports theory extension through a central registry. To add a new theory:
1. Create a new directory under theory_lib/
2. Implement semantic.py, operators.py, and examples.py
3. Add test cases in a test/ subdirectory
4. Register the theory name in AVAILABLE_THEORIES

Usage Examples:
    # Import a specific theory
    from model_checker.theory_lib import default
    
    # Use with BuildExample constructor
    from model_checker import BuildExample
    model = BuildExample("simple_modal", default)
    
    # Access examples from a theory
    from model_checker.theory_lib import get_examples
    examples = get_examples('default')
    
    # Get test examples for unit testing
    from model_checker.theory_lib import get_test_examples
    test_examples = get_test_examples('default')
    
    # Discover all available theories
    from model_checker.theory_lib import discover_theories
    all_theories = discover_theories()
"""

import importlib
import os

# Registry of available theories - add new theories here
AVAILABLE_THEORIES = [
    'default',      # Standard bilateral truthmaker semantics
    'exclusion',    # Unilateral semantics with exclusion relations
    'imposition',   # Semantics with imposition relations
    'bimodal',      # Bimodal semantics
]

# Dictionary to cache loaded theory modules
_theory_modules = {}

def get_examples(theory_name):
    """Access example model configurations from a specific theory.
    
    Each theory provides a set of examples that demonstrate its logical principles.
    These examples are used for demonstration and model checking.
    
    Args:
        theory_name (str): Name of the registered theory ('default', 'exclusion', etc.)
        
    Returns:
        dict: Dictionary mapping example names to (premises, conclusions, settings) tuples
        
    Raises:
        ValueError: If the theory is not registered or examples cannot be loaded
        
    Example:
        >>> from model_checker.theory_lib import get_examples
        >>> default_examples = get_examples('default')
        >>> print(list(default_examples.keys()))
        ['CF_CM_1', 'CF_TH_14']
    """
    if theory_name not in AVAILABLE_THEORIES:
        raise ValueError(f"Unknown theory: {theory_name}")
    
    try:
        module = importlib.import_module(f".{theory_name}.examples", package=__name__)
        return module.example_range
    except (ImportError, AttributeError) as e:
        raise ValueError(f"Could not load examples for theory '{theory_name}': {str(e)}")

def get_test_examples(theory_name):
    """Access test examples from a specific theory for unit testing.
    
    These examples include test cases with expected results for automated testing.
    Each example typically includes premises, conclusions, settings, and expected outcome.
    
    Args:
        theory_name (str): Name of the registered theory ('default', 'exclusion', etc.)
        
    Returns:
        dict: Dictionary mapping test names to (premises, conclusions, settings) tuples
        
    Raises:
        ValueError: If the theory is not registered or test examples cannot be loaded
        
    Example:
        >>> from model_checker.theory_lib import get_test_examples
        >>> tests = get_test_examples('default')
        >>> # Use with pytest parametrization
        >>> @pytest.mark.parametrize("example_name, example_case", tests.items())
        >>> def test_examples(example_name, example_case):
        >>>     # Test implementation
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
    
    This function returns the semantic theory implementations that define
    the logical behavior of each theory variant.
    
    Args:
        theory_name (str): Name of the registered theory ('default', 'exclusion', etc.)
        
    Returns:
        dict: Dictionary mapping semantic theory names to their implementation classes
        
    Raises:
        ValueError: If the theory is not registered or semantic theories cannot be loaded
        
    Example:
        >>> from model_checker.theory_lib import get_semantic_theories
        >>> semantics = get_semantic_theories('default')
        >>> # Access a specific semantic theory variant
        >>> bilateral = semantics.get('bilateral')
    """
    if theory_name not in AVAILABLE_THEORIES:
        raise ValueError(f"Unknown theory: {theory_name}")
    
    try:
        module = importlib.import_module(f".{theory_name}.examples", package=__name__)
        return module.semantic_theories
    except (ImportError, AttributeError) as e:
        raise ValueError(f"Could not load semantic theories for theory '{theory_name}': {str(e)}")

def discover_theories():
    """Discover available theories by scanning the directory structure.
    
    Identifies directories that have the required files to be considered a theory
    implementation (examples.py and operators.py). Used primarily for development
    to find unregistered theories.
    
    Returns:
        list: Alphabetically sorted list of discovered theory names
        
    Example:
        >>> from model_checker.theory_lib import discover_theories, AVAILABLE_THEORIES
        >>> discovered = discover_theories()
        >>> unregistered = [t for t in discovered if t not in AVAILABLE_THEORIES]
        >>> print(f"Unregistered theories found: {unregistered}")
    """
    current_dir = os.path.dirname(os.path.abspath(__file__))
    theories = []
    
    # Find directories containing both examples.py and operators.py
    for item in os.listdir(current_dir):
        if os.path.isdir(os.path.join(current_dir, item)) and not item.startswith('__'):
            examples_path = os.path.join(current_dir, item, 'examples.py')
            operators_path = os.path.join(current_dir, item, 'operators.py')
            if os.path.exists(examples_path) and os.path.exists(operators_path):
                theories.append(item)
    
    return sorted(theories)

# Public API
__all__ = [
    'AVAILABLE_THEORIES',
    'get_examples',
    'get_test_examples',
    'get_semantic_theories',
    'discover_theories',
]

# Lazy loading implementation via __getattr__

def __getattr__(name):
    """Lazily load theory modules when accessed.
    
    This special method implements Python's attribute lookup protocol.
    When a module attribute is requested that doesn't exist in globals(),
    Python calls this method to resolve it.
    
    Args:
        name (str): Name of the requested attribute
        
    Returns:
        module: The imported theory module if the name matches a registered theory
        
    Raises:
        AttributeError: If the name is not a registered theory
        
    Example:
        # This triggers __getattr__('default')
        from model_checker.theory_lib import default
    """
    if name in AVAILABLE_THEORIES:
        # Load and cache the module if not already loaded
        if name not in _theory_modules:
            try:
                module = importlib.import_module(f".{name}", package=__name__)
                _theory_modules[name] = module
            except ImportError as e:
                raise AttributeError(f"Failed to import theory '{name}': {str(e)}")
        return _theory_modules[name]
    
    raise AttributeError(f"module '{__name__}' has no attribute '{name}'")
