"""
API utility functions for accessing theories and examples.

This module provides functions for retrieving theories and examples from the
model checker's theory library.
"""


def get_example(name, example_range):
    """Get a specific example by name from the provided example range.
    
    Args:
        name (str): Name of the example to retrieve
        example_range (dict): Dictionary containing the examples
        
    Returns:
        list: [premises, conclusions, settings]
        
    Raises:
        KeyError: If the example name is not found
    """
    if name not in example_range:
        raise KeyError(f"Example {name} not found. Available examples: {list(example_range.keys())}")
    return example_range[name]


def get_theory(name, semantic_theories=None):
    """Get a specific semantic theory by name.
    
    This function can be called in two ways:
    1. With just the theory name (e.g., 'default') - will automatically load the semantic theories
    2. With both name and semantic_theories - useful when you already have the semantic theories loaded
    
    Args:
        name (str): Name of the theory to retrieve (e.g., 'default', 'exclusion')
        semantic_theories (dict, optional): Dictionary containing semantic theories. 
                                           If None, will be loaded automatically.
        
    Returns:
        dict: Dictionary containing semantics, proposition, model, and operators
        
    Raises:
        ValueError: If the theory name is not found or the theory_lib module can't be loaded
        KeyError: If the specific theory is not found in the semantic_theories
    """
    # If semantic_theories is not provided, try to load it
    if semantic_theories is None:
        try:
            # Import here to avoid circular imports
            from model_checker.theory_lib import get_semantic_theories
            semantic_theories = get_semantic_theories(name)
        except ImportError as e:
            available_theories = []
            try:
                from model_checker.theory_lib import AVAILABLE_THEORIES
                available_theories = AVAILABLE_THEORIES
            except ImportError:
                pass
            
            raise ValueError(f"Could not load theory_lib module. Available theories: {available_theories}") from e
        except ValueError as e:
            raise ValueError(f"Theory '{name}' not found in theory_lib") from e
    
    # For theories with only one variant, return that variant regardless of name
    if len(semantic_theories) == 1:
        return list(semantic_theories.values())[0]
    
    # Standard case - look up the theory by name
    if name not in semantic_theories:
        raise KeyError(f"Theory '{name}' not found. Available theories: {list(semantic_theories.keys())}")
    
    return semantic_theories[name]