"""Validation utilities for model checker components.

This module provides functions for validating parameters and ensuring
proper types and values for model checking operations.
"""

from model_checker.model import (
    SemanticDefaults,
    PropositionDefaults,
    ModelDefaults,
)
from model_checker.syntactic import (
    OperatorCollection,
)

def validate_semantic_theory(semantic_theory):
    """Validate that a semantic theory contains all required components.
    
    Args:
        semantic_theory: Dictionary containing semantic theory implementation
        
    Returns:
        tuple: (semantics, proposition, operators, model_class) extracted from the theory
        
    Raises:
        TypeError: If any component is missing or has an invalid type
    """
    if not isinstance(semantic_theory, dict):
        raise TypeError(
            "semantic_theory must be a dictionary containing 'semantics', 'proposition', "
            "'operators', and 'model' components"
        )
        
    # Check required components
    for key in ['semantics', 'proposition', 'operators', 'model']:
        if key not in semantic_theory:
            raise TypeError(f"semantic_theory missing required component: {key}")
            
    semantics = semantic_theory["semantics"]
    proposition = semantic_theory["proposition"]
    operators = semantic_theory["operators"]
    model_class = semantic_theory["model"]
    
    # Validate semantics is subclass of SemanticDefaults
    if not issubclass(semantics, SemanticDefaults):
        raise TypeError(
            f"'semantics' must be a subclass of SemanticDefaults, got {type(semantics)}"
        )

    # Validate proposition is subclass of PropositionDefaults
    if not issubclass(proposition, PropositionDefaults):
        raise TypeError(
            f"'proposition' must be a subclass of PropositionDefaults, got {type(proposition)}"
        )

    # Validate operators is instance of OperatorCollection
    if not isinstance(operators, OperatorCollection):
        raise TypeError(
            f"'operators' must be an instance of OperatorCollection, got {type(operators)}"
        )

    # Validate model_class is subclass of ModelDefaults
    if not issubclass(model_class, ModelDefaults):
        raise TypeError(
            f"'model' must be a subclass of ModelDefaults, got {type(model_class)}"
        )
            
    return semantics, proposition, operators, model_class

def validate_example_case(example_case):
    """Validate an example case contains premises, conclusions and settings.
    
    Args:
        example_case: List/tuple containing [premises, conclusions, settings]
        
    Returns:
        tuple: (premises, conclusions, settings) from the example case
        
    Raises:
        TypeError: If example_case has invalid structure or types
    """
    if not isinstance(example_case, (list, tuple)) or len(example_case) != 3:
        raise TypeError(
            "example_case must be a list/tuple containing exactly 3 elements: "
            "[premises, conclusions, settings]"
        )
        
    premises, conclusions, settings = example_case
    
    # Validate premises is a list of strings
    if not isinstance(premises, list) or not all(isinstance(p, str) for p in premises):
        raise TypeError(
            f"premises must be a list of strings, got {type(premises)}"
        )
        
    # Validate conclusions is a list of strings
    if not isinstance(conclusions, list) or not all(isinstance(c, str) for c in conclusions):
        raise TypeError(
            f"conclusions must be a list of strings, got {type(conclusions)}"
        )
        
    # Validate settings is a dictionary
    if not isinstance(settings, dict):
        raise TypeError(
            f"settings must be a dictionary, got {type(settings)}"
        )
        
    return premises, conclusions, settings