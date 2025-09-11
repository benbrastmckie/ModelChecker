"""Validation utilities for model checker components.

This module provides functions for validating parameters and ensuring
proper types and values for model checking operations.
"""

from typing import Dict, List, Tuple, Any, Type

from ..models.semantic import SemanticDefaults
from ..models.proposition import PropositionDefaults
from ..models.structure import ModelDefaults
from ..syntactic import (
    OperatorCollection,
)

from .error_types import ValidationError
from .types import TheoryDict, ExampleSpec

def validate_semantic_theory(semantic_theory: TheoryDict) -> Tuple[Type[SemanticDefaults], Type[PropositionDefaults], OperatorCollection, Type[ModelDefaults]]:
    """Validate that a semantic theory contains all required components.
    
    Args:
        semantic_theory: Dictionary containing semantic theory implementation
        
    Returns:
        tuple: (semantics, proposition, operators, model_class) extracted from the theory
        
    Raises:
        TypeError: If any component is missing or has an invalid type
    """
    if not isinstance(semantic_theory, dict):
        raise ValidationError(
            "semantic_theory",
            "must be a dictionary",
            "dict containing 'semantics', 'proposition', 'operators', and 'model' components"
        )
        
    # Check required components
    for key in ['semantics', 'proposition', 'operators', 'model']:
        if key not in semantic_theory:
            raise ValidationError(
                "semantic_theory",
                f"missing required component: {key}",
                "all of: semantics, proposition, operators, model"
            )
            
    semantics = semantic_theory["semantics"]
    proposition = semantic_theory["proposition"]
    operators = semantic_theory["operators"]
    model_class = semantic_theory["model"]
    
    # Validate semantics is subclass of SemanticDefaults
    if not issubclass(semantics, SemanticDefaults):
        raise ValidationError(
            "semantics",
            f"must be a subclass of SemanticDefaults, got {type(semantics)}",
            "subclass of SemanticDefaults"
        )

    # Validate proposition is subclass of PropositionDefaults
    if not issubclass(proposition, PropositionDefaults):
        raise ValidationError(
            "proposition",
            f"must be a subclass of PropositionDefaults, got {type(proposition)}",
            "subclass of PropositionDefaults"
        )

    # Validate operators is instance of OperatorCollection
    if not isinstance(operators, OperatorCollection):
        raise ValidationError(
            "operators",
            f"must be an instance of OperatorCollection, got {type(operators)}",
            "instance of OperatorCollection"
        )

    # Validate model_class is subclass of ModelDefaults
    if not issubclass(model_class, ModelDefaults):
        raise ValidationError(
            "model",
            f"must be a subclass of ModelDefaults, got {type(model_class)}",
            "subclass of ModelDefaults"
        )
            
    return semantics, proposition, operators, model_class

def validate_example_case(example_case: Any) -> Tuple[List[str], List[str], Dict[str, Any]]:
    """Validate an example case contains premises, conclusions and settings.
    
    Args:
        example_case: List/tuple containing [premises, conclusions, settings]
        
    Returns:
        tuple: (premises, conclusions, settings) from the example case
        
    Raises:
        TypeError: If example_case has invalid structure or types
    """
    if not isinstance(example_case, (list, tuple)) or len(example_case) != 3:
        raise ValidationError(
            "example_case",
            f"must be a list/tuple with 3 elements, got {type(example_case)} with {len(example_case) if isinstance(example_case, (list, tuple)) else 'N/A'} elements",
            "list/tuple of [premises, conclusions, settings]"
        )
        
    premises, conclusions, settings = example_case
    
    # Validate premises is a list of strings
    if not isinstance(premises, list) or not all(isinstance(p, str) for p in premises):
        raise ValidationError(
            "premises",
            f"must be a list of strings, got {type(premises)}",
            "list of strings"
        )
        
    # Validate conclusions is a list of strings
    if not isinstance(conclusions, list) or not all(isinstance(c, str) for c in conclusions):
        raise ValidationError(
            "conclusions",
            f"must be a list of strings, got {type(conclusions)}",
            "list of strings"
        )
        
    # Validate settings is a dictionary
    if not isinstance(settings, dict):
        raise ValidationError(
            "settings",
            f"must be a dictionary, got {type(settings)}",
            "dictionary"
        )
        
    return premises, conclusions, settings