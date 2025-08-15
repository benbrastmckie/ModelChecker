"""
Witness negation theory implementation.

This module implements Strategy E1: Witnesses as Model Predicates, which makes
witness functions first-class citizens of the model structure. Instead of trying
to extract or reconstruct witness functions, they simply exist as queryable
predicates alongside verify and exclude.
"""

__version__ = "1.0.0"
__model_checker_version__ = "0.9.20"  # ModelChecker version this was built with

from .semantic import WitnessSemantics, WitnessModelAdapter, WitnessProposition, WitnessStructure, WitnessAwareModel, WitnessRegistry, WitnessConstraintGenerator
from .operators import witness_operators
from .iterate import ExclusionModelIterator, iterate_example, iterate_example_generator

# For ModelChecker discovery
DefaultSemantics = WitnessSemantics

# Legacy alias for compatibility
ExclusionStructure = WitnessStructure

__all__ = [
    'WitnessSemantics', 
    'WitnessModelAdapter', 
    'WitnessProposition', 
    'WitnessStructure',
    'WitnessAwareModel',
    'WitnessRegistry',
    'WitnessConstraintGenerator',
    'witness_operators', 
    'DefaultSemantics',
    'ExclusionStructure',  # Legacy alias
    'ExclusionModelIterator',
    'iterate_example',
    'iterate_example_generator',
    'get_theory',
    'get_examples', 
    'get_test_examples'
]


def get_theory(config=None):
    """Get exclusion theory configuration.
    
    Args:
        config: Optional configuration (currently unused)
        
    Returns:
        dict: Theory configuration with semantics, proposition, model, and operators
        
    Examples:
        >>> theory = get_theory()
        >>> 'semantics' in theory
        True
        >>> 'operators' in theory
        True
    """
    return {
        "semantics": WitnessSemantics,
        "proposition": WitnessProposition,
        "model": WitnessStructure, 
        "operators": witness_operators
    }


def get_examples():
    """Get exclusion theory example range.
    
    Returns:
        dict: Mapping of example names to example cases
    """
    from .examples import example_range
    return example_range


def get_test_examples():
    """Get exclusion theory test example range.
    
    Returns:
        dict: Mapping of test names to test cases
    """
    from .examples import test_example_range
    return test_example_range