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
    'get_test_examples',
    'print_example_report'
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


def print_example_report():
    """
    Print a summary report of the exclusion theory examples that were run.
    """
    from .examples import example_range, unit_tests
    
    print("\n" + "=" * 80)
    print("EXCLUSION THEORY EXAMPLE REPORT")
    print("=" * 80)
    
    # Count active examples
    active_examples = len(example_range)
    total_available = len(unit_tests)
    
    print(f"\nActive Examples: {active_examples} of {total_available} available")
    
    # Separate countermodels and theorems
    active_cms = [name for name in example_range if '_CM_' in name]
    active_ths = [name for name in example_range if '_TH_' in name]
    
    if active_cms:
        print(f"  Countermodels: {len(active_cms)} - {', '.join(sorted(active_cms))}")
    if active_ths:
        print(f"  Theorems: {len(active_ths)} - {', '.join(sorted(active_ths))}")
    
    print("\n" + "-" * 80)
    print("Theory: Exclusion (Unilateral Semantics)")
    print("Authors: Lucas Champollion & Paul Bernard")
    print("Implementation: Benjamin Brast-McKie, Miguel Buitrago")
    print("-" * 80)
    
    print("\nFor more information, see:")
    print("  - Theory documentation: src/model_checker/theory_lib/exclusion/README.md")
    print("  - General usage guide: Docs/usage/README.md")
    print("=" * 80)