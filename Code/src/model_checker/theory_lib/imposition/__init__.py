"""This module exposes core classes and operators for imposition semantics model checking.

Imposition semantics implements Fine's semantics for counterfactuals through
the imposition operation, which imposes a state upon a world in a semantically
significant way.

Classes:
    ImpositionSemantics: Configures semantic framework with imposition operations
    ImpositionModelIterator: Finds multiple distinct models for imposition semantics examples

Operators:
    imposition_operators: Dictionary of logical operators including:
        - Extensional: ¬ (neg), ∧ (and), ∨ (or), → (conditional), ↔ (biconditional)
        - Imposition: ▷ (boxright), ◇▷ (diamondright)
        - Extremal: ⊤ (top), ⊥ (bottom)

Functions:
    iterate_example: Find multiple distinct models for an imposition semantics example

Examples:
    Access examples through utility functions in theory_lib:
    - theory_lib.get_examples('imposition'): Gets the example_range dictionary
    - theory_lib.get_test_examples('imposition'): Gets test example cases
    - theory_lib.get_semantic_theories('imposition'): Gets semantic theory implementations

Usage:
    from model_checker.theory_lib.imposition import ImpositionSemantics
    from model_checker.theory_lib.imposition import imposition_operators
    from model_checker.theory_lib import get_examples


    # Create a semantics and model structure
    semantics = ImpositionSemantics(settings)
    
    # Find multiple models
    from model_checker.theory_lib.imposition import iterate_example
    models = iterate_example(example, max_iterations=5)
    
    # Access examples
    examples = get_examples('imposition')
"""

from .examples import example_range, unit_tests, test_example_range
from .iterate import ImpositionModelIterator, iterate_example, iterate_example_generator
from .operators import imposition_operators
from .semantic import (
    ImpositionSemantics,
    ImpositionModelStructure as ModelStructure,
)

__version__ = "1.0.0"

# Import Proposition from logos for reuse
from model_checker.theory_lib.logos.semantic import LogosProposition as Proposition

# Import all operators

# Import iteration functionality

# Define the public API of the package

# Version information
__model_checker_version__ = "0.9.20"  # ModelChecker version this was built with
__all__ = [
    "ImpositionSemantics",    # Semantic framework with imposition operations
    "Proposition",            # Reused from logos for consistency
    "ModelStructure",         # Custom model structure with imposition printing
    "imposition_operators",   # Logical operators including boxright (▷) and diamondright (◇▷)
    "ImpositionModelIterator", # Iterator for finding multiple distinct models
    "iterate_example",        # Function to find multiple distinct models
    "iterate_example_generator", # Generator version for incremental display
    "__version__",            # Package version information,
    "__model_checker_version__",  # Compatible ModelChecker version
    "get_theory",
    "get_examples",
    "get_test_examples",
    "print_example_report"
]


def get_theory(config=None):
    """Get imposition theory configuration.
    
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
        "semantics": ImpositionSemantics,
        "proposition": Proposition,
        "model": ModelStructure,
        "operators": imposition_operators
    }


def get_examples():
    """
    Get all imposition examples.
    
    Returns:
        dict: Dictionary containing all imposition examples with categories:
            - 'countermodels': Counter-examples showing invalidity
            - 'theorems': Valid theorems
            - 'all': All examples combined
    """
    
    return {
        'countermodels': imposition_cm_examples,
        'theorems': imposition_th_examples,
        'all': unit_tests
    }


def get_test_examples():
    """Get imposition theory test example range.
    
    Returns:
        dict: Mapping of test names to test cases
    """
    return test_example_range


def print_example_report():
    """
    Print a summary report of the imposition theory examples that were run.
    """
    
    print("\n" + "=" * 80)
    print("IMPOSITION THEORY EXAMPLE REPORT")
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
    print("Theory: Imposition (Bilateral Semantics)")
    print("Author: Kit Fine")
    print("Implementation: Benjamin Brast-McKie, Miguel Buitrago")
    print("-" * 80)
    
    print("\nFor more information, see:")
    print("  - Theory documentation: src/model_checker/theory_lib/imposition/README.md")
    print("  - General usage guide: Docs/usage/README.md")
    print("=" * 80)
