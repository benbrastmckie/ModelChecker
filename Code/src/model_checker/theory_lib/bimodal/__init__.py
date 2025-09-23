"""This module exposes core classes and operators for bimodal logic model checking.

Bimodal logic combines temporal and modal logic, allowing for reasoning about
what is true at different times and in different possible worlds.

Classes:
    BimodalSemantics: Configures the semantic framework with temporal and modal operators
    BimodalProposition: Represents and evaluates formulas in temporal-modal contexts
    BimodalStructure: Manages world histories (sequences of states over time)
    BimodalModelIterator: Finds multiple distinct models for bimodal logic examples

Operators:
    bimodal_operators: Collection of logical operators including:
        - Extensional: ¬ (neg), ∧ (and), ∨ (or), → (conditional), ↔ (biconditional)
        - Modal: □ (necessity), ◇ (possibility)
        - Temporal: ⏵ (future), ⏴ (past)
        - Extremal: ⊤ (top), ⊥ (bottom)

Functions:
    iterate_example: Find multiple distinct models for a bimodal logic example

Examples:
    Access examples through utility functions in theory_lib:
    - theory_lib.get_examples('bimodal'): Gets the example_range dictionary
    - theory_lib.get_semantic_theories('bimodal'): Gets semantic theory implementations

Usage:
    from model_checker.theory_lib.bimodal import BimodalSemantics, BimodalProposition, BimodalStructure
    from model_checker.theory_lib.bimodal import bimodal_operators
    from model_checker.theory_lib import get_examples

    # Create a semantics and model structure
    semantics = BimodalSemantics(settings)
    model = BimodalStructure(semantics)

    # Evaluate formulas
    prop = BimodalProposition(formula, model)
    result = prop.evaluate()
    
    # Find multiple models
    from model_checker.theory_lib.bimodal import iterate_example
    models = iterate_example(example, max_iterations=5)
    
    # Access examples
    examples = get_examples('bimodal')
"""

# Import specific items from semantic
from .semantic import (
    BimodalSemantics,
    BimodalProposition,
    BimodalStructure,
)

# Import operators collection
from .operators import bimodal_operators

# Import iteration functionality
from .iterate import BimodalModelIterator, iterate_example

__version__ = "1.0.0"

# Define the public API of the package

# Version information
__model_checker_version__ = "0.9.20"  # ModelChecker version this was built with
__all__ = [
    "BimodalSemantics",       # Configures semantic framework with temporal and modal operators
    "BimodalProposition",     # Represents and evaluates formulas in temporal-modal contexts
    "BimodalStructure",       # Manages world histories (sequences of states over time)
    "bimodal_operators",      # Logical operators (¬,∧,∨,→,↔,□,◇,⏵,⏴,etc.)
    "BimodalModelIterator",   # Iterator for finding multiple distinct models
    "iterate_example",        # Function to find multiple distinct models
    "__version__",            # Package version information,
    "__model_checker_version__",  # Compatible ModelChecker version
    "get_theory",
    "get_examples",
    "get_test_examples",
    "print_example_report"
]


def get_theory(config=None):
    """Get bimodal theory configuration.
    
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
        "semantics": BimodalSemantics,
        "proposition": BimodalProposition,
        "model": BimodalStructure,
        "operators": bimodal_operators
    }


def get_examples():
    """Get bimodal theory example range.
    
    Returns:
        dict: Mapping of example names to example cases
    """
    from .examples import example_range
    return example_range


def get_test_examples():
    """Get bimodal theory test example range.
    
    Returns:
        dict: Mapping of test names to test cases
    """
    from .examples import test_example_range
    return test_example_range


def print_example_report():
    """
    Print a summary report of the bimodal theory examples that were run.
    """
    from .examples import example_range, unit_tests
    
    print("\n" + "=" * 80)
    print("BIMODAL THEORY EXAMPLE REPORT")
    print("=" * 80)
    
    # Count active examples
    active_examples = len(example_range)
    total_available = len(unit_tests)
    
    print(f"\nActive Examples: {active_examples} of {total_available} available")
    
    # Separate countermodels and theorems by category
    active_cms = [name for name in example_range if '_CM_' in name]
    active_ths = [name for name in example_range if '_TH_' in name]
    
    # Further categorize by type
    extensional = [name for name in example_range if name.startswith('EX_')]
    modal = [name for name in example_range if name.startswith('MD_')]
    tense = [name for name in example_range if name.startswith('TN_')]
    bimodal = [name for name in example_range if name.startswith('BM_')]
    
    if active_cms:
        print(f"  Countermodels: {len(active_cms)}")
        if extensional:
            ext_cms = [n for n in extensional if '_CM_' in n]
            if ext_cms:
                print(f"    Extensional: {', '.join(sorted(ext_cms))}")
        if modal:
            mod_cms = [n for n in modal if '_CM_' in n]
            if mod_cms:
                print(f"    Modal: {', '.join(sorted(mod_cms))}")
        if tense:
            tense_cms = [n for n in tense if '_CM_' in n]
            if tense_cms:
                print(f"    Tense: {', '.join(sorted(tense_cms))}")
        if bimodal:
            bi_cms = [n for n in bimodal if '_CM_' in n]
            if bi_cms:
                print(f"    Bimodal: {', '.join(sorted(bi_cms))}")
    
    if active_ths:
        print(f"  Theorems: {len(active_ths)}")
        if extensional:
            ext_ths = [n for n in extensional if '_TH_' in n]
            if ext_ths:
                print(f"    Extensional: {', '.join(sorted(ext_ths))}")
        if modal:
            mod_ths = [n for n in modal if '_TH_' in n]
            if mod_ths:
                print(f"    Modal: {', '.join(sorted(mod_ths))}")
        if tense:
            tense_ths = [n for n in tense if '_TH_' in n]
            if tense_ths:
                print(f"    Tense: {', '.join(sorted(tense_ths))}")
        if bimodal:
            bi_ths = [n for n in bimodal if '_TH_' in n]
            if bi_ths:
                print(f"    Bimodal: {', '.join(sorted(bi_ths))}")
    
    print("\n" + "-" * 80)
    print("Theory: Bimodal (Two Orthogonal S5 Modalities)")
    print("Authors: Benjamin Brast-McKie")
    print("Implementation: Benjamin Brast-McKie, Miguel Buitrago")
    print("-" * 80)
    
    print("\nFor more information, see:")
    print("  - Theory documentation: src/model_checker/theory_lib/bimodal/README.md")
    print("  - General usage guide: Docs/usage/README.md")
    print("=" * 80)
