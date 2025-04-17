"""This module exposes core classes and operators for exclusion semantics model checking.

Exclusion semantics implements a unilateral approach to semantic verification based on
the work of Bernard and Champollion, focusing on exclusion relations between states.

Classes:
    ExclusionSemantics: Configures the exclusion semantics framework and evaluation rules
    UnilateralProposition: Represents and evaluates formulas using unilateral verification
    ExclusionStructure: Manages the model structure with exclusion relations
    ExclusionModelIterator: Finds multiple distinct models for exclusion semantics examples

Operators:
    exclusion_operators: Dictionary of unilateral logical operators including:
        - Unilateral: ⊻ (exclude), ⊓ (uniwedge), ⊔ (univee), ≔ (uniequiv)
        - Extremal: ⊤ (top), ⊥ (bottom)

Functions:
    iterate_example: Find multiple distinct models for an exclusion semantics example

Examples:
    Access examples through utility functions in theory_lib:
    - theory_lib.get_examples('exclusion'): Gets the example_range dictionary
    - theory_lib.get_test_examples('exclusion'): Gets test example cases
    - theory_lib.get_semantic_theories('exclusion'): Gets semantic theory implementations

Usage:
    from model_checker.theory_lib.exclusion import ExclusionSemantics, UnilateralProposition, ExclusionStructure
    from model_checker.theory_lib.exclusion import exclusion_operators
    from model_checker.theory_lib import get_examples

    # Create a semantics and model structure
    semantics = ExclusionSemantics(settings)
    model = ExclusionStructure(semantics)

    # Evaluate formulas
    prop = UnilateralProposition(formula, model)
    result = prop.evaluate()
    
    # Find multiple models
    from model_checker.theory_lib.exclusion import iterate_example
    models = iterate_example(example, max_iterations=5)
    
    # Access examples
    examples = get_examples('exclusion')
"""

__version__ = "unknown"

# Import specific items from semantic
from .semantic import (
    ExclusionSemantics,
    UnilateralProposition,
    ExclusionStructure,
)

# Import all operators
from .operators import exclusion_operators

# Import iteration functionality
from .iterate import ExclusionModelIterator, iterate_example

# Define the public API of the package
__all__ = [
    "ExclusionSemantics",     # Exclusion semantics framework and evaluation rules
    "UnilateralProposition",  # Represents formulas with unilateral verification
    "ExclusionStructure",     # Manages model structure with exclusion relations
    "exclusion_operators",    # Unilateral logical operators (⊻,⊓,⊔,≔,etc.)
    "ExclusionModelIterator", # Iterator for finding multiple distinct models
    "iterate_example",        # Function to find multiple distinct models
    "__version__",            # Package version information
]
