"""This module exposes core classes and operators for imposition semantics model checking.

Imposition semantics implements Fine's semantics for counterfactuals through
the imposition operation, which imposes a state upon a world in a semantically
significant way.

Classes:
    ImpositionSemantics: Configures semantic framework with imposition operations

Operators:
    imposition_operators: Dictionary of logical operators including:
        - Extensional: ¬ (neg), ∧ (and), ∨ (or), → (conditional), ↔ (biconditional)
        - Imposition: ↪ (imposition), ⟂ (could)
        - Extremal: ⊤ (top), ⊥ (bottom)

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
    
    # Access examples
    examples = get_examples('imposition')
"""

__version__ = "unknown"

# Import specific items from semantic
from .semantic import (
    ImpositionSemantics,
)

# Import all operators
from .operators import imposition_operators

# Define the public API of the package
__all__ = [
    "ImpositionSemantics",  # Semantic framework with imposition operations
    "imposition_operators", # Logical operators including imposition (↪) and could (⟂)
    "__version__",          # Package version information
]
