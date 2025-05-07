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
        - Imposition: ↪ (imposition), ⟂ (could)
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

# Import version utilities
from model_checker.utils import get_model_checker_version

    # Create a semantics and model structure
    semantics = ImpositionSemantics(settings)
    
    # Find multiple models
    from model_checker.theory_lib.imposition import iterate_example
    models = iterate_example(example, max_iterations=5)
    
    # Access examples
    examples = get_examples('imposition')
"""

# Import version utilities
from model_checker.utils import get_model_checker_version

__version__ = "1.0.0"

# Import specific items from semantic
from .semantic import (
    ImpositionSemantics,
)

# Import version utilities
from model_checker.utils import get_model_checker_version

# Import all operators
from .operators import imposition_operators

# Import version utilities
from model_checker.utils import get_model_checker_version

# Import iteration functionality
from .iterate import ImpositionModelIterator, iterate_example

# Import version utilities
from model_checker.utils import get_model_checker_version

# Define the public API of the package

# Version information
__model_checker_version__ = "0.9.20"  # ModelChecker version this was built with
__all__ = [
    "ImpositionSemantics",    # Semantic framework with imposition operations
    "imposition_operators",   # Logical operators including imposition (↪) and could (⟂)
    "ImpositionModelIterator", # Iterator for finding multiple distinct models
    "iterate_example",        # Function to find multiple distinct models
    "__version__",            # Package version information,
    "__model_checker_version__",  # Compatible ModelChecker version
]
