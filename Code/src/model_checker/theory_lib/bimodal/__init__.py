"""This module exposes core classes and operators for bimodal logic model checking.

Bimodal logic combines temporal and modal logic, allowing for reasoning about
what is true at different times and in different possible worlds.

Classes:
    BimodalSemantics: Configures the semantic framework with temporal and modal operators
    BimodalProposition: Represents and evaluates formulas in temporal-modal contexts
    BimodalStructure: Manages world histories (sequences of states over time)

Operators:
    bimodal_operators: Collection of logical operators including:
        - Extensional: ¬ (neg), ∧ (and), ∨ (or), → (conditional), ↔ (biconditional)
        - Modal: □ (necessity), ◇ (possibility)
        - Temporal: ⏵ (future), ⏴ (past)
        - Extremal: ⊤ (top), ⊥ (bottom)

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

# Import examples for access through the API
from .examples import (
    example_range,
    semantic_theories,
    test_example_range,
)

__version__ = "unknown"

# Define the public API of the package
__all__ = [
    "BimodalSemantics",      # Configures semantic framework with temporal and modal operators
    "BimodalProposition",    # Represents and evaluates formulas in temporal-modal contexts
    "BimodalStructure",      # Manages world histories (sequences of states over time)
    "bimodal_operators", # Logical operators (¬,∧,∨,→,↔,□,◇,⏵,⏴,etc.)
    "example_range",         # Dictionary of example test cases
    "semantic_theories",     # Dictionary of semantic theory implementations
    "test_example_range",    # Dictionary of examples used for automated testing
    "__version__",           # Package version information
]
