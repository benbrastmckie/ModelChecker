"""This module exposes core classes and operators for modal logic model checking:

Classes:
    Semantics: Configures the semantic framework and evaluation rules
    Proposition: Represents and evaluates logical formulas
    ModelStructure: Manages the model's state space and accessibility relations

Operators:
    default_operators: Dictionary of standard logical operators including:
        - Extensional: ¬ (not), ∧ (and), ∨ (or), → (if), ←→ (iff)
        - Modal: □ (necessary), ◇ (possible)
        - Counterfactual: □→ (would), ◇→ (might)
        - Constitutive: ≡ (identical), ≤ (grounds), ⊑ (essence)

Examples:
    Access examples through utility functions in theory_lib:
    - theory_lib.get_examples('default'): Gets the example_range dictionary
    - theory_lib.get_test_examples('default'): Gets test example cases
    - theory_lib.get_semantic_theories('default'): Gets semantic theory implementations

Usage:
    from model_checker.theory_lib.default import Semantics, Proposition, ModelStructure
    from model_checker.theory_lib.default import default_operators
    from model_checker.theory_lib import get_examples

    # Create a semantics and model structure
    semantics = Semantics(settings)
    model = ModelStructure(semantics)

    # Evaluate formulas
    prop = Proposition(formula, model)
    result = prop.evaluate()
    
    # Access examples
    examples = get_examples('default')
"""

# Import specific items from semantic
from .semantic import (
    Semantics,
    Proposition,
    ModelStructure,
)

# Import all operators
from .operators import default_operators

__version__ = "unknown"

# Define the public API of the package
__all__ = [
    "Semantics",         # Configures semantic framework and evaluation rules
    "Proposition",       # Represents and evaluates logical formulas
    "ModelStructure",    # Manages model's state space and accessibility relations
    "default_operators", # Standard logical operators (¬,∧,∨,→,←→,□,◇,etc.)
    "__version__",       # Package version information
]
