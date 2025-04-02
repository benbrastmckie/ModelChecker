"""This module exposes core classes and operators for modal logic model checking:

Classes:
    Semantics: Configures the semantic framework and evaluation rules
    Proposition: Represents and evaluates logical formulas
    ModelStructure: Manages the model's state space and accessibility relations

Operators:
    default_operators: Dictionary of standard logical operators including:
        - Extensional: ¬ (not), ∧ (and), ∨ (or), → (if), ↔ (iff)
        - Modal: □ (necessary), ◇ (possible)
        - Counterfactual: □→ (would), ◇→ (might)
        - Constitutive: ≡ (identical), ≤ (grounds), ⊑ (essence)

Usage:
    from model_checker.theory_lib.default import Semantics, Proposition, ModelStructure
    from model_checker.theory_lib.default import default_operators

    # Create a semantics and model structure
    semantics = Semantics(settings)
    model = ModelStructure(semantics)

    # Evaluate formulas
    prop = Proposition(formula, model)
    result = prop.evaluate()
"""

__version__ = "0.0.1"

# Define the public API of the package
__all__ = [
    "Semantics", "Proposition", "ModelStructure",  # semantic
    "default_operators",  # operators
]

# Import specific items from semantic
from .semantic import (
    Semantics,
    Proposition,
    ModelStructure,
)

# Import all operators
from .operators import default_operators

# NOTE: this will cause circular imports
# from .examples import example_range
