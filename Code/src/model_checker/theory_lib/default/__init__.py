"""This module exposes core classes and operators for modal logic model checking:

Classes:
    Semantics: Configures the semantic framework and evaluation rules
    Proposition: Represents and evaluates logical formulas
    ModelStructure: Manages the model's state space and accessibility relations
    DefaultModelIterator: Iterator for finding multiple distinct models

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
    from model_checker.theory_lib.default import iterate_example

    # Create a semantics and model structure
    semantics = Semantics(settings)
    model = ModelStructure(semantics)

    # Evaluate formulas
    prop = Proposition(formula, model)
    result = prop.evaluate()
    
    # Access examples
    examples = get_examples('default')
    
    # Find multiple models
    model_structures = iterate_example(example, max_iterations=5)
"""

# Import specific items from semantic
from .semantic import (
    Semantics,
    Proposition,
    ModelStructure,
)

# Import all operators
from .operators import default_operators

# Import iteration functionality
from .iterate import DefaultModelIterator, iterate_example

# Import version utilities
from model_checker.utils import get_model_checker_version

# Version information
__version__ = "1.0.0"  # Theory version
__model_checker_version__ = get_model_checker_version()  # ModelChecker version this was built with

# Define the public API of the package
__all__ = [
    "Semantics",                  # Configures semantic framework and evaluation rules
    "Proposition",                # Represents and evaluates logical formulas
    "ModelStructure",             # Manages model's state space and accessibility relations
    "default_operators",          # Standard logical operators (¬,∧,∨,→,←→,□,◇,etc.)
    "DefaultModelIterator",       # Iterator for finding multiple models
    "iterate_example",            # Function to find multiple models for an example
    "__version__",                # Theory version information
    "__model_checker_version__",  # Compatible ModelChecker version
]
