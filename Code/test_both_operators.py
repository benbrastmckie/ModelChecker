"""Test module to demonstrate using both imposition and logos counterfactual operators."""

from src.model_checker.theory_lib.imposition import (
    ImpositionSemantics, 
    Proposition, 
    ModelStructure,
    imposition_operators
)

# Semantic theories for the module
semantic_theories = {
    "Imposition": {
        "semantics": ImpositionSemantics,
        "proposition": Proposition,
        "model": ModelStructure,
        "operators": imposition_operators
    }
}

# Example: Compare imposition and logos counterfactuals
compare_premises = ["A", "B"]
compare_conclusions = [
    "(A \\boxright B)",          # Imposition counterfactual
    "(A \\boxrightlogos B)"      # Logos counterfactual
]
compare_settings = {
    "N": 3,
    "expectation": None,  # We'll see what happens
}
compare_example = [
    compare_premises,
    compare_conclusions,
    compare_settings,
]

# Example: Check if they're equivalent
equiv_premises = []
equiv_conclusions = [
    "((A \\boxright B) \\leftrightarrow (A \\boxrightlogos B))"
]
equiv_settings = {
    "N": 3,
    "expectation": None,
}
equiv_example = [
    equiv_premises,
    equiv_conclusions,
    equiv_settings,
]

# Example range
example_range = {
    "compare": compare_example,
    "equiv": equiv_example,
}

# Operators
operator_collection = imposition_operators