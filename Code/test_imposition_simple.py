"""Simple test for imposition relation printing."""

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

# Example: A simple counterfactual
test_imposition_premises = ["A"]
test_imposition_conclusions = ["A \\imposition B"]  # If A then must B
test_imposition_settings = {
    "N": 2,
    "expectation": False,  # We expect a countermodel
}
test_imposition_example = [
    test_imposition_premises,
    test_imposition_conclusions,
    test_imposition_settings,
]

# Example range
example_range = {
    "test_imposition": test_imposition_example
}

# Operators
operator_collection = imposition_operators