"""Module to test imposition relation printing."""

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

# Example: Counterfactual modus ponens (should be valid)
cf_mp_premises = ["A", "A \\imposition B"]
cf_mp_conclusions = ["B"]
cf_mp_settings = {
    "N": 2,
    "expectation": True,  # We expect validity (no countermodel)
}
cf_mp_example = [
    cf_mp_premises,
    cf_mp_conclusions,
    cf_mp_settings,
]

# Example: Antecedent strengthening (should have countermodel)
ant_str_premises = ["A \\imposition C"]
ant_str_conclusions = ["(A \\wedge B) \\imposition C"]
ant_str_settings = {
    "N": 3,
    "expectation": False,  # We expect a countermodel
}
ant_str_example = [
    ant_str_premises,
    ant_str_conclusions,
    ant_str_settings,
]

# Example range
example_range = {
    "cf_mp": cf_mp_example,
    "ant_str": ant_str_example,
}

# Operators
operator_collection = imposition_operators