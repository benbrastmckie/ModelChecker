"""Test module for exclusion theory with new operator names."""

from src.model_checker.theory_lib.exclusion import (
    WitnessSemantics,
    WitnessProposition,
    WitnessStructure,
    witness_operators
)

# Semantic theories for the module
semantic_theories = {
    "Exclusion": {
        "semantics": WitnessSemantics,
        "proposition": WitnessProposition,
        "model": WitnessStructure,
        "operators": witness_operators
    }
}

# Example: Simple negation
neg_premises = ["A"]
neg_conclusions = ["\\neg A"]
neg_settings = {
    "N": 2,
    "expectation": False,  # We expect a countermodel
}
neg_example = [
    neg_premises,
    neg_conclusions,
    neg_settings,
]

# Example: Conjunction
conj_premises = ["A", "B"]
conj_conclusions = ["(A \\wedge B)"]
conj_settings = {
    "N": 2,
    "expectation": True,  # We expect validity
}
conj_example = [
    conj_premises,
    conj_conclusions,
    conj_settings,
]

# Example: Equivalence/Identity
equiv_premises = ["(A \\wedge B)"]
equiv_conclusions = ["((A \\wedge B) \\equiv (A \\wedge B))"]
equiv_settings = {
    "N": 2,
    "expectation": True,  # We expect validity (reflexivity of identity)
}
equiv_example = [
    equiv_premises,
    equiv_conclusions,
    equiv_settings,
]

# Example range
example_range = {
    "neg": neg_example,
    "conj": conj_example,
    "equiv": equiv_example,
}

# Operators
operator_collection = witness_operators