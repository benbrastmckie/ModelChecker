"""Test script for iterate=2 functionality across theories."""

# Import semantic classes
from src.model_checker.theory_lib.logos.semantic import (
    LogosSemantics,
    LogosProposition,
    LogosModelStructure,
)

# Import operators
from src.model_checker.theory_lib.logos.operators import LogosOperatorRegistry

# Create operator registry
test_registry = LogosOperatorRegistry()

# Define test examples with iterate=2
TEST_ITERATE_premises = ['A']
TEST_ITERATE_conclusions = ['B']
TEST_ITERATE_settings = {
    'N': 3,
    'contingent': False,
    'non_null': False,
    'disjoint': False,
    'non_empty': False,  
    'max_time': 10,
    'print_impossible': False,
    'print_constraints': False,
    'expectation': True,
    'print_z3': False,
    'iterate': 2,  # This should trigger iteration
}
TEST_ITERATE_example = [
    TEST_ITERATE_premises,
    TEST_ITERATE_conclusions,
    TEST_ITERATE_settings,
]

# Create theory dictionary
unit_tests = {
    "TEST_ITERATE": TEST_ITERATE_example,
}

# Create theory configuration
test_theory = {
    "semantics": LogosSemantics,
    "proposition": LogosProposition,
    "model": LogosModelStructure,
    "operators": test_registry.get_operators(),
}

# Required: semantic_theories
semantic_theories = {
    "Primary": test_theory,
}

# Required: example_range
example_range = unit_tests