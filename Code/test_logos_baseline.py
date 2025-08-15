#!/usr/bin/env python3
"""Test script to capture baseline logos iteration behavior."""

import sys
from model_checker.builder.example import BuildExample
from model_checker.theory_lib.logos import get_theory, iterate_example_generator
from model_checker.theory_lib.logos.operators import LogosOperatorRegistry
from unittest.mock import Mock
from types import SimpleNamespace

# Get logos theory with operators loaded
registry = LogosOperatorRegistry()
registry.load_subtheories(['modal'])  # Load modal operators

theory = {
    'semantics': get_theory()['semantics'],
    'proposition': get_theory()['proposition'],
    'model': get_theory()['model'],
    'operators': registry.get_operators(),
    'name': 'Logos'
}

# Create properly mocked BuildModule
module = Mock()
module.theory_name = 'logos'
module.semantic_theories = {"logos": theory}
module.raw_general_settings = {}
module.general_settings = {}
module.module_flags = SimpleNamespace()

# Example case with modal operator that should show differences
example_case = [
    ["\\Box A"],            # premises
    ["\\Box B"],            # conclusions - should fail
    {"N": 3, "iterate": 3}  # settings with iteration requested
]

print("=== Testing Logos Theory Iteration (Baseline) ===")
print(f"Premises: {example_case[0]}")
print(f"Conclusions: {example_case[1]}")
print(f"Settings: {example_case[2]}")
print()

# Build example - this creates the initial model
example = BuildExample(module, theory, example_case, 'logos')

# Test generator interface
gen = iterate_example_generator(example, max_iterations=3)

models = []
for i, model in enumerate(gen):
    models.append(model)
    print(f"\n=== Model {i+1} ===")
    # Print basic model info
    if hasattr(model, 'print_model'):
        model.print_model()
    else:
        print("(Model structure without print method)")
        
print(f"\nTotal models found: {len(models)}")