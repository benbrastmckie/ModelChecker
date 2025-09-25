#!/usr/bin/env python3
"""Test the operator registry directly."""

import sys
sys.path.insert(0, '/Users/nicky/Documents/project_eleven')

# Import the registry from project_eleven
from operators import LogosOperatorRegistry

# Create a registry and load counterfactual operators
registry = LogosOperatorRegistry()
print("Loading subtheories: extensional, modal, counterfactual")
registry.load_subtheories(['extensional', 'modal', 'counterfactual'])

# Get the operators
ops_collection = registry.get_operators()
print(f"\nOperator Collection type: {type(ops_collection)}")

# Check what operators are available
if hasattr(ops_collection, 'operator_dictionary'):
    print(f"Operator dictionary keys: {list(ops_collection.operator_dictionary.keys())}")
    if '\\boxright' in ops_collection.operator_dictionary:
        print("✓ \\boxright found!")
    else:
        print("✗ \\boxright NOT found")

# Try loading just counterfactual to see what it adds
registry2 = LogosOperatorRegistry()
print("\n--- Testing just counterfactual subtheory ---")
registry2.load_subtheories(['counterfactual'])
ops2 = registry2.get_operators()
if hasattr(ops2, 'operator_dictionary'):
    print(f"Counterfactual-only operators: {list(ops2.operator_dictionary.keys())}")

# Check if the counterfactual subtheory module has the operators
print("\n--- Checking counterfactual module directly ---")
from subtheories.counterfactual.operators import COUNTERFACTUAL_OPERATORS
print(f"COUNTERFACTUAL_OPERATORS has {len(COUNTERFACTUAL_OPERATORS)} operators")
for op in COUNTERFACTUAL_OPERATORS:
    print(f"  - {op.symbol}: {op.name}")