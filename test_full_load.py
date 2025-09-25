#!/usr/bin/env python3
"""Test full loading with debugging."""

import sys
sys.path.insert(0, '/Users/nicky/Documents/ModelChecker/Code/src')
sys.path.insert(0, '/Users/nicky/Documents/project_eleven')

# Import the counterfactual examples module
from model_checker.builder.loader import ModuleLoader
loader = ModuleLoader("examples", "/Users/nicky/Documents/project_eleven/subtheories/counterfactual/examples.py")
module = loader.load_module()

print(f"Module loaded: {module.__name__}")
print(f"Module __package__: {module.__package__}")

# Try to manually execute the registry creation
print("\n--- Testing manual registry creation ---")
from project_eleven.operators import LogosOperatorRegistry
registry = LogosOperatorRegistry()

# Check __package__ in the context
import project_eleven.operators as op_module
print(f"operators module __package__: {op_module.__package__}")

try:
    registry.load_subtheories(['extensional', 'modal', 'counterfactual'])
    ops = registry.get_operators()
    print(f"Successfully loaded operators")
    if hasattr(ops, 'operator_dictionary'):
        print(f"Operator count: {len(ops.operator_dictionary)}")
        if '\\boxright' in ops.operator_dictionary:
            print("✓ \\boxright found!")
        else:
            print("✗ \\boxright not found")
            print("Available operators:", list(ops.operator_dictionary.keys()))
except Exception as e:
    print(f"Failed to load operators: {e}")
    import traceback
    traceback.print_exc()