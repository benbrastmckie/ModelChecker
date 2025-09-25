#!/usr/bin/env python3
"""Debug the import chain for operators."""

import sys
import importlib
sys.path.insert(0, '/Users/nicky/Documents/project_eleven')

# Test importing the counterfactual subtheory
print("--- Testing counterfactual import ---")
cf_module = importlib.import_module('subtheories.counterfactual', package=None)
print(f"Module: {cf_module}")
print(f"Has get_operators: {hasattr(cf_module, 'get_operators')}")

if hasattr(cf_module, 'get_operators'):
    ops = cf_module.get_operators()
    print(f"get_operators returns: {ops}")
    print(f"Operators: {list(ops.keys())}")

# Now test using the registry
print("\n--- Testing via LogosOperatorRegistry ---")
from operators import LogosOperatorRegistry

registry = LogosOperatorRegistry()
print("Initial operator count:", len(registry.operator_collection.operator_dictionary))

# Load just counterfactual
print("\nLoading counterfactual subtheory...")
try:
    cf_mod = registry.load_subtheory('counterfactual')
    print(f"Loaded: {cf_mod}")
    print(f"Loaded subtheories: {list(registry.loaded_subtheories.keys())}")
    print(f"Operator count after loading: {len(registry.operator_collection.operator_dictionary)}")

    ops_coll = registry.get_operators()
    if '\\boxright' in ops_coll.operator_dictionary:
        print("✓ \\boxright found after loading counterfactual")
    else:
        print("✗ \\boxright NOT found after loading counterfactual")
        print(f"Available: {list(ops_coll.operator_dictionary.keys())}")
except Exception as e:
    print(f"Error: {e}")
    import traceback
    traceback.print_exc()