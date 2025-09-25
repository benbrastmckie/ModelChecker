#!/usr/bin/env python3
"""Test operator loading in project_eleven."""

import sys
sys.path.insert(0, '/Users/nicky/Documents/ModelChecker/Code/src')

# Test 1: Load the module and check operators
from model_checker.builder.loader import ModuleLoader

print("Loading project_eleven counterfactual examples...")
test_file = "/Users/nicky/Documents/project_eleven/subtheories/counterfactual/examples.py"
loader = ModuleLoader("examples", test_file)
module = loader.load_module()

print(f"Module loaded: {module.__name__}")

# Check what's in the module
if hasattr(module, 'semantic_theories'):
    print(f"Has semantic_theories: {list(module.semantic_theories.keys())}")
    for theory_name, theory in module.semantic_theories.items():
        if 'operators' in theory:
            ops = theory['operators']
            print(f"  {theory_name} operators type: {type(ops)}")
            if hasattr(ops, 'operators'):
                print(f"    Operators: {[op.symbol for op in ops.operators]}")
            else:
                print(f"    Operators object: {ops}")

# Check if LogosOperatorRegistry was imported
if hasattr(module, 'LogosOperatorRegistry'):
    print(f"Has LogosOperatorRegistry: {module.LogosOperatorRegistry}")

# Check example_range
if hasattr(module, 'example_range'):
    print(f"Example range keys: {list(module.example_range.keys())[:5]}...")
    # Check first example
    first_key = list(module.example_range.keys())[0]
    first_example = module.example_range[first_key]
    print(f"First example ({first_key}): premises={first_example.get('premises', [])} conclusions={first_example.get('conclusions', [])}")