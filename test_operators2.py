#!/usr/bin/env python3
"""Test operator loading in project_eleven - detailed."""

import sys
sys.path.insert(0, '/Users/nicky/Documents/ModelChecker/Code/src')

from model_checker.builder.loader import ModuleLoader

print("Loading project_eleven counterfactual examples...")
test_file = "/Users/nicky/Documents/project_eleven/subtheories/counterfactual/examples.py"
loader = ModuleLoader("examples", test_file)
module = loader.load_module()

# Get the semantic theory
theory = module.semantic_theories['Brast-McKie']
ops_collection = theory['operators']

print(f"Operator Collection: {ops_collection}")
print(f"Operator dictionary keys: {list(ops_collection.operator_dictionary.keys())}")

# Check if boxright is there
if '\\boxright' in ops_collection.operator_dictionary:
    print("✓ \\boxright found in operators")
else:
    print("✗ \\boxright NOT found in operators")
    print("Available operators:")
    for key in ops_collection.operator_dictionary.keys():
        print(f"  '{key}'")

# Check the first example that uses boxright
cf_cm_1 = module.example_range['CF_CM_1']
print(f"\nCF_CM_1 example:")
print(f"  Premises: {cf_cm_1['premises']}")
print(f"  Conclusions: {cf_cm_1['conclusions']}")