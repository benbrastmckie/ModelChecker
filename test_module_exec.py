#!/usr/bin/env python3
"""Test what happens when the module is loaded."""

import sys
sys.path.insert(0, '/Users/nicky/Documents/ModelChecker/Code/src')

from model_checker.builder.loader import ModuleLoader
loader = ModuleLoader("examples", "/Users/nicky/Documents/project_eleven/subtheories/counterfactual/examples.py")
module = loader.load_module()

print(f"Module loaded: {module.__name__}")

# Check what's in the semantic_theories
if hasattr(module, 'semantic_theories'):
    for name, theory in module.semantic_theories.items():
        print(f"\nTheory: {name}")
        ops = theory.get('operators')
        if ops:
            print(f"  Operators type: {type(ops)}")
            if hasattr(ops, 'operator_dictionary'):
                print(f"  Operator count: {len(ops.operator_dictionary)}")
                print(f"  Has \\boxright: {'\\boxright' in ops.operator_dictionary}")
                if '\\boxright' not in ops.operator_dictionary:
                    print(f"  Available: {list(ops.operator_dictionary.keys())}")

# Check if the registry is available
if hasattr(module, 'counterfactual_registry'):
    print(f"\nFound counterfactual_registry")
    reg = module.counterfactual_registry
    print(f"  Type: {type(reg)}")
    print(f"  Loaded subtheories: {list(reg.loaded_subtheories.keys())}")