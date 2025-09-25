#!/usr/bin/env python3
"""Test the loader directly to see which strategy it selects."""

import sys
from pathlib import Path

# Ensure we're using the development version
sys.path.insert(0, '/Users/nicky/Documents/ModelChecker/Code/src')

from model_checker.builder.loader import ModuleLoader

test_file = "/Users/nicky/Documents/project_eleven/subtheories/counterfactual/examples.py"

print("Creating loader...")
loader = ModuleLoader("examples", test_file)

print(f"Module path: {test_file}")
print(f"_is_theory_lib_file(): {loader._is_theory_lib_file()}")
print(f"_is_package(): {loader._is_package()}")

print("\nAttempting to load module...")
try:
    module = loader.load_module()
    print("✓ Success! Module loaded")
except Exception as e:
    print(f"✗ Failed: {e}")
    import traceback
    traceback.print_exc()