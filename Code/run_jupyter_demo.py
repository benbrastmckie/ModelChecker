#!/usr/bin/env python3
"""
Simple script to test the model-checker with jupyter integration.
Run this from the nix-shell.
"""

import os
import sys

# Add the necessary paths
current_dir = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, current_dir)
sys.path.insert(0, os.path.join(current_dir, 'src'))

# Import the package
try:
    import model_checker
    print(f"Successfully imported model_checker from {model_checker.__file__}")
    print(f"Version: {model_checker.__version__}")
except ImportError as e:
    print(f"Failed to import model_checker: {e}")
    sys.exit(1)

# Try to import jupyter-related modules
try:
    from model_checker.jupyter import check_formula
    print("Successfully imported check_formula from model_checker.jupyter")
except ImportError as e:
    print(f"Failed to import from model_checker.jupyter: {e}")
    sys.exit(1)

# Test a simple formula
print("\nTesting a simple formula:")
result = check_formula("p → (q → p)")
print("Formula check successful!")

print("\nIf you want to run the interactive notebook version, try:")
print("jupyter notebook --no-browser src/model_checker/theory_lib/jupyter/jupyter_demo.ipynb")