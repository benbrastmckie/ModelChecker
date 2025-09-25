#!/usr/bin/env python3
"""Test script to verify the import fix for generated projects with relative imports."""

import sys
import os
import tempfile
import shutil
from pathlib import Path

# Add the src directory to path to use the modified code
src_dir = Path(__file__).parent / 'Code' / 'src'
sys.path.insert(0, str(src_dir))

# Now import the model_checker components
from model_checker.builder.loader import ModuleLoader
from model_checker.builder.strategies import PackageImportStrategy

def test_package_import():
    """Test the PackageImportStrategy with a file that has relative imports."""

    # Use the actual project_eleven example
    test_file = "/Users/nicky/Documents/project_eleven/subtheories/counterfactual/examples.py"

    if not Path(test_file).exists():
        print(f"Error: Test file {test_file} does not exist")
        return False

    print(f"Testing import of: {test_file}")

    try:
        # Create a loader
        loader = ModuleLoader("examples", test_file)

        # Try to load the module
        module = loader.load_module()

        print("✓ Module loaded successfully!")

        # Check if key attributes exist
        if hasattr(module, 'example_range'):
            print("✓ Found example_range attribute")
        if hasattr(module, 'LogosSemantics'):
            print("✓ Found LogosSemantics class")
        if hasattr(module, 'LogosProposition'):
            print("✓ Found LogosProposition class")

        return True

    except Exception as e:
        print(f"✗ Failed to load module: {e}")
        import traceback
        traceback.print_exc()
        return False

def test_direct_strategy():
    """Test the strategy directly."""
    print("\n--- Testing PackageImportStrategy directly ---")

    test_file = "/Users/nicky/Documents/project_eleven/subtheories/counterfactual/examples.py"

    try:
        strategy = PackageImportStrategy()
        module = strategy.import_module("examples", test_file)
        print("✓ Direct strategy test passed!")
        return True
    except Exception as e:
        print(f"✗ Direct strategy test failed: {e}")
        import traceback
        traceback.print_exc()
        return False

if __name__ == "__main__":
    print("=== Testing Import Fix for Generated Projects ===\n")

    test1 = test_package_import()
    test2 = test_direct_strategy()

    print("\n=== Test Results ===")
    print(f"Package import test: {'PASSED' if test1 else 'FAILED'}")
    print(f"Direct strategy test: {'PASSED' if test2 else 'FAILED'}")

    if test1 and test2:
        print("\n✓ All tests passed! The fix is working.")
        sys.exit(0)
    else:
        print("\n✗ Some tests failed. The fix needs adjustment.")
        sys.exit(1)