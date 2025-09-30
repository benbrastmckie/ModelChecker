#!/usr/bin/env python3
"""
Test script to validate type hints in theory_lib modules.

This script tests the type hint functionality without requiring
the full model_checker framework to load.
"""

import sys
import os

# Add the source path
sys.path.insert(0, 'Code/src')

def test_type_hints():
    """Test that type hints are working correctly."""
    print("=== Testing Type Hints ===")

    # Test error system first (should work)
    try:
        from model_checker.theory_lib.errors import TheoryError, ErrorSeverity
        print("✓ Error system imports successfully")

        # Test error creation
        error = TheoryError("Test", theory="test", suggestion="Try this")
        print(f"✓ Error creation works: {error}")

    except Exception as e:
        print(f"✗ Error system failed: {e}")
        return False

    # Test type system
    try:
        # Direct import to avoid framework loading issues
        import importlib.util
        spec = importlib.util.spec_from_file_location(
            "types",
            "Code/src/model_checker/theory_lib/types.py"
        )
        types_module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(types_module)

        print("✓ Type system loads successfully")
        print(f"✓ Semantics protocol: {types_module.Semantics}")
        print(f"✓ Proposition protocol: {types_module.Proposition}")

    except Exception as e:
        print(f"✗ Type system failed: {e}")
        return False

    # Test individual function signatures (without full import)
    try:
        with open('Code/src/model_checker/theory_lib/__init__.py', 'r') as f:
            content = f.read()

        # Check for type hints in function signatures
        type_hint_functions = [
            'get_examples(theory_name: str) -> Dict[str, Any]',
            'get_test_examples(theory_name: str) -> Dict[str, Any]',
            'discover_theories() -> List[str]',
            'get_theory_version_registry() -> Dict[str, str]',
        ]

        for func_sig in type_hint_functions:
            if func_sig in content:
                print(f"✓ Found type hint: {func_sig}")
            else:
                print(f"✗ Missing type hint: {func_sig}")
                return False

    except Exception as e:
        print(f"✗ Type hint validation failed: {e}")
        return False

    print("\n=== Type Hint Testing Complete ===")
    return True

if __name__ == '__main__':
    success = test_type_hints()
    sys.exit(0 if success else 1)