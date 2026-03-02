#!/usr/bin/env python3
"""
Debug script to test specific parts of the demo notebook.
"""

import os
import sys
import traceback

def setup_environment():
    """Set up the environment for testing."""
    print("Setting up environment...")
    current_dir = os.getcwd()
    print(f"Current directory: {current_dir}")
    
    # Add src to path
    src_dir = os.path.join(current_dir, 'src')
    if src_dir not in sys.path:
        sys.path.insert(0, src_dir)
        print(f"Added to path: {src_dir}")

def test_basic_imports():
    """Test basic imports from the ModelChecker package."""
    print("\nTesting basic imports...")
    try:
        import model_checker
        print(f"✓ Successfully imported model_checker from {model_checker.__file__}")
        print(f"  Version: {model_checker.__version__}")
        
        from model_checker.jupyter import check_formula, find_countermodel, ModelExplorer
        print("✓ Successfully imported check_formula, find_countermodel, ModelExplorer")
        
        return True
    except Exception as e:
        print(f"✗ Error importing: {str(e)}")
        traceback.print_exc()
        return False

def test_formula_checking():
    """Test formula checking functionality."""
    print("\nTesting formula checking...")
    try:
        from model_checker.jupyter import check_formula
        
        # Basic formula
        result = check_formula("p → (q → p)")
        print("✓ Successfully ran check_formula")
        
        # With premises
        result = check_formula("q", premises=["p", "p → q"])
        print("✓ Successfully ran check_formula with premises")
        
        return True
    except Exception as e:
        print(f"✗ Error checking formula: {str(e)}")
        traceback.print_exc()
        return False

def test_environment_setup():
    """Test environment setup code from the notebook."""
    print("\nTesting environment setup from notebook...")
    try:
        from model_checker.jupyter.environment import setup_environment, get_diagnostic_info
        
        # Get environment info
        env_info = setup_environment()
        print(f"Environment setup result: {env_info.get('status', 'unknown')}")
        
        # Get diagnostic info
        diag_info = get_diagnostic_info()
        print(f"ModelChecker path: {diag_info.get('model_checker', {}).get('path', 'unknown')}")
        
        return True
    except Exception as e:
        print(f"✗ Error in environment setup: {str(e)}")
        traceback.print_exc()
        return False

def test_unicode():
    """Test Unicode operator handling."""
    print("\nTesting Unicode operator handling...")
    try:
        from model_checker.jupyter.unicode import unicode_to_latex, latex_to_unicode
        
        # Test conversion
        unicode_formula = "p → (q ∧ ¬r) ∨ □s"
        latex_formula = unicode_to_latex(unicode_formula)
        back_to_unicode = latex_to_unicode(latex_formula)
        
        print(f"Unicode: {unicode_formula}")
        print(f"LaTeX:   {latex_formula}")
        print(f"Back to Unicode: {back_to_unicode}")
        
        return True
    except Exception as e:
        print(f"✗ Error handling Unicode operators: {str(e)}")
        traceback.print_exc()
        return False

def test_theory_examples():
    """Test loading examples from theories."""
    print("\nTesting theory examples loading...")
    try:
        from model_checker.jupyter.utils import load_examples
        
        # Try loading default theory examples
        examples = load_examples("default")
        if examples:
            print(f"✓ Successfully loaded {len(examples)} examples from default theory")
            # Print first example name
            if examples:
                first_example = list(examples.keys())[0]
                print(f"  First example: {first_example}")
        else:
            print("No examples found in default theory")
        
        return True
    except Exception as e:
        print(f"✗ Error loading theory examples: {str(e)}")
        traceback.print_exc()
        return False

def main():
    """Main entry point."""
    setup_environment()
    
    # Run tests
    tests = [
        test_basic_imports,
        test_environment_setup,
        test_formula_checking,
        test_unicode,
        test_theory_examples
    ]
    
    results = []
    for test in tests:
        results.append(test())
    
    # Summary
    print("\nTest Summary:")
    print(f"Total tests: {len(tests)}")
    print(f"Passed: {sum(results)}")
    print(f"Failed: {len(results) - sum(results)}")
    
    if all(results):
        print("\n✓ All tests passed!")
    else:
        print("\n✗ Some tests failed!")
        
    # Return exit code
    return 0 if all(results) else 1

if __name__ == "__main__":
    sys.exit(main())
