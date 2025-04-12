#!/usr/bin/env python3
"""Test runner for ModelChecker package components.

This script runs tests for all non-theory components (builder, settings, etc.), 
following the same approach as run_tests.py but focusing on core package components.
"""

import os
import sys
import argparse
import subprocess

def run_package_tests(components=None, verbose=False):
    """Run tests for specified package components.
    
    Args:
        components: List of components to test (e.g., ['builder', 'settings']).
                   If None, tests all available components.
        verbose: Whether to run tests in verbose mode
    
    Returns:
        int: Exit code (0 for success, 1 for failures)
    """
    # We're now in the Code directory
    code_dir = os.path.dirname(__file__)
    env = os.environ.copy()
    env['PYTHONPATH'] = os.path.join(code_dir, 'src')
    
    # Define available components and their test directories
    available_components = {
        'builder': os.path.join("src", "model_checker", "builder", "tests"),
        'settings': os.path.join("src", "model_checker", "settings", "tests")
    }
    
    # If no components specified, test all available components
    if not components:
        components = list(available_components.keys())
    
    # Validate requested components exist
    for component in components:
        if component not in available_components:
            print(f"Unknown component: {component}")
            print(f"Available components: {', '.join(available_components.keys())}")
            return 1
    
    # Track overall success
    overall_success = True
    
    # Run tests for each component
    for component in components:
        test_dir = available_components[component]
        full_test_dir = os.path.join(code_dir, test_dir)
        
        # Check if test directory exists
        if not os.path.exists(full_test_dir):
            print(f"Directory not found: {test_dir}")
            overall_success = False
            continue
        
        print(f"\nRunning tests for {component} module")
        print("=" * 80)
        
        try:
            # Construct command for running the tests
            run_command = ["pytest", test_dir]
            if verbose:
                run_command.append("-v")
            
            # Run the tests
            result = subprocess.run(run_command, cwd=code_dir, env=env)
            
            if result.returncode != 0:
                print(f"\nFAILED: {component.capitalize()} tests had failures")
                overall_success = False
            else:
                print(f"\nSUCCESS: All {component} tests passed!")
            
        except Exception as e:
            print(f"Error running {component} tests: {str(e)}")
            overall_success = False
    
    return 0 if overall_success else 1

def main():
    """Main entry point for the script."""
    parser = argparse.ArgumentParser(description="Run tests for ModelChecker package components")
    parser.add_argument(
        "--components", 
        nargs="+", 
        help="Components to test (e.g., builder settings). Default: all components."
    )
    parser.add_argument(
        "--verbose", "-v", 
        action="store_true", 
        help="Enable verbose output"
    )
    
    args = parser.parse_args()
    exit_code = run_package_tests(args.components, args.verbose)
    sys.exit(exit_code)

if __name__ == "__main__":
    main()