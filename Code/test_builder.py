#!/usr/bin/env python3
"""Test runner for the builder module.

This script runs tests for the builder module, following the same approach
as run_tests.py but focused specifically on the builder package.
"""

import os
import sys
import argparse
import subprocess

def run_builder_tests(verbose=False):
    """Run tests for the builder module."""
    # We're now in the Code directory
    code_dir = os.path.dirname(__file__)
    
    # Set the path for the builder tests
    test_dir = os.path.join("src", "model_checker", "builder", "tests")
    
    # Check if builder tests directory exists
    full_test_dir = os.path.join(code_dir, test_dir)
    if not os.path.exists(full_test_dir):
        print(f"Directory not found: {test_dir}")
        return 1
    
    env = os.environ.copy()
    env['PYTHONPATH'] = os.path.join(code_dir, 'src')
    
    print(f"Running tests for builder module")
    print("=" * 80)
    
    try:
        # Construct command for running the builder tests
        run_command = ["pytest", test_dir]
        if verbose:
            run_command.append("-v")
        
        # Run the tests
        result = subprocess.run(run_command, cwd=code_dir, env=env)
        
        if result.returncode != 0:
            print("\nFAILED: Builder tests had failures")
            return 1
        else:
            print("\nSUCCESS: All builder tests passed!")
            return 0
        
    except Exception as e:
        print(f"Error running builder tests: {str(e)}")
        return 1

def main():
    """Main entry point for the script."""
    parser = argparse.ArgumentParser(description="Run tests for the builder module")
    parser.add_argument(
        "--verbose", "-v", 
        action="store_true", 
        help="Enable verbose output"
    )
    
    args = parser.parse_args()
    exit_code = run_builder_tests(args.verbose)
    sys.exit(exit_code)

if __name__ == "__main__":
    main()