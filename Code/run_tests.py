#!/usr/bin/env python3
"""Test runner for ModelChecker theories.

This script runs tests for theories registered in the theory_lib. 
It follows the same approach as update.sh but in a more Pythonic way.
"""

import os
import sys
import argparse
import subprocess

def get_registered_theories():
    """Get the list of registered theories from theory_lib."""
    # We're now in the Code directory, so we can just use src directly
    env = os.environ.copy()
    env['PYTHONPATH'] = os.path.join(os.path.dirname(__file__), 'src')
    
    # Get the list of theories from AVAILABLE_THEORIES
    result = subprocess.run(
        [sys.executable, '-c', 'from model_checker.theory_lib import AVAILABLE_THEORIES; print(" ".join(AVAILABLE_THEORIES))'],
        capture_output=True,
        text=True,
        env=env,
        cwd=os.path.dirname(__file__)
    )
    
    if result.returncode != 0:
        print(f"Error getting registered theories: {result.stderr}")
        return []
    
    theories = result.stdout.strip().split()
    return theories

def run_tests(theories=None, verbose=False):
    """Run tests for the specified theories."""
    # We're now in the Code directory
    code_dir = os.path.dirname(__file__)
    
    # If no theories specified, get all registered ones
    if not theories:
        theories = get_registered_theories()
        if not theories:
            print("No theories found or error getting registered theories")
            return 1
    
    # Print header
    print(f"Running tests for theories: {', '.join(theories)}")
    print("=" * 80)
    
    failed_theories = []
    
    for theory in theories:
        test_dir = os.path.join("src", "model_checker", "theory_lib", theory)
        
        # Check if test directory exists
        full_test_dir = os.path.join(code_dir, test_dir)
        if not os.path.exists(full_test_dir):
            print(f"Directory not found for theory: {theory}")
            continue
        
        # Check specifically for the test subdirectory
        test_subdir = os.path.join(full_test_dir, "test")
        if os.path.exists(test_subdir):
            # If there's a test subdirectory, target that specifically
            test_dir = os.path.join(test_dir, "test")
        
        env = os.environ.copy()
        env['PYTHONPATH'] = os.path.join(code_dir, 'src')
        
        print(f"\nTesting theory: {theory}")
        print("-" * 50)
        
        try:
            # Construct command for running the test
            run_command = ["pytest", test_dir]
            if verbose:
                run_command.append("-v")
            
            # Run the tests
            result = subprocess.run(run_command, cwd=code_dir, env=env)
            
            if result.returncode != 0:
                failed_theories.append(theory)
            
        except Exception as e:
            print(f"Error running tests for {theory}: {str(e)}")
            failed_theories.append(theory)
    
    # Print summary
    print("\n" + "=" * 80)
    print("Test Summary:")
    for theory in theories:
        status = "FAILED" if theory in failed_theories else "PASSED"
        print(f"  {theory}: {status}")
    
    # Print overall success/failure message
    if failed_theories:
        print(f"\nFAILED: {len(failed_theories)} theories had test failures")
    else:
        print("\nSUCCESS: All tests passed!")
    
    return 1 if failed_theories else 0

def main():
    """Main entry point for the script."""
    parser = argparse.ArgumentParser(description="Run tests for ModelChecker theories")
    parser.add_argument(
        "--theories", 
        nargs="+", 
        help="Specific theories to test (default: all registered theories)"
    )
    parser.add_argument(
        "--verbose", "-v", 
        action="store_true", 
        help="Enable verbose output"
    )
    
    args = parser.parse_args()
    exit_code = run_tests(args.theories, args.verbose)
    sys.exit(exit_code)

if __name__ == "__main__":
    main()