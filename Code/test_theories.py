#!/usr/bin/env python3
"""Test runner for ModelChecker theories.

This script runs tests for theories registered in the theory_lib.
It provides a standardized way to test all registered theories or specific ones.
"""

import os
import sys
import argparse
import subprocess
from typing import List, Optional

def get_registered_theories():
    """Get the list of registered theories from theory_lib.
    
    Returns:
        List[str]: List of registered theory names
    """
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

def run_tests(theories: Optional[List[str]] = None, verbose: bool = False, failfast: bool = False):
    """Run tests for the specified theories.
    
    Args:
        theories: List of theory names to test. If None, tests all registered theories.
        verbose: Whether to run tests in verbose mode
        failfast: Whether to stop after the first failure
        
    Returns:
        int: Exit code (0 for success, 1 for failures)
    """
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
        
        # Check specifically for the tests or test subdirectory
        tests_subdir = os.path.join(full_test_dir, "tests")
        test_subdir = os.path.join(full_test_dir, "test")
        
        if os.path.exists(tests_subdir):
            # If there's a tests subdirectory, target that specifically
            test_dir = os.path.join(test_dir, "tests")
        elif os.path.exists(test_subdir):
            # For backward compatibility, also check for the test subdirectory
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
            if failfast:
                run_command.append("-xvs")
            
            # Run the tests
            result = subprocess.run(run_command, cwd=code_dir, env=env)
            
            if result.returncode != 0:
                failed_theories.append(theory)
                if failfast:
                    # Stop on first failure
                    break
            
        except Exception as e:
            print(f"Error running tests for {theory}: {str(e)}")
            failed_theories.append(theory)
            if failfast:
                break
    
    # Print summary
    print("\n" + "=" * 80)
    print("Test Summary:")
    for theory in theories:
        if failfast and theory not in failed_theories and len(failed_theories) > 0:
            # If we're in failfast mode and stopped after a failure,
            # mark untested theories as SKIPPED
            status = "SKIPPED" if theory not in theories[:theories.index(failed_theories[0])+1] else \
                    "FAILED" if theory in failed_theories else "PASSED"
        else:
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
    parser.add_argument(
        "--failfast", "-x", 
        action="store_true", 
        help="Stop after first failure"
    )
    
    args = parser.parse_args()
    exit_code = run_tests(args.theories, args.verbose, args.failfast)
    sys.exit(exit_code)

if __name__ == "__main__":
    main()