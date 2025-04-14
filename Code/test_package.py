#!/usr/bin/env python3
"""Test runner for ModelChecker package components.

This script runs tests for all non-theory components (builder, settings, utils, etc.), 
providing a unified interface for running component tests across the ModelChecker package.
"""

import os
import sys
import glob
import argparse
import subprocess
from typing import List, Optional, Dict

def discover_components() -> Dict[str, str]:
    """Dynamically discover testable components by looking for test directories.
    
    Returns:
        Dict[str, str]: Dictionary mapping component names to test directories
    """
    # We're in the Code directory
    code_dir = os.path.dirname(__file__)
    src_dir = os.path.join(code_dir, 'src', 'model_checker')
    
    # Find all test directories (excluding theory_lib tests)
    components = {}
    
    # Check top-level utils tests
    top_level_tests = os.path.join(src_dir, 'tests')
    if os.path.exists(top_level_tests) and os.path.isdir(top_level_tests):
        components['core'] = os.path.join("src", "model_checker", "tests")
    
    # Check subdirectory tests
    for item in os.listdir(src_dir):
        # Skip theory_lib as it's handled by theory_tests.py
        if item == 'theory_lib':
            continue
            
        item_path = os.path.join(src_dir, item)
        if os.path.isdir(item_path):
            # Check if there's a tests subdirectory
            test_dir = os.path.join(item_path, 'tests')
            if os.path.exists(test_dir) and os.path.isdir(test_dir):
                components[item] = os.path.join("src", "model_checker", item, "tests")
    
    return components

def list_available_components() -> None:
    """Print the list of available testable components."""
    components = discover_components()
    
    if not components:
        print("No testable components found!")
        return
    
    print("Available components:")
    for name, path in components.items():
        print(f"  - {name} ({path})")
    print()
    print("Run tests with: python test_package.py [--components component1 component2 ...]")

def run_package_tests(
    components: Optional[List[str]] = None, 
    verbose: bool = False,
    failfast: bool = False,
    list_only: bool = False
) -> int:
    """Run tests for specified package components.
    
    Args:
        components: List of components to test. If None, tests all available components.
        verbose: Whether to run tests in verbose mode
        failfast: Whether to stop after the first failure
        list_only: Only list available components, don't run tests
        
    Returns:
        int: Exit code (0 for success, 1 for failures)
    """
    # List components if requested
    if list_only:
        list_available_components()
        return 0
    
    # We're now in the Code directory
    code_dir = os.path.dirname(__file__)
    env = os.environ.copy()
    env['PYTHONPATH'] = os.path.join(code_dir, 'src')
    
    # Get the list of available components
    available_components = discover_components()
    
    if not available_components:
        print("No testable components found!")
        return 1
        
    # If no components specified, test all available components
    if not components:
        components = list(available_components.keys())
    
    # Validate requested components exist
    for component in components:
        if component not in available_components:
            print(f"Unknown component: {component}")
            print(f"Available components: {', '.join(available_components.keys())}")
            return 1
    
    # Print header
    print(f"Running tests for components: {', '.join(components)}")
    print("=" * 80)
    
    # Track failed components
    failed_components = []
    
    # Run tests for each component
    for component in components:
        test_dir = available_components[component]
        full_test_dir = os.path.join(code_dir, test_dir)
        
        print(f"\nTesting component: {component}")
        print("-" * 50)
        
        try:
            # Construct command for running the tests
            run_command = ["pytest", test_dir]
            if verbose:
                run_command.append("-v")
            if failfast:
                run_command.append("-xvs")
            
            # Run the tests
            result = subprocess.run(run_command, cwd=code_dir, env=env)
            
            if result.returncode != 0:
                failed_components.append(component)
                if failfast:
                    # Stop on first failure if requested
                    break
            
        except Exception as e:
            print(f"Error running {component} tests: {str(e)}")
            failed_components.append(component)
            if failfast:
                break
    
    # Print summary
    print("\n" + "=" * 80)
    print("Test Summary:")
    for component in components:
        if failfast and component not in failed_components and len(failed_components) > 0:
            # If we're in failfast mode and stopped after a failure,
            # mark untested components as SKIPPED
            status = "SKIPPED" if component not in components[:components.index(failed_components[0])+1] else \
                    "FAILED" if component in failed_components else "PASSED"
        else:
            status = "FAILED" if component in failed_components else "PASSED"
        print(f"  {component}: {status}")
    
    # Print overall success/failure message
    if failed_components:
        print(f"\nFAILED: {len(failed_components)} components had test failures")
    else:
        print("\nSUCCESS: All tests passed!")
    
    return 1 if failed_components else 0

def main():
    """Main entry point for the script."""
    parser = argparse.ArgumentParser(description="Run tests for ModelChecker package components")
    parser.add_argument(
        "--components", 
        nargs="+", 
        help="Components to test. Default: all available components."
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
    parser.add_argument(
        "--list", "-l", 
        action="store_true",
        help="List available components"
    )
    
    args = parser.parse_args()
    exit_code = run_package_tests(args.components, args.verbose, args.failfast, args.list)
    sys.exit(exit_code)

if __name__ == "__main__":
    main()