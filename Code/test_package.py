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
import importlib.util
from typing import List, Optional, Dict

def discover_components() -> Dict[str, str]:
    """Dynamically discover testable components by looking for test directories.
    
    Returns:
        Dict[str, str]: Dictionary mapping component names to test directories
    """
    # We're in the Code directory
    code_dir = os.path.dirname(__file__)
    src_dir = os.path.join(code_dir, 'src', 'model_checker')
    
    # Find all test directories
    components = {}
    
    # Check top-level utils tests
    top_level_tests = os.path.join(src_dir, 'tests')
    if os.path.exists(top_level_tests) and os.path.isdir(top_level_tests):
        components['core'] = os.path.join("src", "model_checker", "tests")
    
    # Check subdirectory tests
    for item in os.listdir(src_dir):
        item_path = os.path.join(src_dir, item)
        if os.path.isdir(item_path):
            # Check if there's a tests subdirectory
            test_dir = os.path.join(item_path, 'tests')
            if os.path.exists(test_dir) and os.path.isdir(test_dir):
                # Skip theory-specific tests in theory_lib (these are handled by test_theories.py)
                if item == 'theory_lib':
                    # Add only theory_lib common tests (not individual theory tests)
                    theory_test_files = glob.glob(os.path.join(test_dir, "test_*.py"))
                    if theory_test_files:
                        components['theory_lib'] = os.path.join("src", "model_checker", "theory_lib", "tests")
                else:
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

def setup_environment():
    """Set up the environment for running tests and metadata operations.
    
    This ensures PYTHONPATH includes the src directory for proper imports.
    
    Returns:
        dict: Environment with PYTHONPATH properly set
    """
    code_dir = os.path.dirname(__file__)
    src_path = os.path.join(code_dir, 'src')
    
    # Add src directory to Python path for importing modules
    if src_path not in sys.path:
        sys.path.insert(0, src_path)
    
    # Create environment with PYTHONPATH set for subprocess calls
    env = os.environ.copy()
    env['PYTHONPATH'] = src_path
    
    return env

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
    
    # Set up environment and get code directory
    env = setup_environment()
    code_dir = os.path.dirname(__file__)
    
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

def run_metadata_operations(args):
    """Run metadata management operations.
    
    Args:
        args: Command-line arguments
    
    Returns:
        int: Exit code (0 for success, 1 for failure)
    """
    try:
        # Set up environment
        setup_environment()
        
        # Import metadata functions directly
        from model_checker.theory_lib.meta_data import (
            update_all_theory_versions,
            create_all_license_files,
            create_all_citation_files,
            verify_metadata_consistency,
            print_metadata_report
        )
        
        # Process commands
        if args.update_versions:
            print(f"Updating all theory versions to {args.update_versions}...")
            results = update_all_theory_versions(args.update_versions)
            print("Update results:")
            for theory, version in results.items():
                print(f"  {theory}: {version}")
            print()
        
        if args.create_licenses:
            print(f"Creating {args.license_type} license files...")
            author_info = {"name": args.author} if args.author else None
            results = create_all_license_files(args.license_type, author_info)
            print("License creation results:")
            for theory, success in results.items():
                status = "Success" if success else "Failed"
                print(f"  {theory}: {status}")
            print()
        
        if args.create_citations:
            print("Creating citation files...")
            author_info = {"name": args.author} if args.author else None
            results = create_all_citation_files(author_info)
            print("Citation creation results:")
            for theory, success in results.items():
                status = "Success" if success else "Failed"
                print(f"  {theory}: {status}")
            print()
        
        # Always print the report if specified, or if no other actions were taken
        if args.metadata_report or not (args.update_versions or args.create_licenses or args.create_citations):
            print_metadata_report()
        
        return 0
    except Exception as e:
        print(f"Error running metadata operations: {e}")
        return 1

def main():
    """Main entry point for the script."""
    parser = argparse.ArgumentParser(description="Run tests for ModelChecker package components")
    
    # Testing-related arguments
    test_group = parser.add_argument_group("Test Options")
    test_group.add_argument(
        "--components", 
        nargs="+", 
        help="Components to test. Default: all available components."
    )
    test_group.add_argument(
        "--verbose", "-v", 
        action="store_true", 
        help="Enable verbose output"
    )
    test_group.add_argument(
        "--failfast", "-x", 
        action="store_true", 
        help="Stop after first failure"
    )
    test_group.add_argument(
        "--list", "-l", 
        action="store_true",
        help="List available components"
    )
    
    # Metadata-related arguments
    metadata_group = parser.add_argument_group("Metadata Management")
    metadata_group.add_argument(
        "--metadata-report", 
        action="store_true", 
        help="Print metadata consistency report"
    )
    metadata_group.add_argument(
        "--update-versions", 
        metavar="VERSION", 
        help="Update all theory versions to specified value"
    )
    metadata_group.add_argument(
        "--create-licenses", 
        action="store_true", 
        help="Create license files for all theories"
    )
    metadata_group.add_argument(
        "--create-citations", 
        action="store_true", 
        help="Create citation files for all theories"
    )
    metadata_group.add_argument(
        "--author", 
        metavar="NAME", 
        help="Author name for license and citation files"
    )
    metadata_group.add_argument(
        "--license-type", 
        metavar="TYPE", 
        default="GPL-3.0", 
        help="License type (default: GPL-3.0)"
    )
    
    args = parser.parse_args()
    
    # Determine if we're running metadata operations
    running_metadata = any([
        args.metadata_report,
        args.update_versions is not None,
        args.create_licenses,
        args.create_citations
    ])
    
    if running_metadata:
        # Run metadata operations
        exit_code = run_metadata_operations(args)
    else:
        # Run tests
        exit_code = run_package_tests(args.components, args.verbose, args.failfast, args.list)
    
    sys.exit(exit_code)

if __name__ == "__main__":
    main()