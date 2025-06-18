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


def add_logos_args(parser):
    """Add logos-specific argument parsing with inclusive-by-default approach."""
    logos_group = parser.add_argument_group('logos testing options')
    
    # Test type restrictions (default: run both examples and unit tests)
    logos_group.add_argument('--examples', nargs='*', 
                           help='RESTRICT to example tests only. Optionally specify example names')
    logos_group.add_argument('--package', action='store_true', 
                           help='RESTRICT to unit/implementation tests only')
    
    # Subtheory restrictions (default: all subtheories)
    logos_group.add_argument('--extensional', action='store_true',
                           help='RESTRICT to extensional subtheory only')
    logos_group.add_argument('--modal', action='store_true',
                           help='RESTRICT to modal subtheory only') 
    logos_group.add_argument('--constitutive', action='store_true',
                           help='RESTRICT to constitutive subtheory only')
    logos_group.add_argument('--counterfactual', action='store_true',
                           help='RESTRICT to counterfactual subtheory only')
    logos_group.add_argument('--relevance', action='store_true',
                           help='RESTRICT to relevance subtheory only')
    
    # Unit test category restrictions (default: all unit test categories)
    logos_group.add_argument('--semantics', action='store_true',
                           help='RESTRICT to semantic method tests only')
    logos_group.add_argument('--operators', action='store_true',
                           help='RESTRICT to operator implementation tests only')
    logos_group.add_argument('--registry', action='store_true',
                           help='RESTRICT to registry functionality tests only')
    logos_group.add_argument('--proposition', action='store_true',
                           help='RESTRICT to proposition tests only')
    logos_group.add_argument('--model-structure', action='store_true',
                           help='RESTRICT to model structure tests only')
    logos_group.add_argument('--error-conditions', action='store_true',
                           help='RESTRICT to error condition tests only')


def validate_example_names(example_names, theory='logos'):
    """Validate that specified example names exist."""
    # Import the examples to validate names
    code_dir = os.path.dirname(__file__)
    env = os.environ.copy()
    env['PYTHONPATH'] = os.path.join(code_dir, 'src')
    
    validation_script = f"""
import sys
try:
    from model_checker.theory_lib.{theory}.examples import unit_tests
    available_examples = list(unit_tests.keys())
    invalid_names = []
    for name in {example_names}:
        if '*' not in name and name not in available_examples:
            invalid_names.append(name)
    
    if invalid_names:
        print(f"ERROR: Unknown example names: {{', '.join(invalid_names)}}")
        print(f"Available examples: {{', '.join(sorted(available_examples))}}")
        
        # Suggest similar names
        for invalid in invalid_names:
            similar = [ex for ex in available_examples if invalid.lower() in ex.lower()]
            if similar:
                print(f"Did you mean: {{', '.join(similar[:3])}}")
        sys.exit(1)
    else:
        print("VALID")
except Exception as e:
    print(f"ERROR: Cannot validate examples: {{e}}")
    sys.exit(1)
"""
    
    result = subprocess.run(
        [sys.executable, '-c', validation_script],
        capture_output=True,
        text=True,
        env=env,
        cwd=code_dir
    )
    
    if result.returncode != 0:
        print(result.stdout)
        return False
    return True


def build_logos_test_command(args, code_dir):
    """Build pytest command for logos testing with inclusive-by-default approach."""
    base_dir = "src/model_checker/theory_lib/logos/tests"
    command = ["pytest"]
    
    # Start with all tests, then apply restrictions
    test_directories = []
    test_filters = []
    
    # Determine test type restrictions
    run_examples = True
    run_unit_tests = True
    
    if args.examples is not None:
        # Restrict to examples only
        run_unit_tests = False
        test_directories.append(f"{base_dir}/test_examples")
    elif args.package:
        # Restrict to unit tests only
        run_examples = False
        test_directories.append(f"{base_dir}/test_unit")
    else:
        # Default: run both examples and unit tests
        test_directories.append(base_dir)
    
    # Handle specific example names (most restrictive)
    if args.examples and len(args.examples) > 0:
        # Validate example names first
        if not validate_example_names(args.examples):
            return None
            
        example_names = args.examples
        if len(example_names) == 1 and '*' in example_names[0]:
            # Wildcard pattern
            pattern = example_names[0].replace('*', '')
            test_filters.append(f"test_logos_examples and {pattern}")
        else:
            # Exact matches - create OR expression
            test_expr = " or ".join(f"{name}" for name in example_names)
            test_filters.append(f"({test_expr})")
    
    # Apply subtheory restrictions
    subtheory_filters = []
    if args.extensional:
        subtheory_filters.append("(extensional or EXT_)")
    if args.modal:
        subtheory_filters.append("(modal or MOD_)")
    if args.constitutive:
        subtheory_filters.append("(constitutive or CON_ or CL_)")
    if args.counterfactual:
        subtheory_filters.append("(counterfactual or CF_)")
    if args.relevance:
        subtheory_filters.append("(relevance or REL_)")
    
    # If any subtheory specified, restrict to those
    if subtheory_filters:
        test_filters.append(f"({' or '.join(subtheory_filters)})")
    
    # Apply unit test category restrictions (only if running unit tests)
    if run_unit_tests and args.package:
        unit_filters = []
        if args.semantics:
            unit_filters.append("semantic")
        if args.operators:
            unit_filters.append("operator")
        if args.registry:
            unit_filters.append("registry")
        if args.proposition:
            unit_filters.append("proposition")
        if getattr(args, 'model_structure', False):
            unit_filters.append("model_structure")
        if getattr(args, 'error_conditions', False):
            unit_filters.append("error_condition")
        
        # If any unit test categories specified, restrict to those
        if unit_filters:
            test_filters.append(f"({' or '.join(unit_filters)})")
    
    # Add directories to command
    command.extend(test_directories)
    
    # Combine all filters with AND logic
    if test_filters:
        combined_filter = " and ".join(test_filters)
        command.extend(["-k", combined_filter])
    
    return command

def run_tests(theories: Optional[List[str]] = None, verbose: bool = False, failfast: bool = False, **kwargs):
    """Run tests for the specified theories.
    
    Args:
        theories: List of theory names to test. If None, tests all registered theories.
        verbose: Whether to run tests in verbose mode
        failfast: Whether to stop after the first failure
        **kwargs: Additional arguments for theory-specific testing (e.g., logos arguments)
        
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
            # Check if this is logos theory and we have special arguments
            if theory == 'logos' and any(key.startswith('logos_') for key in kwargs.keys()):
                # Create an args object for logos-specific testing
                class LogosArgs:
                    def __init__(self, **kwargs):
                        # Set all possible arguments to their defaults
                        self.examples = kwargs.get('logos_examples')
                        self.package = kwargs.get('logos_package', False)
                        self.extensional = kwargs.get('logos_extensional', False)
                        self.modal = kwargs.get('logos_modal', False)
                        self.constitutive = kwargs.get('logos_constitutive', False)
                        self.counterfactual = kwargs.get('logos_counterfactual', False)
                        self.relevance = kwargs.get('logos_relevance', False)
                        self.semantics = kwargs.get('logos_semantics', False)
                        self.operators = kwargs.get('logos_operators', False)
                        self.registry = kwargs.get('logos_registry', False)
                        self.proposition = kwargs.get('logos_proposition', False)
                        setattr(self, 'model_structure', kwargs.get('logos_model_structure', False))
                        setattr(self, 'error_conditions', kwargs.get('logos_error_conditions', False))
                
                args = LogosArgs(**kwargs)
                run_command = build_logos_test_command(args, code_dir)
                
                if run_command is None:
                    print(f"Error: Invalid arguments for logos theory testing")
                    failed_theories.append(theory)
                    continue
            else:
                # Standard pytest command
                run_command = ["pytest", test_dir]
            
            # Add standard flags
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
    
    # Add logos-specific arguments only if logos is in the requested theories
    # This provides a cleaner interface when not using logos
    requested_theories = sys.argv
    if '--theories' in requested_theories:
        theory_idx = requested_theories.index('--theories') + 1
        if theory_idx < len(requested_theories) and 'logos' in requested_theories[theory_idx:]:
            add_logos_args(parser)
    elif 'logos' in get_registered_theories():
        # If no specific theories requested, add logos args in case logos is tested
        add_logos_args(parser)
    
    args = parser.parse_args()
    
    # Convert logos-specific arguments to kwargs format
    kwargs = {}
    if hasattr(args, 'examples'):
        kwargs['logos_examples'] = args.examples
    if hasattr(args, 'package'):
        kwargs['logos_package'] = args.package
    if hasattr(args, 'extensional'):
        kwargs['logos_extensional'] = args.extensional
    if hasattr(args, 'modal'):
        kwargs['logos_modal'] = args.modal
    if hasattr(args, 'constitutive'):
        kwargs['logos_constitutive'] = args.constitutive
    if hasattr(args, 'counterfactual'):
        kwargs['logos_counterfactual'] = args.counterfactual
    if hasattr(args, 'relevance'):
        kwargs['logos_relevance'] = args.relevance
    if hasattr(args, 'semantics'):
        kwargs['logos_semantics'] = args.semantics
    if hasattr(args, 'operators'):
        kwargs['logos_operators'] = args.operators
    if hasattr(args, 'registry'):
        kwargs['logos_registry'] = args.registry
    if hasattr(args, 'proposition'):
        kwargs['logos_proposition'] = args.proposition
    if hasattr(args, 'model_structure'):
        kwargs['logos_model_structure'] = getattr(args, 'model_structure')
    if hasattr(args, 'error_conditions'):
        kwargs['logos_error_conditions'] = getattr(args, 'error_conditions')
    
    exit_code = run_tests(args.theories, args.verbose, args.failfast, **kwargs)
    sys.exit(exit_code)

if __name__ == "__main__":
    main()