#!/usr/bin/env python3
"""Unified test runner for ModelChecker theories and package components.

This script provides a comprehensive interface for running tests across:
- Theory examples (integration tests from examples.py files)
- Unit tests (component/implementation tests)
- Package tests (framework infrastructure tests)

Usage examples:
    ./run_tests.py                           # Run all tests
    ./run_tests.py --examples                # Run only example tests
    ./run_tests.py --unit                    # Run only unit tests
    ./run_tests.py --package                 # Run only package tests
    ./run_tests.py logos modal               # Test logos modal subtheory
    ./run_tests.py --examples logos modal    # Example tests for logos modal
"""

import os
import sys
import argparse
import subprocess
from dataclasses import dataclass
from typing import List, Dict, Optional, Union
from pathlib import Path


@dataclass
class TestConfig:
    """Immutable test configuration."""
    theories: List[str]
    subtheories: Dict[str, List[str]]  # theory -> list of subtheories
    components: List[str]
    run_examples: bool
    run_unit: bool
    run_package: bool
    verbose: bool
    failfast: bool
    coverage: bool
    markers: List[str]
    pytest_args: List[str]

    @classmethod
    def from_args(cls, args, runner: 'TestRunner') -> 'TestConfig':
        """Create configuration from command line arguments."""
        # Parse positional arguments for theories/subtheories
        theories, subtheories = runner._parse_positional_args(args.targets or [])
        
        # If no theories specified and not package-only, use all available theories
        if not theories and not (args.package and not args.examples and not args.unit):
            theories = runner.theories
        
        # If no components specified and package testing requested, use all components
        components = args.components or (runner.components if args.package else [])
        
        # Determine what test types to run
        run_examples = args.examples or (not args.unit and not args.package)
        run_unit = args.unit or (not args.examples and not args.package)
        run_package = args.package or (not args.examples and not args.unit)
        
        config = cls(
            theories=theories,
            subtheories=subtheories,
            components=components,
            run_examples=run_examples,
            run_unit=run_unit,
            run_package=run_package,
            verbose=args.verbose,
            failfast=args.failfast,
            coverage=getattr(args, 'coverage', False),
            markers=getattr(args, 'markers', []),
            pytest_args=[]
        )
        
        config.validate(runner)
        return config

    def validate(self, runner: 'TestRunner') -> None:
        """Validate configuration against available theories/components."""
        validator = TestConfigValidator()
        validator.validate_theories(self.theories, runner.theories)
        validator.validate_components(self.components, runner.components)
        
        for theory, subs in self.subtheories.items():
            validator.validate_subtheories(theory, subs, runner.subtheories)


class TestResults:
    """Tracks test execution results."""
    
    def __init__(self):
        self.theory_results: Dict[str, Dict[str, int]] = {}  # theory -> test_type -> exit_code
        self.component_results: Dict[str, int] = {}  # component -> exit_code
        self.overall_success = True
    
    def add_theory_result(self, theory: str, test_type: str, exit_code: int) -> None:
        """Add result for theory test execution."""
        if theory not in self.theory_results:
            self.theory_results[theory] = {}
        self.theory_results[theory][test_type] = exit_code
        if exit_code != 0:
            self.overall_success = False
    
    def add_component_result(self, component: str, exit_code: int) -> None:
        """Add result for component test execution."""
        self.component_results[component] = exit_code
        if exit_code != 0:
            self.overall_success = False
    
    def merge(self, other: 'TestResults') -> None:
        """Merge another TestResults into this one."""
        for theory, results in other.theory_results.items():
            if theory not in self.theory_results:
                self.theory_results[theory] = {}
            self.theory_results[theory].update(results)
        
        self.component_results.update(other.component_results)
        self.overall_success = self.overall_success and other.overall_success
    
    def get_exit_code(self) -> int:
        """Get overall exit code (0 for success, 1 for failures)."""
        return 0 if self.overall_success else 1
    
    def print_summary(self) -> None:
        """Print test execution summary."""
        print("\n" + "=" * 80)
        print("Test Summary:")
        
        # Theory results
        if self.theory_results:
            print("\nTheory Tests:")
            for theory, results in self.theory_results.items():
                for test_type, exit_code in results.items():
                    status = "PASSED" if exit_code == 0 else "FAILED"
                    print(f"  {theory} ({test_type}): {status}")
        
        # Component results
        if self.component_results:
            print("\nPackage Tests:")
            for component, exit_code in self.component_results.items():
                status = "PASSED" if exit_code == 0 else "FAILED"
                print(f"  {component}: {status}")
        
        # Overall status
        overall_status = "SUCCESS: All tests passed!" if self.overall_success else "FAILED: Some tests failed"
        print(f"\n{overall_status}")


class TestConfigValidator:
    """Validates test configuration before execution."""
    
    def validate_theories(self, theories: List[str], available: List[str]) -> None:
        """Validate requested theories exist."""
        invalid = [t for t in theories if t not in available]
        if invalid:
            available_str = ', '.join(sorted(available))
            raise ValueError(f"Unknown theories: {invalid}. Available: {available_str}")
    
    def validate_subtheories(self, theory: str, subtheories: List[str], 
                           available_subtheories: Dict[str, List[str]]) -> None:
        """Validate subtheories belong to theory."""
        if subtheories and theory not in available_subtheories:
            raise ValueError(f"Theory '{theory}' does not support subtheories")
        
        if subtheories:
            valid = available_subtheories[theory]
            invalid = [s for s in subtheories if s not in valid]
            if invalid:
                valid_str = ', '.join(sorted(valid))
                raise ValueError(f"Unknown subtheories for {theory}: {invalid}. Available: {valid_str}")
    
    def validate_components(self, components: List[str], available: List[str]) -> None:
        """Validate requested components exist."""
        invalid = [c for c in components if c not in available]
        if invalid:
            available_str = ', '.join(sorted(available))
            raise ValueError(f"Unknown components: {invalid}. Available: {available_str}")


class TestRunner:
    """Main test runner coordinating all test execution."""
    
    def __init__(self):
        self.code_dir = Path(__file__).parent
        self.theories = self._discover_theories()
        self.components = self._discover_components()
        self.subtheories = self._discover_subtheories()
        self.test_categories = ['examples', 'unit', 'package']
    
    def run(self, config: TestConfig) -> TestResults:
        """Execute tests based on configuration."""
        results = TestResults()
        
        # Print startup information
        self._print_startup_info(config)
        
        # Run requested test types
        if config.run_examples and config.theories:
            print(f"\nRunning example tests for theories: {', '.join(config.theories)}")
            example_results = self._run_example_tests(config)
            results.merge(example_results)
        
        if config.run_unit and config.theories:
            print(f"\nRunning unit tests for theories: {', '.join(config.theories)}")
            unit_results = self._run_unit_tests(config)
            results.merge(unit_results)
        
        if config.run_package and config.components:
            print(f"\nRunning package tests for components: {', '.join(config.components)}")
            package_results = self._run_package_tests(config)
            results.merge(package_results)
        
        return results
    
    def _discover_theories(self) -> List[str]:
        """Discover available theories, excluding 'default' by design."""
        theories = []
        theory_lib_dir = self.code_dir / "src" / "model_checker" / "theory_lib"
        
        if not theory_lib_dir.exists():
            return theories
        
        for item in theory_lib_dir.iterdir():
            if (item.is_dir() and 
                not item.name.startswith('__') and 
                item.name != 'default' and  # Exclude default theory
                (item / "tests").exists() and
                (item / "examples.py").exists()):
                theories.append(item.name)
        
        return sorted(theories)
    
    def _discover_components(self) -> List[str]:
        """Discover available package components with test directories."""
        components = []
        src_dir = self.code_dir / "src" / "model_checker"
        
        if not src_dir.exists():
            return components
        
        for item in src_dir.iterdir():
            if (item.is_dir() and 
                not item.name.startswith('__') and 
                item.name != 'theory_lib' and  # Skip theory_lib (handled separately)
                (item / "tests").exists()):
                components.append(item.name)
        
        # Add theory_lib itself (for infrastructure tests)
        theory_lib_tests = src_dir / "theory_lib" / "tests"
        if theory_lib_tests.exists():
            components.append("theory_lib")
        
        return sorted(components)
    
    def _discover_subtheories(self) -> Dict[str, List[str]]:
        """Discover subtheories for theories that support them."""
        # Currently only logos supports subtheories
        return {
            'logos': ['modal', 'counterfactual', 'extensional', 'constitutive', 'relevance']
        }
    
    def _parse_positional_args(self, targets: List[str]) -> tuple[List[str], Dict[str, List[str]]]:
        """Parse positional arguments into theories and subtheories.
        
        Examples:
            ['logos'] -> (['logos'], {})
            ['logos', 'modal'] -> (['logos'], {'logos': ['modal']})
            ['logos', 'modal', 'counterfactual'] -> (['logos'], {'logos': ['modal', 'counterfactual']})
            ['exclusion', 'bimodal'] -> (['exclusion', 'bimodal'], {})
        """
        if not targets:
            return [], {}
        
        theories = []
        subtheories = {}
        
        i = 0
        while i < len(targets):
            target = targets[i]
            
            # Check if this is a theory
            if target in self.theories:
                theories.append(target)
                
                # Check if this theory supports subtheories and has them specified
                if target in self.subtheories:
                    theory_subtheories = []
                    # Look ahead for subtheories
                    j = i + 1
                    while j < len(targets) and targets[j] in self.subtheories[target]:
                        theory_subtheories.append(targets[j])
                        j += 1
                    
                    if theory_subtheories:
                        subtheories[target] = theory_subtheories
                        i = j  # Skip the subtheories we just processed
                    else:
                        i += 1
                else:
                    i += 1
            else:
                # Unknown target
                all_targets = self.theories + self.components
                available_subtheories = [sub for subs in self.subtheories.values() for sub in subs]
                all_targets.extend(available_subtheories)
                raise ValueError(f"Unknown target: {target}. Available: {', '.join(sorted(all_targets))}")
        
        return theories, subtheories
    
    def _print_startup_info(self, config: TestConfig) -> None:
        """Print information about what will be tested."""
        print("=" * 80)
        print("ModelChecker Unified Test Runner")
        print("=" * 80)
        
        test_types = []
        if config.run_examples:
            test_types.append("examples")
        if config.run_unit:
            test_types.append("unit")
        if config.run_package:
            test_types.append("package")
        
        print(f"Test types: {', '.join(test_types)}")
        
        if config.theories:
            print(f"Theories: {', '.join(config.theories)}")
            for theory, subs in config.subtheories.items():
                if subs:
                    print(f"  {theory} subtheories: {', '.join(subs)}")
        
        if config.components:
            print(f"Components: {', '.join(config.components)}")
    
    def _run_example_tests(self, config: TestConfig) -> TestResults:
        """Run example tests - placeholder for Phase 2."""
        results = TestResults()
        for theory in config.theories:
            # Placeholder: will be implemented in Phase 2
            print(f"  [PLACEHOLDER] Example tests for {theory}")
            results.add_theory_result(theory, 'examples', 0)  # Success placeholder
        return results
    
    def _run_unit_tests(self, config: TestConfig) -> TestResults:
        """Run unit tests - placeholder for Phase 2."""
        results = TestResults()
        for theory in config.theories:
            # Placeholder: will be implemented in Phase 2
            print(f"  [PLACEHOLDER] Unit tests for {theory}")
            results.add_theory_result(theory, 'unit', 0)  # Success placeholder
        return results
    
    def _run_package_tests(self, config: TestConfig) -> TestResults:
        """Run package tests - placeholder for Phase 2."""
        results = TestResults()
        for component in config.components:
            # Placeholder: will be implemented in Phase 2
            print(f"  [PLACEHOLDER] Package tests for {component}")
            results.add_component_result(component, 0)  # Success placeholder
        return results


def create_argument_parser() -> argparse.ArgumentParser:
    """Create command line argument parser."""
    parser = argparse.ArgumentParser(
        description="Unified test runner for ModelChecker theories and components",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  %(prog)s                          Run all tests (examples + unit + package)
  %(prog)s --examples               Run only example tests for all theories
  %(prog)s --unit                   Run only unit tests for all theories
  %(prog)s --package                Run only package tests for all components
  %(prog)s logos                    Run all test types for logos theory
  %(prog)s logos modal              Run all test types for logos modal subtheory
  %(prog)s --examples logos modal   Run example tests for logos modal subtheory
  %(prog)s exclusion bimodal        Run all test types for exclusion and bimodal
  %(prog)s --package builder        Run package tests for builder component
        """
    )
    
    # Test type selection
    test_group = parser.add_argument_group("Test Type Selection")
    test_group.add_argument(
        "--examples", 
        action="store_true",
        help="Run only example tests (integration tests from examples.py)"
    )
    test_group.add_argument(
        "--unit", 
        action="store_true",
        help="Run only unit tests (component/implementation tests)"
    )
    test_group.add_argument(
        "--package", 
        action="store_true",
        help="Run only package tests (framework infrastructure)"
    )
    
    # Target selection
    parser.add_argument(
        "targets",
        nargs="*",
        help="Theories and subtheories to test (e.g., 'logos modal counterfactual')"
    )
    parser.add_argument(
        "--components",
        nargs="+",
        help="Specific components to test (for --package)"
    )
    
    # Standard options
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
    
    return parser


def main():
    """Main entry point."""
    parser = create_argument_parser()
    args = parser.parse_args()
    
    try:
        # Create test runner and configuration
        runner = TestRunner()
        
        # Show available targets if none specified and no test type flags
        if not args.targets and not any([args.examples, args.unit, args.package]):
            print("Available theories:", ', '.join(runner.theories))
            print("Available components:", ', '.join(runner.components))
            print("Available subtheories (logos):", ', '.join(runner.subtheories.get('logos', [])))
            print("\nRunning all tests...")
        
        config = TestConfig.from_args(args, runner)
        
        # Run tests
        results = runner.run(config)
        
        # Print summary and exit
        results.print_summary()
        sys.exit(results.get_exit_code())
        
    except ValueError as e:
        print(f"Error: {e}", file=sys.stderr)
        sys.exit(1)
    except KeyboardInterrupt:
        print("\nTest execution interrupted by user", file=sys.stderr)
        sys.exit(1)
    except Exception as e:
        print(f"Unexpected error: {e}", file=sys.stderr)
        sys.exit(1)


if __name__ == "__main__":
    main()