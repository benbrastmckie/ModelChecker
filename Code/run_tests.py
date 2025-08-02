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
import time
from dataclasses import dataclass
from typing import List, Dict, Optional, Union, Tuple
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
        # Also use all components if no specific test type is requested (running all tests)
        use_all_components = args.package or (not args.examples and not args.unit)
        components = args.components or (runner.components if use_all_components else [])
        
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
        self.subtheory_counts: Dict[str, Dict[str, int]] = {}  # theory -> subtheory -> count
        self.theory_timings: Dict[str, Dict[str, float]] = {}  # theory -> test_type -> time_taken
        self.subtheory_timings: Dict[str, Dict[str, float]] = {}  # theory -> subtheory -> time_taken
    
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
    
    def add_subtheory_count(self, theory: str, subtheory: str, count: int) -> None:
        """Add example count for a subtheory."""
        if theory not in self.subtheory_counts:
            self.subtheory_counts[theory] = {}
        self.subtheory_counts[theory][subtheory] = count
    
    def add_theory_timing(self, theory: str, test_type: str, time_taken: float) -> None:
        """Add timing for theory test execution."""
        if theory not in self.theory_timings:
            self.theory_timings[theory] = {}
        self.theory_timings[theory][test_type] = time_taken
    
    def add_subtheory_timing(self, theory: str, subtheory: str, time_taken: float) -> None:
        """Add timing for subtheory test execution."""
        if theory not in self.subtheory_timings:
            self.subtheory_timings[theory] = {}
        self.subtheory_timings[theory][subtheory] = time_taken
    
    def merge(self, other: 'TestResults') -> None:
        """Merge another TestResults into this one."""
        for theory, results in other.theory_results.items():
            if theory not in self.theory_results:
                self.theory_results[theory] = {}
            self.theory_results[theory].update(results)
        
        self.component_results.update(other.component_results)
        
        # Merge subtheory counts
        for theory, counts in other.subtheory_counts.items():
            if theory not in self.subtheory_counts:
                self.subtheory_counts[theory] = {}
            self.subtheory_counts[theory].update(counts)
        
        # Merge theory timings
        for theory, timings in other.theory_timings.items():
            if theory not in self.theory_timings:
                self.theory_timings[theory] = {}
            self.theory_timings[theory].update(timings)
        
        # Merge subtheory timings
        for theory, timings in other.subtheory_timings.items():
            if theory not in self.subtheory_timings:
                self.subtheory_timings[theory] = {}
            self.subtheory_timings[theory].update(timings)
        
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
                    
                    # Show timing info
                    if theory in self.theory_timings and test_type in self.theory_timings[theory]:
                        time_taken = self.theory_timings[theory][test_type]
                        print(f"    Time: {time_taken:.2f}s")
                    
                    # Show example counts for all theories
                    if test_type == "examples" and theory in self.subtheory_counts:
                        if theory == "logos":
                            print(f"    Subtheory example counts:")
                            for subtheory, count in sorted(self.subtheory_counts[theory].items()):
                                timing_str = ""
                                if theory in self.subtheory_timings and subtheory in self.subtheory_timings[theory]:
                                    timing_str = f" ({self.subtheory_timings[theory][subtheory]:.2f}s)"
                                print(f"      {subtheory}: {count} examples{timing_str}")
                            total = sum(self.subtheory_counts[theory].values())
                            total_time = sum(self.subtheory_timings.get(theory, {}).values())
                            print(f"      Total: {total} examples ({total_time:.2f}s)")
                        else:
                            # For non-logos theories, just show the total
                            if "total" in self.subtheory_counts[theory]:
                                print(f"    Example count: {self.subtheory_counts[theory]['total']} examples")
        
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


class ExampleTestRunner:
    """Runs integration tests from examples.py files."""
    
    def __init__(self, code_dir: Path):
        self.code_dir = code_dir
        self.src_dir = code_dir / "src"
    
    def run_theory_examples(self, theory: str, subtheories: List[str], config: TestConfig, 
                           results: Optional[TestResults] = None) -> int:
        """Run example tests for a specific theory with optional subtheory filtering."""
        if theory == 'logos':
            return self._run_logos_example_tests(subtheories, config, results)
        else:
            return self._run_standard_example_tests(theory, config, results)
    
    def _run_logos_example_tests(self, subtheories: List[str], config: TestConfig, 
                                results: Optional[TestResults] = None) -> int:
        """Run logos example tests from subtheory directories."""
        overall_exit_code = 0
        
        # Determine which subtheories to test
        target_subtheories = subtheories if subtheories else ['modal', 'counterfactual', 'extensional', 'constitutive', 'relevance']
        
        for subtheory in target_subtheories:
            subtheory_test_dir = self.src_dir / "model_checker" / "theory_lib" / "logos" / "subtheories" / subtheory / "tests"
            
            if not subtheory_test_dir.exists():
                print(f"      Warning: No tests found for logos {subtheory} subtheory")
                continue
            
            print(f"      Testing {subtheory} subtheory examples")
            
            # Count examples first if results object provided
            if results:
                example_count = self._count_subtheory_examples(subtheory)
                if example_count > 0:
                    results.add_subtheory_count("logos", subtheory, example_count)
            
            # Build command for subtheory examples
            command = ["pytest", str(subtheory_test_dir)]
            command.extend(["-k", "example"])  # Only example tests (matches both "examples" and "example_cases")
            
            if config.verbose:
                command.append("-v")
            if config.failfast:
                command.append("-x")
            
            # Execute tests and measure time
            env = self._setup_environment()
            start_time = time.time()
            try:
                result = subprocess.run(command, cwd=self.code_dir, env=env)
                elapsed_time = time.time() - start_time
                
                # Record timing if results object provided
                if results:
                    results.add_subtheory_timing("logos", subtheory, elapsed_time)
                
                if result.returncode != 0:
                    overall_exit_code = result.returncode
                    if config.failfast:
                        break
            except Exception as e:
                elapsed_time = time.time() - start_time
                if results:
                    results.add_subtheory_timing("logos", subtheory, elapsed_time)
                print(f"      Error running {subtheory} examples: {e}")
                overall_exit_code = 1
                if config.failfast:
                    break
        
        return overall_exit_code
    
    def _run_standard_example_tests(self, theory: str, config: TestConfig, 
                                   results: Optional[TestResults] = None) -> int:
        """Run example tests for standard theories (non-logos)."""
        test_dir = self.src_dir / "model_checker" / "theory_lib" / theory / "tests"
        
        if not test_dir.exists():
            print(f"    Warning: No test directory found for {theory}")
            return 0
        
        # Count examples first if results object provided
        if results:
            example_count = self._count_theory_examples(theory)
            if example_count > 0:
                results.add_subtheory_count(theory, "total", example_count)
        
        # Build pytest command
        command = ["pytest", str(test_dir)]
        command.extend(["-k", "example"])  # Only example tests (matches both "examples" and "example_cases")
        
        if config.verbose:
            command.append("-v")
        if config.failfast:
            command.append("-x")
        
        # Set up environment and execute
        env = self._setup_environment()
        try:
            result = subprocess.run(command, cwd=self.code_dir, env=env)
            return result.returncode
        except Exception as e:
            print(f"    Error running example tests for {theory}: {e}")
            return 1
    
    def _count_subtheory_examples(self, subtheory: str) -> int:
        """Count the number of examples for a logos subtheory."""
        examples_file = self.src_dir / "model_checker" / "theory_lib" / "logos" / "subtheories" / subtheory / "examples.py"
        
        if not examples_file.exists():
            return 0
        
        # Count examples by looking for patterns like "XXX_TH_N_example" or "XXX_CM_N_example"
        count = 0
        try:
            with open(examples_file, 'r') as f:
                content = f.read()
                # Match patterns like MOD_TH_1_example, CF_CM_2_example, etc.
                import re
                pattern = r'^[A-Z]+_(?:TH|CM)_\d+_example\s*='
                matches = re.findall(pattern, content, re.MULTILINE)
                count = len(matches)
        except Exception:
            pass
        
        return count
    
    def _count_theory_examples(self, theory: str) -> int:
        """Count the number of examples for a standard theory."""
        examples_file = self.src_dir / "model_checker" / "theory_lib" / theory / "examples.py"
        
        if not examples_file.exists():
            return 0
        
        # Count examples by looking for patterns
        count = 0
        try:
            with open(examples_file, 'r') as f:
                content = f.read()
                # Match patterns - theories use different prefixes
                import re
                # Generic pattern to match various naming conventions
                patterns = [
                    r'^[A-Z]+_(?:TH|CM)_\d+_example\s*=',  # Standard pattern like MOD_TH_1_example
                    r'^[A-Za-z_]+_example_\d+\s*=',        # Pattern like exclusion_example_1
                    r'^example_[A-Za-z_]+_\d+\s*=',        # Pattern like example_counterfactual_1
                    r'^[A-Za-z]+Example\d+\s*=',           # Pattern like ImpositionExample1
                ]
                
                for pattern in patterns:
                    matches = re.findall(pattern, content, re.MULTILINE)
                    count += len(matches)
        except Exception:
            pass
        
        return count
    
    
    def _setup_environment(self) -> Dict[str, str]:
        """Set up environment for test execution."""
        env = os.environ.copy()
        env['PYTHONPATH'] = str(self.src_dir)
        return env


class UnitTestRunner:
    """Runs unit tests for theory implementations."""
    
    def __init__(self, code_dir: Path):
        self.code_dir = code_dir
        self.src_dir = code_dir / "src"
    
    def run_theory_units(self, theory: str, subtheories: List[str], config: TestConfig) -> int:
        """Run unit tests for a specific theory with optional subtheory filtering."""
        if theory == 'logos':
            return self._run_logos_unit_tests(subtheories, config)
        else:
            return self._run_standard_unit_tests(theory, config)
    
    def _run_logos_unit_tests(self, subtheories: List[str], config: TestConfig) -> int:
        """Run logos unit tests from main tests directory with subtheory filtering."""
        test_dir = self.src_dir / "model_checker" / "theory_lib" / "logos" / "tests"
        
        if not test_dir.exists():
            print(f"    Warning: No test directory found for logos")
            return 0
        
        # Build command for logos unit tests
        command = ["pytest", str(test_dir)]
        
        # Add subtheory filtering if specified
        if subtheories:
            # Build filter for specific subtheories
            subtheory_patterns = {
                'modal': '(modal or MOD_)',
                'counterfactual': '(counterfactual or CF_)', 
                'extensional': '(extensional or EXT_)',
                'constitutive': '(constitutive or CON_ or CL_)',
                'relevance': '(relevance or REL_)'
            }
            
            patterns = [subtheory_patterns[sub] for sub in subtheories if sub in subtheory_patterns]
            if patterns:
                filter_expr = f"({' or '.join(patterns)}) and not example"
                command.extend(["-k", filter_expr])
            else:
                command.extend(["-k", "not example"])  # Just exclude examples
        else:
            command.extend(["-k", "not example"])  # Exclude example tests
        
        if config.verbose:
            command.append("-v")
        if config.failfast:
            command.append("-x")
        
        # Execute tests
        env = self._setup_environment()
        try:
            result = subprocess.run(command, cwd=self.code_dir, env=env)
            return result.returncode
        except Exception as e:
            print(f"    Error running unit tests for logos: {e}")
            return 1
    
    def _run_standard_unit_tests(self, theory: str, config: TestConfig) -> int:
        """Run unit tests for standard theories (non-logos)."""
        test_dir = self.src_dir / "model_checker" / "theory_lib" / theory / "tests"
        
        if not test_dir.exists():
            print(f"    Warning: No test directory found for {theory}")
            return 0
        
        # Build pytest command
        command = ["pytest", str(test_dir)]
        command.extend(["-k", "not example"])  # Exclude example tests
        
        if config.verbose:
            command.append("-v")
        if config.failfast:
            command.append("-x")
        
        # Set up environment and execute
        env = self._setup_environment()
        try:
            result = subprocess.run(command, cwd=self.code_dir, env=env)
            return result.returncode
        except Exception as e:
            print(f"    Error running unit tests for {theory}: {e}")
            return 1
    
    
    def _setup_environment(self) -> Dict[str, str]:
        """Set up environment for test execution."""
        env = os.environ.copy()
        env['PYTHONPATH'] = str(self.src_dir)
        return env


class PackageTestRunner:
    """Runs package/infrastructure component tests."""
    
    def __init__(self, code_dir: Path):
        self.code_dir = code_dir
        self.src_dir = code_dir / "src"
    
    def run_component_tests(self, component: str, config: TestConfig) -> int:
        """Run tests for a specific package component."""
        if component == "theory_lib":
            test_dir = self.src_dir / "model_checker" / "theory_lib" / "tests"
        else:
            test_dir = self.src_dir / "model_checker" / component / "tests"
        
        if not test_dir.exists():
            print(f"    Warning: No test directory found for {component}")
            return 0
        
        # Build pytest command
        command = self._build_pytest_command(test_dir, config)
        
        # Set up environment
        env = self._setup_environment()
        
        # Execute tests
        try:
            result = subprocess.run(command, cwd=self.code_dir, env=env)
            return result.returncode
        except Exception as e:
            print(f"    Error running package tests for {component}: {e}")
            return 1
    
    def _build_pytest_command(self, test_dir: Path, config: TestConfig) -> List[str]:
        """Build pytest command for package tests."""
        command = ["pytest", str(test_dir)]
        
        # Add standard pytest options
        if config.verbose:
            command.append("-v")
        if config.failfast:
            command.append("-x")
        
        return command
    
    def _setup_environment(self) -> Dict[str, str]:
        """Set up environment for test execution."""
        env = os.environ.copy()
        env['PYTHONPATH'] = str(self.src_dir)
        return env


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
        """Discover available theories."""
        theories = []
        theory_lib_dir = self.code_dir / "src" / "model_checker" / "theory_lib"
        
        if not theory_lib_dir.exists():
            return theories
        
        for item in theory_lib_dir.iterdir():
            if (item.is_dir() and 
                not item.name.startswith('__') and 
                item.name != 'bimodal' and  # Exclude bimodal theory (not finished)
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
        """Run example tests for specified theories/subtheories."""
        results = TestResults()
        example_runner = ExampleTestRunner(self.code_dir)
        
        for theory in config.theories:
            subtheories = config.subtheories.get(theory, [])
            print(f"  Running example tests for {theory}")
            if subtheories:
                print(f"    Subtheories: {', '.join(subtheories)}")
            
            start_time = time.time()
            exit_code = example_runner.run_theory_examples(theory, subtheories, config, results)
            elapsed_time = time.time() - start_time
            
            results.add_theory_result(theory, 'examples', exit_code)
            results.add_theory_timing(theory, 'examples', elapsed_time)
            
            if exit_code != 0 and config.failfast:
                break
        
        return results
    
    def _run_unit_tests(self, config: TestConfig) -> TestResults:
        """Run unit tests for specified theories/subtheories."""
        results = TestResults()
        unit_runner = UnitTestRunner(self.code_dir)
        
        for theory in config.theories:
            subtheories = config.subtheories.get(theory, [])
            print(f"  Running unit tests for {theory}")
            if subtheories:
                print(f"    Subtheories: {', '.join(subtheories)}")
            
            start_time = time.time()
            exit_code = unit_runner.run_theory_units(theory, subtheories, config)
            elapsed_time = time.time() - start_time
            
            results.add_theory_result(theory, 'unit', exit_code)
            results.add_theory_timing(theory, 'unit', elapsed_time)
            
            if exit_code != 0 and config.failfast:
                break
        
        return results
    
    def _run_package_tests(self, config: TestConfig) -> TestResults:
        """Run package tests for specified components."""
        results = TestResults()
        package_runner = PackageTestRunner(self.code_dir)
        
        for component in config.components:
            print(f"  Running package tests for {component}")
            
            exit_code = package_runner.run_component_tests(component, config)
            results.add_component_result(component, exit_code)
            
            if exit_code != 0 and config.failfast:
                break
        
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
