"""Solver comparison test suite for logos theory examples.

This module runs all subtheory examples against both z3 and cvc5 backends,
collecting timing data for systematic comparison.

Usage:
    # Run all solver comparison tests
    pytest test_solver_comparison.py -v

    # Run specific subtheory
    pytest test_solver_comparison.py -k "first_order" -v

    # Run specific solver
    pytest test_solver_comparison.py -k "z3" -v
"""

import time
from dataclasses import dataclass, field
from typing import List, Dict, Any, Optional

import pytest

from model_checker.solver import detect_cvc5, detect_z3
from model_checker.solver.registry import set_cli_backend, clear_cli_backend, reset_registry
from model_checker import z3_shim
from model_checker.theory_lib.logos import get_theory
from model_checker.theory_lib.logos.examples import all_subtheory_examples
from model_checker.builder.example import BuildExample
from model_checker.builder.module import BuildModule
from types import SimpleNamespace
from unittest.mock import Mock


# Skip all tests if cvc5 is not available
pytestmark = pytest.mark.skipif(
    not detect_cvc5(),
    reason="cvc5 not installed - solver comparison requires both backends"
)


@dataclass
class SolverTestResult:
    """Data class for storing test results."""
    solver: str
    subtheory: str
    example_name: str
    passed: bool
    time_seconds: float
    expectation: Optional[bool]
    result: Optional[bool] = None
    error: Optional[str] = None


# Module-level results collection
_test_results: List[SolverTestResult] = []


def switch_solver(backend: str) -> None:
    """Switch to specified solver backend with full cache invalidation.

    Args:
        backend: Either 'z3' or 'cvc5'
    """
    # Clear CLI backend first
    clear_cli_backend()
    # Reset registry caches
    reset_registry()
    # Reset z3_shim cached module
    z3_shim._reset_backend()
    # Set new backend
    set_cli_backend(backend)


@pytest.fixture(autouse=True)
def reset_state():
    """Reset registry state before and after each test."""
    reset_registry()
    z3_shim._reset_backend()
    clear_cli_backend()
    yield
    reset_registry()
    z3_shim._reset_backend()
    clear_cli_backend()


def get_required_subtheories(subtheory: str) -> List[str]:
    """Get the subtheory list required for a given subtheory's examples.

    Different subtheories have different dependency requirements:
    - extensional: just extensional
    - modal: extensional + modal
    - constitutive: extensional + modal + constitutive
    - counterfactual: extensional + modal + counterfactual
    - relevance: extensional + modal + constitutive + relevance
    - first_order: extensional + constitutive + first_order
    """
    subtheory_deps = {
        'extensional': ['extensional'],
        'modal': ['extensional', 'modal'],
        'constitutive': ['extensional', 'modal', 'constitutive'],
        'counterfactual': ['extensional', 'modal', 'counterfactual'],
        'relevance': ['extensional', 'modal', 'constitutive', 'relevance'],
        'first_order': ['extensional', 'constitutive', 'first_order'],
    }
    return subtheory_deps.get(subtheory, ['extensional', subtheory])


def create_test_module(theory: Dict[str, Any]) -> Mock:
    """Create a mock build module for testing.

    Args:
        theory: The semantic theory dict from get_theory()

    Returns:
        Mock module suitable for BuildExample
    """
    mock_module = Mock()
    mock_module.semantic_theories = {"logos": theory}

    general_settings = {
        'N': 2,
        'contingent': False,
        'disjoint': False,
        'non_empty': True,
        'non_null': True,
        'print_constraints': False,
        'save_output': False,
        'print_impossible': False,
        'print_z3': False,
        'max_time': 5
    }
    mock_module.general_settings = general_settings
    mock_module.raw_general_settings = general_settings
    mock_module.module_flags = SimpleNamespace(
        contingent=False,
        disjoint=False,
        non_empty=False,
        non_null=False,
        print_constraints=False,
        save_output=False,
        print_impossible=False,
        print_z3=False,
        maximize=False
    )

    return mock_module


def run_example_with_timing(
    example_case: List[Any],
    theory: Dict[str, Any],
) -> tuple[bool, float, Optional[str]]:
    """Run a single example and return result with timing.

    Args:
        example_case: [premises, conclusions, settings] tuple
        theory: The semantic theory dict

    Returns:
        Tuple of (result_matches_expectation, time_seconds, error_message)
    """
    start_time = time.perf_counter()
    error = None
    result = None

    try:
        mock_module = create_test_module(theory)
        example = BuildExample(mock_module, theory, example_case)

        # Check if a model was found (countermodel exists)
        # z3_model_status is True/truthy when SAT (countermodel found)
        # z3_model_status is False/None when UNSAT (no countermodel - theorem)
        result = bool(example.model_structure.z3_model_status)

    except Exception as e:
        error = str(e)
        result = None

    elapsed = time.perf_counter() - start_time

    # Compare with expectation
    expectation = example_case[2].get('expectation', None)
    if result is None:
        passed = False
    elif expectation is None:
        passed = True  # No expectation, consider pass if no error
    else:
        # expectation=True means we expect a countermodel (SAT)
        # expectation=False means we expect no countermodel (UNSAT - theorem)
        passed = (result == expectation)

    return passed, elapsed, error


def flatten_examples() -> List[tuple[str, str, List[Any]]]:
    """Flatten all_subtheory_examples into (subtheory, name, example) tuples."""
    examples = []
    for subtheory, subtheory_examples in all_subtheory_examples.items():
        for name, example in subtheory_examples.items():
            examples.append((subtheory, name, example))
    return examples


# Generate test parameters
def get_test_parameters():
    """Generate parametrized test cases for all examples and both solvers."""
    examples = flatten_examples()
    params = []
    for subtheory, name, example in examples:
        for solver in ['z3', 'cvc5']:
            params.append(pytest.param(
                solver, subtheory, name, example,
                id=f"{solver}-{name}"
            ))
    return params


@pytest.mark.parametrize(
    "solver,subtheory,example_name,example_case",
    get_test_parameters()
)
def test_example_with_solver(solver, subtheory, example_name, example_case):
    """Test a single example with a specific solver backend.

    This test:
    1. Switches to the specified solver backend
    2. Loads the theory with required subtheories
    3. Runs the example
    4. Verifies the result matches expectation
    5. Records timing data
    """
    # Switch to the target solver
    switch_solver(solver)

    # Get required subtheories for this example
    required_subs = get_required_subtheories(subtheory)

    # Load theory with correct subtheories
    theory = get_theory(required_subs)

    # Run with timing
    passed, elapsed, error = run_example_with_timing(example_case, theory)

    # Record result
    expectation = example_case[2].get('expectation', None)
    result = SolverTestResult(
        solver=solver,
        subtheory=subtheory,
        example_name=example_name,
        passed=passed,
        time_seconds=elapsed,
        expectation=expectation,
        error=error
    )
    _test_results.append(result)

    # Assert passed
    if error:
        pytest.fail(f"Example {example_name} with {solver} failed: {error}")

    assert passed, (
        f"Example {example_name} with {solver}: "
        f"expectation={expectation}, but result did not match"
    )


def pytest_sessionfinish(session, exitstatus):
    """Generate report after test session completes."""
    if not _test_results:
        return

    # Group results by solver
    z3_results = [r for r in _test_results if r.solver == 'z3']
    cvc5_results = [r for r in _test_results if r.solver == 'cvc5']

    # Calculate statistics
    def stats(results):
        if not results:
            return {'count': 0, 'passed': 0, 'failed': 0, 'avg_time': 0, 'total_time': 0}
        passed = sum(1 for r in results if r.passed)
        failed = len(results) - passed
        total_time = sum(r.time_seconds for r in results)
        avg_time = total_time / len(results) if results else 0
        return {
            'count': len(results),
            'passed': passed,
            'failed': failed,
            'avg_time': avg_time,
            'total_time': total_time
        }

    z3_stats = stats(z3_results)
    cvc5_stats = stats(cvc5_results)

    # Print summary
    print("\n" + "=" * 60)
    print("SOLVER COMPARISON SUMMARY")
    print("=" * 60)
    print(f"\nZ3:   {z3_stats['passed']}/{z3_stats['count']} passed, "
          f"avg {z3_stats['avg_time']:.3f}s, total {z3_stats['total_time']:.2f}s")
    print(f"CVC5: {cvc5_stats['passed']}/{cvc5_stats['count']} passed, "
          f"avg {cvc5_stats['avg_time']:.3f}s, total {cvc5_stats['total_time']:.2f}s")

    # Group by subtheory
    subtheories = set(r.subtheory for r in _test_results)
    print("\nBy Subtheory:")
    for sub in sorted(subtheories):
        sub_z3 = [r for r in z3_results if r.subtheory == sub]
        sub_cvc5 = [r for r in cvc5_results if r.subtheory == sub]
        z3_time = sum(r.time_seconds for r in sub_z3)
        cvc5_time = sum(r.time_seconds for r in sub_cvc5)
        print(f"  {sub}: z3={z3_time:.3f}s, cvc5={cvc5_time:.3f}s")

    print("=" * 60)


class TestSolverSwitching:
    """Tests to verify solver switching works correctly."""

    def test_z3_available(self):
        """Verify z3 is available."""
        assert detect_z3(), "z3 should be available"

    def test_cvc5_available(self):
        """Verify cvc5 is available (or tests should have been skipped)."""
        assert detect_cvc5(), "cvc5 should be available for these tests"

    def test_switch_to_z3(self):
        """Test switching to z3 backend."""
        switch_solver('z3')
        from model_checker.solver import get_active_backend
        assert get_active_backend() == 'z3'

    def test_switch_to_cvc5(self):
        """Test switching to cvc5 backend."""
        switch_solver('cvc5')
        from model_checker.solver import get_active_backend
        assert get_active_backend() == 'cvc5'
