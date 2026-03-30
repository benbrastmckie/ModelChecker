#!/usr/bin/env python3
"""comparison.py - Benchmark z3 vs cvc5 on logos theory examples.

This script systematically runs all logos theory examples against both z3 and cvc5
solvers, recording results and timing data to output.json for analysis.

Usage:
    python comparison.py                    # Run all examples
    python comparison.py --output results.json  # Custom output file
    python comparison.py --subtheory modal  # Run only modal examples
    python comparison.py --verbose          # Show per-example output

The output JSON includes:
- metadata: timestamp, solver versions, platform info
- summary: pass/fail counts and timing by solver
- by_subtheory: breakdown by logos subtheory
- results: per-example results with timing
- disagreements: examples where solvers disagree
"""

import argparse
import json
import platform
import sys
import time
from dataclasses import dataclass, field, asdict
from datetime import datetime
from typing import Any, Dict, List, Optional

from model_checker.solver import detect_cvc5, detect_z3
from model_checker.solver.registry import (
    set_cli_backend,
    clear_cli_backend,
    reset_registry,
)
from model_checker import z3_shim
from model_checker.theory_lib.logos import get_theory
from model_checker.theory_lib.logos.examples import all_subtheory_examples
from model_checker.builder.example import BuildExample
from types import SimpleNamespace
from unittest.mock import Mock


@dataclass
class SolverResult:
    """Result from running an example with a specific solver."""

    result: Optional[bool]  # True=SAT, False=UNSAT, None=error
    passed: bool  # Did result match expectation?
    time_seconds: float
    error: Optional[str] = None


@dataclass
class ExampleResult:
    """Combined results for an example across both solvers."""

    subtheory: str
    example_name: str
    expectation: Optional[bool]  # True=expect SAT, False=expect UNSAT
    z3: Optional[SolverResult] = None
    cvc5: Optional[SolverResult] = None


@dataclass
class SolverSummary:
    """Summary statistics for a single solver."""

    total_examples: int = 0
    passed: int = 0
    failed: int = 0
    errors: int = 0
    timeouts: int = 0
    total_time_seconds: float = 0.0
    avg_time_seconds: float = 0.0


@dataclass
class SubtheorySummary:
    """Summary statistics for a subtheory."""

    z3: Dict[str, Any] = field(default_factory=dict)
    cvc5: Dict[str, Any] = field(default_factory=dict)


@dataclass
class Disagreement:
    """Record of a solver disagreement."""

    example_name: str
    subtheory: str
    z3_result: Optional[bool]
    cvc5_result: Optional[bool]
    expectation: Optional[bool]


@dataclass
class BenchmarkMetadata:
    """Metadata about the benchmark run."""

    timestamp: str
    z3_version: str
    cvc5_version: str
    platform: str
    python_version: str
    total_examples: int
    total_runtime_seconds: float


@dataclass
class BenchmarkOutput:
    """Complete benchmark output structure."""

    metadata: BenchmarkMetadata
    summary: Dict[str, SolverSummary]
    by_subtheory: Dict[str, SubtheorySummary]
    results: List[Dict[str, Any]]
    disagreements: List[Dict[str, Any]]


def switch_solver(backend: str) -> None:
    """Switch to specified solver backend with full cache invalidation.

    This uses the three-step reset pattern from test_solver_comparison.py:
    1. Clear CLI backend first
    2. Reset registry caches
    3. Reset z3_shim cached module
    4. Set new backend

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


def get_required_subtheories(subtheory: str) -> List[str]:
    """Get the subtheory list required for a given subtheory's examples.

    Different subtheories have different dependency requirements:
    - extensional: just extensional
    - modal: extensional + modal + first_order
    - constitutive: extensional + modal + constitutive
    - counterfactual: extensional + modal + counterfactual
    - relevance: extensional + modal + constitutive + relevance
    - first_order: extensional + constitutive + first_order

    Args:
        subtheory: Name of the target subtheory

    Returns:
        List of subtheory names to load
    """
    subtheory_deps = {
        "extensional": ["extensional"],
        "modal": ["extensional", "modal", "first_order"],
        "constitutive": ["extensional", "modal", "constitutive"],
        "counterfactual": ["extensional", "modal", "counterfactual"],
        "relevance": ["extensional", "modal", "constitutive", "relevance"],
        "first_order": ["extensional", "constitutive", "first_order"],
    }
    return subtheory_deps.get(subtheory, ["extensional", subtheory])


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
        "N": 2,
        "contingent": False,
        "disjoint": False,
        "non_empty": True,
        "non_null": True,
        "print_constraints": False,
        "save_output": False,
        "print_impossible": False,
        "print_z3": False,
        "max_time": 5,
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
        maximize=False,
    )

    return mock_module


def flatten_examples(
    subtheory_filter: Optional[str] = None,
) -> List[tuple[str, str, List[Any]]]:
    """Flatten all_subtheory_examples into (subtheory, name, example) tuples.

    Args:
        subtheory_filter: If provided, only return examples from this subtheory

    Returns:
        List of (subtheory, example_name, example_case) tuples
    """
    examples = []
    for subtheory, subtheory_examples in all_subtheory_examples.items():
        if subtheory_filter and subtheory != subtheory_filter:
            continue
        for name, example in subtheory_examples.items():
            examples.append((subtheory, name, example))
    return examples


def run_example_with_timing(
    example_case: List[Any],
    theory: Dict[str, Any],
) -> tuple[Optional[bool], bool, float, Optional[str]]:
    """Run a single example and return result with timing.

    Args:
        example_case: [premises, conclusions, settings] tuple
        theory: The semantic theory dict

    Returns:
        Tuple of (result, passed, time_seconds, error_message)
        - result: True=SAT (countermodel found), False=UNSAT (theorem), None=error
        - passed: Whether result matches expectation
        - time_seconds: Elapsed time
        - error_message: Error string if exception occurred
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
    expectation = example_case[2].get("expectation", None)
    if result is None:
        passed = False
    elif expectation is None:
        passed = True  # No expectation, consider pass if no error
    else:
        # expectation=True means we expect a countermodel (SAT)
        # expectation=False means we expect no countermodel (UNSAT - theorem)
        passed = result == expectation

    return result, passed, elapsed, error


def get_z3_version() -> str:
    """Get z3 version string."""
    try:
        import z3

        return z3.get_version_string()
    except Exception:
        return "unknown"


def get_cvc5_version() -> str:
    """Get cvc5 version string."""
    try:
        import cvc5

        version = cvc5.Solver().getVersion()
        # Handle bytes if returned
        if isinstance(version, bytes):
            version = version.decode("utf-8")
        return str(version)
    except Exception:
        return "unknown"


def check_solver_availability() -> tuple[bool, bool]:
    """Check if z3 and cvc5 are available.

    Returns:
        Tuple of (z3_available, cvc5_available)
    """
    return detect_z3(), detect_cvc5()


def run_benchmarks(
    subtheory_filter: Optional[str] = None,
    verbose: bool = False,
) -> Dict[str, Any]:
    """Run all benchmarks and return structured results.

    Args:
        subtheory_filter: If provided, only run examples from this subtheory
        verbose: If True, print per-example output

    Returns:
        Dictionary with metadata, summary, by_subtheory, results, and disagreements
    """
    start_time = time.perf_counter()

    # Collect all examples
    examples = flatten_examples(subtheory_filter)
    total_examples = len(examples)

    print(f"Running {total_examples} examples against z3 and cvc5...")
    print()

    # Results storage
    results: List[Dict[str, Any]] = []
    disagreements: List[Dict[str, Any]] = []

    # Per-solver statistics
    solver_stats = {
        "z3": {
            "passed": 0,
            "failed": 0,
            "errors": 0,
            "times": [],
        },
        "cvc5": {
            "passed": 0,
            "failed": 0,
            "errors": 0,
            "times": [],
        },
    }

    # Per-subtheory statistics
    subtheory_stats: Dict[str, Dict[str, Dict[str, Any]]] = {}

    # Run each example with both solvers
    for idx, (subtheory, name, example_case) in enumerate(examples, 1):
        # Initialize subtheory stats if needed
        if subtheory not in subtheory_stats:
            subtheory_stats[subtheory] = {
                "z3": {"passed": 0, "failed": 0, "errors": 0, "time": 0.0},
                "cvc5": {"passed": 0, "failed": 0, "errors": 0, "time": 0.0},
            }

        expectation = example_case[2].get("expectation", None)

        result_entry = {
            "subtheory": subtheory,
            "example_name": name,
            "expectation": expectation,
        }

        # Run with each solver
        solver_results: Dict[str, Dict[str, Any]] = {}

        for solver in ["z3", "cvc5"]:
            switch_solver(solver)
            theory = get_theory(get_required_subtheories(subtheory))
            result, passed, elapsed, error = run_example_with_timing(
                example_case, theory
            )

            solver_result = {
                "result": result,
                "passed": passed,
                "time_seconds": round(elapsed, 6),
                "error": error,
            }
            solver_results[solver] = solver_result
            result_entry[solver] = solver_result

            # Update statistics
            solver_stats[solver]["times"].append(elapsed)
            if error:
                solver_stats[solver]["errors"] += 1
                subtheory_stats[subtheory][solver]["errors"] += 1
            elif passed:
                solver_stats[solver]["passed"] += 1
                subtheory_stats[subtheory][solver]["passed"] += 1
            else:
                solver_stats[solver]["failed"] += 1
                subtheory_stats[subtheory][solver]["failed"] += 1
            subtheory_stats[subtheory][solver]["time"] += elapsed

        results.append(result_entry)

        # Check for disagreement
        z3_result = solver_results["z3"]["result"]
        cvc5_result = solver_results["cvc5"]["result"]
        if z3_result != cvc5_result:
            disagreements.append(
                {
                    "example_name": name,
                    "subtheory": subtheory,
                    "z3_result": z3_result,
                    "cvc5_result": cvc5_result,
                    "expectation": expectation,
                }
            )

        # Progress output
        if verbose:
            z3_status = "PASS" if solver_results["z3"]["passed"] else "FAIL"
            cvc5_status = "PASS" if solver_results["cvc5"]["passed"] else "FAIL"
            z3_err = " (error)" if solver_results["z3"]["error"] else ""
            cvc5_err = " (error)" if solver_results["cvc5"]["error"] else ""
            disagree = " [DISAGREE]" if z3_result != cvc5_result else ""
            print(
                f"  [{idx}/{total_examples}] {name}: "
                f"z3={z3_status}{z3_err} cvc5={cvc5_status}{cvc5_err}{disagree}"
            )
        elif idx % 20 == 0:
            print(f"  Progress: {idx}/{total_examples}")

    total_runtime = time.perf_counter() - start_time

    # Build summary
    summary = {}
    for solver in ["z3", "cvc5"]:
        stats = solver_stats[solver]
        times = stats["times"]
        summary[solver] = {
            "total_examples": len(times),
            "passed": stats["passed"],
            "failed": stats["failed"],
            "errors": stats["errors"],
            "total_time_seconds": round(sum(times), 4),
            "avg_time_seconds": round(sum(times) / len(times), 6) if times else 0.0,
        }

    # Build by_subtheory with rounded times
    by_subtheory = {}
    for sub, stats in subtheory_stats.items():
        by_subtheory[sub] = {
            "z3": {
                "passed": stats["z3"]["passed"],
                "failed": stats["z3"]["failed"],
                "errors": stats["z3"]["errors"],
                "time": round(stats["z3"]["time"], 4),
            },
            "cvc5": {
                "passed": stats["cvc5"]["passed"],
                "failed": stats["cvc5"]["failed"],
                "errors": stats["cvc5"]["errors"],
                "time": round(stats["cvc5"]["time"], 4),
            },
        }

    # Build output structure
    output = {
        "metadata": {
            "timestamp": datetime.now().isoformat(),
            "z3_version": get_z3_version(),
            "cvc5_version": get_cvc5_version(),
            "platform": platform.system(),
            "python_version": platform.python_version(),
            "total_examples": total_examples,
            "total_runtime_seconds": round(total_runtime, 2),
        },
        "summary": summary,
        "by_subtheory": by_subtheory,
        "results": results,
        "disagreements": disagreements,
    }

    # Print summary
    print()
    print("=" * 60)
    print("BENCHMARK SUMMARY")
    print("=" * 60)
    print(
        f"Z3:   {summary['z3']['passed']}/{summary['z3']['total_examples']} passed, "
        f"{summary['z3']['errors']} errors, "
        f"avg {summary['z3']['avg_time_seconds']:.4f}s, "
        f"total {summary['z3']['total_time_seconds']:.2f}s"
    )
    print(
        f"CVC5: {summary['cvc5']['passed']}/{summary['cvc5']['total_examples']} passed, "
        f"{summary['cvc5']['errors']} errors, "
        f"avg {summary['cvc5']['avg_time_seconds']:.4f}s, "
        f"total {summary['cvc5']['total_time_seconds']:.2f}s"
    )

    if disagreements:
        print(f"\nDisagreements: {len(disagreements)}")
        for d in disagreements:
            print(
                f"  {d['example_name']}: z3={d['z3_result']} vs cvc5={d['cvc5_result']}"
            )

    print()
    print("By Subtheory:")
    for sub, stats in sorted(by_subtheory.items()):
        print(
            f"  {sub}: z3={stats['z3']['time']:.3f}s, cvc5={stats['cvc5']['time']:.3f}s"
        )
    print("=" * 60)

    return output


def parse_args() -> argparse.Namespace:
    """Parse command line arguments."""
    parser = argparse.ArgumentParser(
        description="Benchmark z3 vs cvc5 on logos theory examples"
    )
    parser.add_argument(
        "--output",
        "-o",
        default="output.json",
        help="Output JSON file (default: output.json)",
    )
    parser.add_argument(
        "--subtheory",
        "-s",
        choices=[
            "extensional",
            "modal",
            "constitutive",
            "counterfactual",
            "relevance",
            "first_order",
        ],
        help="Run only examples from this subtheory",
    )
    parser.add_argument(
        "--verbose",
        "-v",
        action="store_true",
        help="Show detailed per-example output",
    )
    return parser.parse_args()


def main() -> int:
    """Main entry point for the comparison script.

    Returns:
        Exit code (0 for success, 1 for error)
    """
    args = parse_args()

    # Check solver availability
    z3_available, cvc5_available = check_solver_availability()

    if not z3_available:
        print("Error: z3 is not installed or not available")
        return 1

    if not cvc5_available:
        print("Error: cvc5 is not installed or not available")
        print("This script requires both z3 and cvc5 for comparison.")
        return 1

    print("Solver availability check passed:")
    print(f"  z3: {get_z3_version()}")
    print(f"  cvc5: {get_cvc5_version()}")
    print()

    # Run benchmarks
    results = run_benchmarks(
        subtheory_filter=args.subtheory,
        verbose=args.verbose,
    )

    # Write output
    with open(args.output, "w") as f:
        json.dump(results, f, indent=2)

    print(f"\nResults written to {args.output}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
