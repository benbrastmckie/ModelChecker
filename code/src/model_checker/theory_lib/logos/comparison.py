#!/usr/bin/env python3
"""comparison.py - Benchmark z3 vs cvc5 on logos theory examples.

This script systematically runs logos theory examples against both z3 and cvc5
solvers, recording results and timing data to output.json for analysis.

Usage:
    python comparison.py                         # Run all examples
    python comparison.py --curated               # Run curated 24 examples
    python comparison.py --curated --table       # ASCII table output
    python comparison.py --curated --format timing  # Timing-focused JSON
    python comparison.py --output results.json   # Custom output file
    python comparison.py --subtheory modal       # Run only modal examples
    python comparison.py --verbose               # Show per-example output
    python comparison.py --timeout 60            # Custom timeout per example

Flags:
    --curated, -c    Run curated 24 examples (4 per subtheory) for quick comparison
    --format, -f     Output format: 'full' (default) or 'timing' (simplified)
    --table          Print ASCII table to console
    --verbose, -v    Show detailed per-example output
    --timeout, -t    Timeout per example per solver in seconds (default: 30)
    --subtheory, -s  Filter to specific subtheory
    --output, -o     Output JSON file (default: output.json)

The output JSON includes:
- metadata: timestamp, solver versions, platform info, curated flag
- summary: pass/fail counts and timing by solver
- timing_summary: per-solver timing statistics (fastest/slowest examples)
- comparison_stats: agreement counts, faster solver counts, avg time ratio
- by_subtheory: breakdown by logos subtheory
- results: per-example results with timing and comparison fields
- disagreements: examples where solvers disagree
"""

import argparse
import json
import platform
import signal
import sys
import time
from dataclasses import dataclass, field, asdict
from datetime import datetime
from typing import Any, Dict, List, Optional


class ExampleTimeout(Exception):
    """Raised when an example exceeds its time limit."""
    pass


def _timeout_handler(signum, frame):
    raise ExampleTimeout("Example timed out")

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


# Curated example selection for focused comparison testing
# 24 examples total: 4 per subtheory (2 theorems + 2 countermodels)
COMPARISON_EXAMPLES = {
    "extensional": ["EXT_TH_1", "EXT_TH_7", "EXT_CM_1", "EXT_CM_2"],
    "modal": ["MOD_TH_5", "MOD_TH_3", "MOD_CM_1", "MOD_CM_3"],
    "constitutive": ["CL_TH_1", "CL_TH_16", "CL_CM_1", "CL_CM_7"],
    "counterfactual": ["CF_TH_1", "CF_TH_2", "CF_CM_1", "CF_CM_7"],
    "relevance": ["REL_TH_1", "REL_TH_7", "REL_CM_1", "REL_CM_3"],
}


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


@dataclass
class TimingSummary:
    """Timing-focused summary for a single solver."""

    total_time_seconds: float = 0.0
    avg_time_seconds: float = 0.0
    fastest_example: str = ""
    fastest_time: float = 0.0
    slowest_example: str = ""
    slowest_time: float = 0.0


@dataclass
class ComparisonStats:
    """Statistics comparing the two solvers."""

    agreements: int = 0
    disagreements: int = 0
    z3_faster_count: int = 0
    cvc5_faster_count: int = 0
    ties: int = 0
    avg_time_ratio: float = 0.0  # slower/faster ratio average


def format_as_table(results: Dict[str, Any]) -> str:
    """Format benchmark results as an ASCII table.

    Args:
        results: Full benchmark results dictionary

    Returns:
        ASCII table string for console output
    """
    lines = []

    # Header
    lines.append("+" + "-" * 78 + "+")
    lines.append("| {:^76} |".format("DUAL-SOLVER TIMING COMPARISON"))
    lines.append("+" + "-" * 78 + "+")

    # Metadata
    meta = results["metadata"]
    lines.append("| {:20} {:55} |".format("Timestamp:", meta["timestamp"][:19]))
    lines.append("| {:20} {:55} |".format("Z3 Version:", meta["z3_version"]))
    lines.append("| {:20} {:55} |".format("CVC5 Version:", meta["cvc5_version"]))
    lines.append("| {:20} {:55} |".format("Total Examples:", str(meta["total_examples"])))
    curated_str = "Yes" if meta.get("curated", False) else "No"
    lines.append("| {:20} {:55} |".format("Curated:", curated_str))
    lines.append("+" + "-" * 78 + "+")

    # Timing Summary
    lines.append("| {:^76} |".format("TIMING SUMMARY"))
    lines.append("+" + "-" * 39 + "+" + "-" * 38 + "+")
    lines.append("| {:^37} | {:^36} |".format("Z3", "CVC5"))
    lines.append("+" + "-" * 39 + "+" + "-" * 38 + "+")

    ts = results["timing_summary"]
    lines.append("| Total:   {:>27.4f}s | Total:   {:>25.4f}s |".format(
        ts["z3"]["total_time_seconds"], ts["cvc5"]["total_time_seconds"]))
    lines.append("| Avg:     {:>27.6f}s | Avg:     {:>25.6f}s |".format(
        ts["z3"]["avg_time_seconds"], ts["cvc5"]["avg_time_seconds"]))
    lines.append("| Fastest: {:>17} {:>8.4f}s | Fastest: {:>15} {:>6.4f}s |".format(
        ts["z3"]["fastest_example"][:17], ts["z3"]["fastest_time"],
        ts["cvc5"]["fastest_example"][:15], ts["cvc5"]["fastest_time"]))
    lines.append("| Slowest: {:>17} {:>8.4f}s | Slowest: {:>15} {:>6.4f}s |".format(
        ts["z3"]["slowest_example"][:17], ts["z3"]["slowest_time"],
        ts["cvc5"]["slowest_example"][:15], ts["cvc5"]["slowest_time"]))
    lines.append("+" + "-" * 78 + "+")

    # Comparison Stats
    cs = results["comparison_stats"]
    lines.append("| {:^76} |".format("COMPARISON STATISTICS"))
    lines.append("+" + "-" * 78 + "+")
    lines.append("| Agreements: {:>5}   Disagreements: {:>5}   Avg Time Ratio: {:>6.2f}x {:>11} |".format(
        cs["agreements"], cs["disagreements"], cs["avg_time_ratio"], ""))
    lines.append("| Z3 Faster:  {:>5}   CVC5 Faster:   {:>5}   Ties: {:>5} {:>21} |".format(
        cs["z3_faster_count"], cs["cvc5_faster_count"], cs["ties"], ""))
    lines.append("+" + "-" * 78 + "+")

    # Results table header
    lines.append("| {:^76} |".format("EXAMPLE RESULTS"))
    lines.append("+" + "-" * 20 + "+" + "-" * 12 + "+" + "-" * 12 + "+" + "-" * 10 + "+" + "-" * 10 + "+" + "-" * 10 + "+")
    lines.append("| {:^18} | {:^10} | {:^10} | {:^8} | {:^8} | {:^8} |".format(
        "Example", "Z3 (s)", "CVC5 (s)", "Agree", "Faster", "Ratio"))
    lines.append("+" + "-" * 20 + "+" + "-" * 12 + "+" + "-" * 12 + "+" + "-" * 10 + "+" + "-" * 10 + "+" + "-" * 10 + "+")

    # Results rows
    for r in results["results"]:
        agree = "Yes" if r.get("agreement", False) else "NO"
        faster = r.get("faster_solver", "")[:8]
        ratio = r.get("time_ratio", 0)
        name = r["example_name"][:18]
        lines.append("| {:18} | {:>10.6f} | {:>10.6f} | {:^8} | {:^8} | {:>7.2f}x |".format(
            name,
            r["z3"]["time_seconds"],
            r["cvc5"]["time_seconds"],
            agree,
            faster,
            ratio,
        ))

    lines.append("+" + "-" * 20 + "+" + "-" * 12 + "+" + "-" * 12 + "+" + "-" * 10 + "+" + "-" * 10 + "+" + "-" * 10 + "+")

    return "\n".join(lines)


def format_as_markdown(results: Dict[str, Any]) -> str:
    """Format benchmark results as a Markdown report with tables.

    Args:
        results: Full benchmark results dictionary

    Returns:
        Markdown string suitable for writing to a .md file
    """
    lines = []
    meta = results["metadata"]
    ts = results["timing_summary"]
    cs = results["comparison_stats"]

    lines.append("# Dual-Solver Timing Comparison")
    lines.append("")
    curated_str = "Yes" if meta.get("curated", False) else "No"
    lines.append(f"- **Timestamp**: {meta['timestamp'][:19]}")
    lines.append(f"- **Z3 Version**: {meta['z3_version']}")
    lines.append(f"- **CVC5 Version**: {meta['cvc5_version']}")
    lines.append(f"- **Total Examples**: {meta['total_examples']}")
    lines.append(f"- **Curated**: {curated_str}")
    lines.append(f"- **Total Runtime**: {meta['total_runtime_seconds']:.2f}s")
    lines.append("")

    # Timing Summary
    lines.append("## Timing Summary")
    lines.append("")
    lines.append("| Metric | Z3 | CVC5 |")
    lines.append("|--------|---:|-----:|")
    lines.append("| Total Time | {:.4f}s | {:.4f}s |".format(
        ts["z3"]["total_time_seconds"], ts["cvc5"]["total_time_seconds"]))
    lines.append("| Avg Time | {:.6f}s | {:.6f}s |".format(
        ts["z3"]["avg_time_seconds"], ts["cvc5"]["avg_time_seconds"]))
    lines.append("| Fastest | {} ({:.4f}s) | {} ({:.4f}s) |".format(
        ts["z3"]["fastest_example"], ts["z3"]["fastest_time"],
        ts["cvc5"]["fastest_example"], ts["cvc5"]["fastest_time"]))
    lines.append("| Slowest | {} ({:.4f}s) | {} ({:.4f}s) |".format(
        ts["z3"]["slowest_example"], ts["z3"]["slowest_time"],
        ts["cvc5"]["slowest_example"], ts["cvc5"]["slowest_time"]))
    lines.append("")

    # Comparison Statistics
    lines.append("## Comparison Statistics")
    lines.append("")
    lines.append("| Metric | Value |")
    lines.append("|--------|------:|")
    lines.append(f"| Agreements | {cs['agreements']} |")
    lines.append(f"| Disagreements | {cs['disagreements']} |")
    lines.append(f"| Z3 Faster | {cs['z3_faster_count']} |")
    lines.append(f"| CVC5 Faster | {cs['cvc5_faster_count']} |")
    lines.append(f"| Ties | {cs['ties']} |")
    lines.append(f"| Avg Time Ratio | {cs['avg_time_ratio']:.2f}x |")
    lines.append("")

    # Example Results
    lines.append("## Example Results")
    lines.append("")
    lines.append("| Example | Z3 (s) | CVC5 (s) | Agree | Faster | Ratio |")
    lines.append("|---------|-------:|--------:|:-----:|:------:|------:|")
    for r in results["results"]:
        agree = "Yes" if r.get("agreement", False) else "**NO**"
        faster = r.get("faster_solver", "")
        ratio = r.get("time_ratio", 0)
        lines.append("| {} | {:.6f} | {:.6f} | {} | {} | {:.2f}x |".format(
            r["example_name"],
            r["z3"]["time_seconds"],
            r["cvc5"]["time_seconds"],
            agree,
            faster,
            ratio,
        ))
    lines.append("")

    # Disagreements section (if any)
    if results.get("disagreements"):
        lines.append("## Disagreements")
        lines.append("")
        lines.append("| Example | Subtheory | Z3 Result | CVC5 Result | Expected |")
        lines.append("|---------|-----------|:---------:|:-----------:|:--------:|")
        for d in results["disagreements"]:
            lines.append("| {} | {} | {} | {} | {} |".format(
                d["example_name"], d["subtheory"],
                d["z3_result"], d["cvc5_result"], d["expectation"]))
        lines.append("")

    return "\n".join(lines)


def compute_timing_comparison(
    results: List[Dict[str, Any]],
) -> tuple[Dict[str, Dict[str, Any]], Dict[str, Any]]:
    """Compute timing-focused summaries and comparison statistics.

    Args:
        results: List of result dictionaries with z3/cvc5 timing data

    Returns:
        Tuple of (timing_summary dict, comparison_stats dict)
    """
    # Initialize timing tracking
    timing_data = {
        "z3": {"times": [], "examples": []},
        "cvc5": {"times": [], "examples": []},
    }

    # Initialize comparison tracking
    agreements = 0
    disagreements = 0
    z3_faster = 0
    cvc5_faster = 0
    ties = 0
    time_ratios = []

    for r in results:
        # Collect timing data
        for solver in ["z3", "cvc5"]:
            if r.get(solver) and not r[solver].get("error"):
                timing_data[solver]["times"].append(r[solver]["time_seconds"])
                timing_data[solver]["examples"].append(r["example_name"])

        # Count agreements/disagreements
        if r.get("agreement", False):
            agreements += 1
        else:
            disagreements += 1

        # Count faster solver
        faster = r.get("faster_solver", "")
        if faster == "z3":
            z3_faster += 1
        elif faster == "cvc5":
            cvc5_faster += 1
        else:
            ties += 1

        # Collect time ratios (only if meaningful)
        ratio = r.get("time_ratio", 0)
        if ratio > 0:
            time_ratios.append(ratio)

    # Build timing summary for each solver
    timing_summary = {}
    for solver in ["z3", "cvc5"]:
        times = timing_data[solver]["times"]
        examples = timing_data[solver]["examples"]

        if times:
            fastest_idx = times.index(min(times))
            slowest_idx = times.index(max(times))
            timing_summary[solver] = {
                "total_time_seconds": round(sum(times), 4),
                "avg_time_seconds": round(sum(times) / len(times), 6),
                "fastest_example": examples[fastest_idx],
                "fastest_time": round(times[fastest_idx], 6),
                "slowest_example": examples[slowest_idx],
                "slowest_time": round(times[slowest_idx], 6),
            }
        else:
            timing_summary[solver] = {
                "total_time_seconds": 0.0,
                "avg_time_seconds": 0.0,
                "fastest_example": "",
                "fastest_time": 0.0,
                "slowest_example": "",
                "slowest_time": 0.0,
            }

    # Build comparison stats
    comparison_stats = {
        "agreements": agreements,
        "disagreements": disagreements,
        "z3_faster_count": z3_faster,
        "cvc5_faster_count": cvc5_faster,
        "ties": ties,
        "avg_time_ratio": round(sum(time_ratios) / len(time_ratios), 2) if time_ratios else 0.0,
    }

    return timing_summary, comparison_stats


def switch_solver(backend: str) -> None:
    """Switch to specified solver backend with full cache invalidation.

    This uses the three-step reset pattern from test_solver_comparison.py:
    1. Clear CLI backend first
    2. Reset registry caches
    3. Reset z3_shim cached module
    4. Reset AtomSort (so it's recreated for new backend)
    5. Set new backend

    Args:
        backend: Either 'z3' or 'cvc5'
    """
    from model_checker.syntactic.atoms import reset_atom_sort

    # Clear CLI backend first
    clear_cli_backend()
    # Reset registry caches
    reset_registry()
    # Reset z3_shim cached module
    z3_shim._reset_backend()
    # Reset AtomSort so it's recreated for the new backend
    reset_atom_sort()
    # Set new backend
    set_cli_backend(backend)


def get_required_subtheories(subtheory: str) -> List[str]:
    """Get the subtheory list required for a given subtheory's examples.

    Different subtheories have different dependency requirements:
    - extensional: just extensional
    - modal: extensional + modal
    - constitutive: extensional + modal + constitutive
    - counterfactual: extensional + modal + counterfactual
    - relevance: extensional + modal + constitutive + relevance

    Args:
        subtheory: Name of the target subtheory

    Returns:
        List of subtheory names to load
    """
    subtheory_deps = {
        "extensional": ["extensional"],
        "modal": ["extensional", "modal"],
        "constitutive": ["extensional", "modal", "constitutive"],
        "counterfactual": ["extensional", "modal", "counterfactual"],
        "relevance": ["extensional", "modal", "constitutive", "relevance"],
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


def get_curated_examples(
    subtheory_filter: Optional[str] = None,
) -> List[tuple[str, str, List[Any]]]:
    """Get curated examples for focused comparison testing.

    Returns a subset of 24 examples (4 per subtheory: 2 theorems + 2 countermodels)
    selected to provide coverage across all operators while keeping runtime low.

    Args:
        subtheory_filter: If provided, only return curated examples from this subtheory

    Returns:
        List of (subtheory, example_name, example_case) tuples
    """
    examples = []
    for subtheory, example_names in COMPARISON_EXAMPLES.items():
        if subtheory_filter and subtheory != subtheory_filter:
            continue
        subtheory_examples = all_subtheory_examples.get(subtheory, {})
        for name in example_names:
            if name in subtheory_examples:
                examples.append((subtheory, name, subtheory_examples[name]))
            else:
                print(f"Warning: curated example {name} not found in {subtheory}")
    return examples


def run_example_with_timing(
    example_case: List[Any],
    theory: Dict[str, Any],
    timeout: int = 30,
) -> tuple[Optional[bool], bool, float, Optional[str], bool]:
    """Run a single example and return result with timing.

    Args:
        example_case: [premises, conclusions, settings] tuple
        theory: The semantic theory dict
        timeout: Maximum seconds per example (0 = no timeout)

    Returns:
        Tuple of (result, passed, time_seconds, error_message, timed_out)
        - result: True=SAT (countermodel found), False=UNSAT (theorem), None=error
        - passed: Whether result matches expectation
        - time_seconds: Elapsed time
        - error_message: Error string if exception occurred
        - timed_out: Whether the example hit the timeout
    """
    start_time = time.perf_counter()
    error = None
    result = None
    timed_out = False

    # Set up alarm-based timeout (Linux/macOS only)
    old_handler = None
    if timeout > 0:
        old_handler = signal.signal(signal.SIGALRM, _timeout_handler)
        signal.alarm(timeout)

    try:
        mock_module = create_test_module(theory)
        example = BuildExample(mock_module, theory, example_case)

        # Check if a model was found (countermodel exists)
        # z3_model_status is True/truthy when SAT (countermodel found)
        # z3_model_status is False/None when UNSAT (no countermodel - theorem)
        result = bool(example.model_structure.z3_model_status)

    except ExampleTimeout:
        error = f"timeout ({timeout}s)"
        result = None
        timed_out = True

    except Exception as e:
        error = str(e)
        result = None

    finally:
        # Cancel any pending alarm and restore old handler
        if timeout > 0:
            signal.alarm(0)
            if old_handler is not None:
                signal.signal(signal.SIGALRM, old_handler)

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

    return result, passed, elapsed, error, timed_out


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
    timeout: int = 30,
    curated: bool = False,
) -> Dict[str, Any]:
    """Run all benchmarks and return structured results.

    Args:
        subtheory_filter: If provided, only run examples from this subtheory
        verbose: If True, print per-example output
        timeout: Maximum seconds per example per solver (0 = no timeout)
        curated: If True, run only curated 24 examples instead of all examples

    Returns:
        Dictionary with metadata, summary, by_subtheory, results, and disagreements
    """
    start_time = time.perf_counter()

    # Collect examples (curated or all)
    if curated:
        examples = get_curated_examples(subtheory_filter)
    else:
        examples = flatten_examples(subtheory_filter)
    total_examples = len(examples)

    timeout_label = f" (timeout: {timeout}s)" if timeout > 0 else ""
    curated_label = " [curated]" if curated else ""
    print(f"Running {total_examples}{curated_label} examples against z3 and cvc5{timeout_label}...")
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
            "timeouts": 0,
            "times": [],
        },
        "cvc5": {
            "passed": 0,
            "failed": 0,
            "errors": 0,
            "timeouts": 0,
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
            result, passed, elapsed, error, timed_out = run_example_with_timing(
                example_case, theory, timeout=timeout
            )

            solver_result = {
                "result": result,
                "passed": passed,
                "time_seconds": round(elapsed, 6),
                "error": error,
                "timed_out": timed_out,
            }
            solver_results[solver] = solver_result
            result_entry[solver] = solver_result

            # Update statistics
            solver_stats[solver]["times"].append(elapsed)
            if timed_out:
                solver_stats[solver]["timeouts"] += 1
                subtheory_stats[subtheory][solver]["errors"] += 1
            elif error:
                solver_stats[solver]["errors"] += 1
                subtheory_stats[subtheory][solver]["errors"] += 1
            elif passed:
                solver_stats[solver]["passed"] += 1
                subtheory_stats[subtheory][solver]["passed"] += 1
            else:
                solver_stats[solver]["failed"] += 1
                subtheory_stats[subtheory][solver]["failed"] += 1
            subtheory_stats[subtheory][solver]["time"] += elapsed

        # Add timing comparison fields
        z3_time = solver_results["z3"]["time_seconds"]
        cvc5_time = solver_results["cvc5"]["time_seconds"]
        if z3_time < cvc5_time:
            faster_solver = "z3"
            time_ratio = round(cvc5_time / z3_time, 2) if z3_time > 0 else 0.0
        elif cvc5_time < z3_time:
            faster_solver = "cvc5"
            time_ratio = round(z3_time / cvc5_time, 2) if cvc5_time > 0 else 0.0
        else:
            faster_solver = "tie"
            time_ratio = 1.0

        z3_result = solver_results["z3"]["result"]
        cvc5_result = solver_results["cvc5"]["result"]
        result_entry["agreement"] = z3_result == cvc5_result
        result_entry["faster_solver"] = faster_solver
        result_entry["time_ratio"] = time_ratio

        results.append(result_entry)

        # Check for disagreement
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
        z3_error = solver_results["z3"]["error"]
        cvc5_error = solver_results["cvc5"]["error"]
        z3_timeout = solver_results["z3"]["timed_out"]
        cvc5_timeout = solver_results["cvc5"]["timed_out"]
        if verbose:
            z3_status = "PASS" if solver_results["z3"]["passed"] else "FAIL"
            cvc5_status = "PASS" if solver_results["cvc5"]["passed"] else "FAIL"
            z3_err = f" (error: {z3_error})" if z3_error else ""
            cvc5_err = f" (error: {cvc5_error})" if cvc5_error else ""
            disagree = " [DISAGREE]" if z3_result != cvc5_result else ""
            print(
                f"  [{idx}/{total_examples}] {name}: "
                f"z3={z3_status}{z3_err} cvc5={cvc5_status}{cvc5_err}{disagree}"
            )
        else:
            # Print timeouts and errors immediately even in non-verbose mode
            if z3_timeout or cvc5_timeout:
                parts = []
                if z3_timeout:
                    parts.append(f"z3: {timeout}s")
                if cvc5_timeout:
                    parts.append(f"cvc5: {timeout}s")
                print(f"  TIMEOUT [{idx}/{total_examples}] {name}: {'; '.join(parts)}")
            elif z3_error or cvc5_error:
                errs = []
                if z3_error:
                    errs.append(f"z3: {z3_error}")
                if cvc5_error:
                    errs.append(f"cvc5: {cvc5_error}")
                print(f"  ERROR [{idx}/{total_examples}] {name}: {'; '.join(errs)}")
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
            "timeouts": stats["timeouts"],
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

    # Compute timing comparison data
    timing_summary, comparison_stats = compute_timing_comparison(results)

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
            "curated": curated,
        },
        "summary": summary,
        "timing_summary": timing_summary,
        "comparison_stats": comparison_stats,
        "by_subtheory": by_subtheory,
        "results": results,
        "disagreements": disagreements,
    }

    # Print summary
    print()
    print("=" * 60)
    print("BENCHMARK SUMMARY")
    print("=" * 60)
    for solver_label, solver_key in [("Z3  ", "z3"), ("CVC5", "cvc5")]:
        s = summary[solver_key]
        timeout_part = f", {s['timeouts']} timeouts" if s['timeouts'] else ""
        print(
            f"{solver_label}: {s['passed']}/{s['total_examples']} passed, "
            f"{s['errors']} errors{timeout_part}, "
            f"avg {s['avg_time_seconds']:.4f}s, "
            f"total {s['total_time_seconds']:.2f}s"
        )

    # Show unique errors (deduplicated by message)
    z3_errors = {}
    cvc5_errors = {}
    for r in results:
        if r["z3"].get("error"):
            msg = r["z3"]["error"]
            z3_errors.setdefault(msg, []).append(r["example_name"])
        if r["cvc5"].get("error"):
            msg = r["cvc5"]["error"]
            cvc5_errors.setdefault(msg, []).append(r["example_name"])

    if z3_errors or cvc5_errors:
        print(f"\nErrors:")
        for solver_name, error_map in [("z3", z3_errors), ("cvc5", cvc5_errors)]:
            for msg, examples_list in error_map.items():
                count = len(examples_list)
                sample = ", ".join(examples_list[:3])
                suffix = f", ... ({count} total)" if count > 3 else ""
                print(f"  {solver_name}: {msg}")
                print(f"    affected: {sample}{suffix}")

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
        ],
        help="Run only examples from this subtheory",
    )
    parser.add_argument(
        "--verbose",
        "-v",
        action="store_true",
        help="Show detailed per-example output",
    )
    parser.add_argument(
        "--timeout",
        "-t",
        type=int,
        default=30,
        help="Timeout per example per solver in seconds (default: 30, 0 = no timeout)",
    )
    parser.add_argument(
        "--curated",
        "-c",
        action="store_true",
        help="Run only curated 24 examples (4 per subtheory) instead of all examples",
    )
    parser.add_argument(
        "--format",
        "-f",
        choices=["full", "timing"],
        default="full",
        help="Output format: 'full' for all data, 'timing' for timing-focused output",
    )
    parser.add_argument(
        "--table",
        action="store_true",
        help="Print ASCII table to console (in addition to JSON output)",
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
        timeout=args.timeout,
        curated=args.curated,
    )

    # Prepare output based on format
    if args.format == "timing":
        # Simplified timing-focused output
        output = {
            "metadata": results["metadata"],
            "timing_summary": results["timing_summary"],
            "comparison_stats": results["comparison_stats"],
            "results": [
                {
                    "subtheory": r["subtheory"],
                    "example": r["example_name"],
                    "z3_time": r["z3"]["time_seconds"],
                    "cvc5_time": r["cvc5"]["time_seconds"],
                    "agreement": r["agreement"],
                    "faster_solver": r["faster_solver"],
                    "time_ratio": r["time_ratio"],
                }
                for r in results["results"]
            ],
        }
    else:
        output = results

    # Print ASCII table if requested
    if args.table:
        print()
        print(format_as_table(results))

    # Write JSON output
    with open(args.output, "w") as f:
        json.dump(output, f, indent=2)

    # Write Markdown output
    md_output_path = args.output.rsplit(".", 1)[0] + ".md"
    with open(md_output_path, "w") as f:
        f.write(format_as_markdown(results))

    print(f"\nResults written to {args.output} and {md_output_path}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
