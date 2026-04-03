#!/usr/bin/env python3
"""Benchmark comparing finitary vs native quantifier implementations.

This script compares three quantifier configurations:
1. finitary+Z3: Explicit enumeration (current default) with Z3 solver
2. native+Z3: Z3's native ForAll/Exists quantifiers
3. native+CVC5: CVC5's native quantifiers

Usage:
    ./quantifier_benchmark.py                    # Run all 20 examples, all modes
    ./quantifier_benchmark.py --quick            # Run 5 examples for quick test
    ./quantifier_benchmark.py --modes finitary,z3-native  # Specific modes
    ./quantifier_benchmark.py --timeout 60       # Custom timeout per example
    ./quantifier_benchmark.py --format table     # ASCII table output
    ./quantifier_benchmark.py --output results.json  # Custom output file

For full documentation, see: Task 82 research reports
"""

import argparse
import json
import os
import platform
import signal
import sys
import time
from dataclasses import dataclass, field, asdict
from datetime import datetime
from typing import Any, Dict, List, Optional, Literal

# Ensure local src is prioritized
src_path = os.path.abspath(os.path.join(os.path.dirname(__file__), '..', 'src'))
sys.path.insert(0, src_path)


# Selected counterfactual examples: 10 theorems + 10 countermodels
# Based on research report 02_toggleable-quantifier-design.md
SELECTED_EXAMPLES = {
    # Theorems (UNSAT expected)
    "CF_TH_1": {"subtheory": "counterfactual", "description": "Counterfactual Identity", "expected": "unsat"},
    "CF_TH_2": {"subtheory": "counterfactual", "description": "Counterfactual Modus Ponens", "expected": "unsat"},
    "CF_TH_3": {"subtheory": "counterfactual", "description": "Weakened Transitivity", "expected": "unsat"},
    "CF_TH_4": {"subtheory": "counterfactual", "description": "Antecedent Disjunction to Conjunction", "expected": "unsat"},
    "CF_TH_5": {"subtheory": "counterfactual", "description": "Simplification of Disjunctive Antecedent", "expected": "unsat"},
    "CF_TH_6": {"subtheory": "counterfactual", "description": "Double Simplification", "expected": "unsat"},
    "CF_TH_8": {"subtheory": "counterfactual", "description": "Consequent Weakening", "expected": "unsat"},
    "CF_TH_9": {"subtheory": "counterfactual", "description": "Conjunction Introduction", "expected": "unsat"},
    "CF_TH_10": {"subtheory": "counterfactual", "description": "Might Factivity", "expected": "unsat"},
    "CF_TH_11": {"subtheory": "counterfactual", "description": "Definition of Nec", "expected": "unsat"},
    # Countermodels (SAT expected)
    "CF_CM_1": {"subtheory": "counterfactual", "description": "Antecedent Strengthening", "expected": "sat"},
    "CF_CM_5": {"subtheory": "counterfactual", "description": "Double Antecedent Strengthening", "expected": "sat"},
    "CF_CM_7": {"subtheory": "counterfactual", "description": "Contraposition", "expected": "sat"},
    "CF_CM_10": {"subtheory": "counterfactual", "description": "Transitivity", "expected": "sat"},
    "CF_CM_15": {"subtheory": "counterfactual", "description": "Excluded Middle", "expected": "sat"},
    "CF_CM_16": {"subtheory": "counterfactual", "description": "Simplification of Disjunctive Consequent", "expected": "sat"},
    "CF_CM_17": {"subtheory": "counterfactual", "description": "Introduction of Disjunctive Antecedent", "expected": "sat"},
    "CF_CM_18": {"subtheory": "counterfactual", "description": "Must Factivity", "expected": "sat"},
    "CF_CM_19": {"subtheory": "counterfactual", "description": "Exportation", "expected": "sat"},
    "CF_CM_21": {"subtheory": "counterfactual", "description": "Negation Distribution", "expected": "sat"},
}

# Quick mode subset (5 examples)
QUICK_EXAMPLES = ["CF_TH_1", "CF_TH_2", "CF_CM_1", "CF_CM_7", "CF_CM_10"]


class ExampleTimeout(Exception):
    """Raised when an example exceeds its time limit."""
    pass


def _timeout_handler(signum, frame):
    raise ExampleTimeout("Example timed out")


@dataclass
class ModeResult:
    """Result from running an example with a specific mode."""
    result: Optional[str]  # "sat", "unsat", "unknown", or None (error)
    time_seconds: float
    error: Optional[str] = None
    timed_out: bool = False


@dataclass
class ExampleResult:
    """Combined results for an example across all modes."""
    example_name: str
    description: str
    expected: str  # "sat" or "unsat"
    finitary: Optional[ModeResult] = None
    z3_native: Optional[ModeResult] = None
    cvc5_native: Optional[ModeResult] = None


@dataclass
class ModeSummary:
    """Summary statistics for a single mode."""
    total: int = 0
    sat: int = 0
    unsat: int = 0
    unknown: int = 0
    errors: int = 0
    timeouts: int = 0
    total_time: float = 0.0
    avg_time: float = 0.0


@dataclass
class BenchmarkOutput:
    """Complete benchmark output structure."""
    metadata: Dict[str, Any]
    summary: Dict[str, Any]
    timing_summary: Dict[str, Any]
    comparison_stats: Dict[str, Any]
    results: List[Dict[str, Any]]
    disagreements: List[Dict[str, Any]]


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
        if isinstance(version, bytes):
            version = version.decode("utf-8")
        return str(version)
    except Exception:
        return "unknown"


def configure_mode(mode: str) -> None:
    """Configure solver backend and quantifier mode.

    Args:
        mode: One of "finitary", "z3-native", "cvc5-native"
    """
    from model_checker.solver.registry import set_cli_backend, clear_cli_backend, reset_registry
    from model_checker.solver.lifecycle import invalidate_all_caches
    from model_checker.utils.z3_helpers import set_quantifier_mode
    from model_checker import z3_shim
    from model_checker.syntactic.atoms import reset_atom_sort

    # Full cache invalidation
    clear_cli_backend()
    reset_registry()
    z3_shim._reset_backend()
    reset_atom_sort()
    invalidate_all_caches()

    if mode == "finitary":
        set_cli_backend("z3")
        set_quantifier_mode("finitary")
    elif mode == "z3-native":
        set_cli_backend("z3")
        set_quantifier_mode("native")
    elif mode == "cvc5-native":
        set_cli_backend("cvc5")
        set_quantifier_mode("native")
    else:
        raise ValueError(f"Unknown mode: {mode}")


def run_single_example(
    example_name: str,
    example_case: List[Any],
    theory: Dict[str, Any],
    timeout: int = 30,
) -> ModeResult:
    """Run a single example and return result with timing.

    Args:
        example_name: Name of the example (e.g., "CF_TH_1")
        example_case: [premises, conclusions, settings] tuple
        theory: The semantic theory dict
        timeout: Maximum seconds per example (0 = no timeout)

    Returns:
        ModeResult with result, timing, and error info
    """
    from model_checker.builder.example import BuildExample
    from types import SimpleNamespace
    from unittest.mock import Mock

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
        # Create mock module for the example
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

        example = BuildExample(mock_module, theory, example_case)

        # Check if a model was found
        # z3_model_status is truthy when SAT (countermodel found)
        # z3_model_status is falsy when UNSAT (no countermodel - theorem)
        if example.model_structure.z3_model_status:
            result = "sat"
        else:
            result = "unsat"

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

    return ModeResult(
        result=result,
        time_seconds=round(elapsed, 6),
        error=error,
        timed_out=timed_out,
    )


def get_theory_and_examples() -> tuple[Dict[str, Any], Dict[str, List[Any]]]:
    """Get the logos theory and counterfactual examples.

    Returns:
        Tuple of (theory dict, examples dict)
    """
    from model_checker.theory_lib.logos import get_theory
    from model_checker.theory_lib.logos.examples import all_subtheory_examples

    # Get theory with required subtheories for counterfactual examples
    subtheories = ["extensional", "modal", "counterfactual"]
    theory = get_theory(subtheories)

    # Get counterfactual examples
    cf_examples = all_subtheory_examples.get("counterfactual", {})

    return theory, cf_examples


def compute_summary(results: List[ExampleResult], modes: List[str]) -> Dict[str, ModeSummary]:
    """Compute summary statistics for each mode.

    Args:
        results: List of ExampleResult objects
        modes: List of mode names to summarize

    Returns:
        Dict mapping mode name to ModeSummary
    """
    summaries = {}

    for mode in modes:
        summary = ModeSummary()
        times = []

        for r in results:
            mode_result = getattr(r, mode.replace("-", "_"), None)
            if mode_result is None:
                continue

            summary.total += 1

            if mode_result.error:
                if mode_result.timed_out:
                    summary.timeouts += 1
                else:
                    summary.errors += 1
            elif mode_result.result == "sat":
                summary.sat += 1
                times.append(mode_result.time_seconds)
            elif mode_result.result == "unsat":
                summary.unsat += 1
                times.append(mode_result.time_seconds)
            else:
                summary.unknown += 1

        if times:
            summary.total_time = round(sum(times), 4)
            summary.avg_time = round(sum(times) / len(times), 6)

        summaries[mode] = summary

    return summaries


def compute_timing_summary(results: List[ExampleResult], modes: List[str]) -> Dict[str, Dict[str, Any]]:
    """Compute timing-focused summary for each mode.

    Args:
        results: List of ExampleResult objects
        modes: List of mode names

    Returns:
        Dict mapping mode name to timing stats
    """
    timing = {}

    for mode in modes:
        times = []
        examples = []

        for r in results:
            mode_result = getattr(r, mode.replace("-", "_"), None)
            if mode_result and mode_result.result and not mode_result.error:
                times.append(mode_result.time_seconds)
                examples.append(r.example_name)

        if times:
            fastest_idx = times.index(min(times))
            slowest_idx = times.index(max(times))
            timing[mode] = {
                "total_time_seconds": round(sum(times), 4),
                "avg_time_seconds": round(sum(times) / len(times), 6),
                "fastest_example": examples[fastest_idx],
                "fastest_time": round(times[fastest_idx], 6),
                "slowest_example": examples[slowest_idx],
                "slowest_time": round(times[slowest_idx], 6),
            }
        else:
            timing[mode] = {
                "total_time_seconds": 0.0,
                "avg_time_seconds": 0.0,
                "fastest_example": "",
                "fastest_time": 0.0,
                "slowest_example": "",
                "slowest_time": 0.0,
            }

    return timing


def compute_comparison_stats(results: List[ExampleResult], modes: List[str]) -> Dict[str, Any]:
    """Compute comparison statistics between modes.

    Args:
        results: List of ExampleResult objects
        modes: List of mode names

    Returns:
        Dict with comparison statistics
    """
    stats = {
        "native_vs_finitary_z3": {"native_faster": 0, "finitary_faster": 0, "ratio": 0.0},
        "z3_vs_cvc5_native": {"z3_faster": 0, "cvc5_faster": 0, "ratio": 0.0},
        "result_agreements": 0,
        "result_disagreements": 0,
    }

    native_ratios = []
    cvc5_ratios = []

    for r in results:
        fin = r.finitary
        z3n = r.z3_native
        cvc5n = r.cvc5_native

        # Check result agreement across modes
        results_set = set()
        for mode_result in [fin, z3n, cvc5n]:
            if mode_result and mode_result.result:
                results_set.add(mode_result.result)

        if len(results_set) <= 1:
            stats["result_agreements"] += 1
        else:
            stats["result_disagreements"] += 1

        # Compare finitary vs z3-native timing
        if fin and z3n and fin.result and z3n.result and not fin.error and not z3n.error:
            if z3n.time_seconds < fin.time_seconds:
                stats["native_vs_finitary_z3"]["native_faster"] += 1
                native_ratios.append(fin.time_seconds / z3n.time_seconds)
            else:
                stats["native_vs_finitary_z3"]["finitary_faster"] += 1
                if z3n.time_seconds > 0:
                    native_ratios.append(fin.time_seconds / z3n.time_seconds)

        # Compare z3-native vs cvc5-native timing
        if z3n and cvc5n and z3n.result and cvc5n.result and not z3n.error and not cvc5n.error:
            if z3n.time_seconds < cvc5n.time_seconds:
                stats["z3_vs_cvc5_native"]["z3_faster"] += 1
                if cvc5n.time_seconds > 0:
                    cvc5_ratios.append(cvc5n.time_seconds / z3n.time_seconds)
            else:
                stats["z3_vs_cvc5_native"]["cvc5_faster"] += 1
                if z3n.time_seconds > 0:
                    cvc5_ratios.append(cvc5n.time_seconds / z3n.time_seconds)

    if native_ratios:
        stats["native_vs_finitary_z3"]["ratio"] = round(sum(native_ratios) / len(native_ratios), 2)
    if cvc5_ratios:
        stats["z3_vs_cvc5_native"]["ratio"] = round(sum(cvc5_ratios) / len(cvc5_ratios), 2)

    return stats


def find_disagreements(results: List[ExampleResult]) -> List[Dict[str, Any]]:
    """Find examples where modes disagree on results.

    Args:
        results: List of ExampleResult objects

    Returns:
        List of disagreement records
    """
    disagreements = []

    for r in results:
        results_map = {}
        for mode, mode_result in [("finitary", r.finitary), ("z3_native", r.z3_native), ("cvc5_native", r.cvc5_native)]:
            if mode_result and mode_result.result:
                results_map[mode] = mode_result.result

        unique_results = set(results_map.values())
        if len(unique_results) > 1:
            disagreements.append({
                "example_name": r.example_name,
                "expected": r.expected,
                "finitary_result": results_map.get("finitary"),
                "z3_native_result": results_map.get("z3_native"),
                "cvc5_native_result": results_map.get("cvc5_native"),
            })

    return disagreements


def format_as_table(output: Dict[str, Any]) -> str:
    """Format benchmark results as ASCII table.

    Args:
        output: Full benchmark output dict

    Returns:
        ASCII table string
    """
    lines = []

    # Header
    lines.append("+" + "-" * 90 + "+")
    lines.append("| {:^88} |".format("QUANTIFIER BENCHMARK: FINITARY vs NATIVE"))
    lines.append("+" + "-" * 90 + "+")

    # Metadata
    meta = output["metadata"]
    lines.append("| {:22} {:65} |".format("Timestamp:", meta["timestamp"][:19]))
    lines.append("| {:22} {:65} |".format("Z3 Version:", meta["z3_version"]))
    lines.append("| {:22} {:65} |".format("CVC5 Version:", meta["cvc5_version"]))
    lines.append("| {:22} {:65} |".format("Total Examples:", str(meta["total_tests"])))
    lines.append("+" + "-" * 90 + "+")

    # Timing Summary
    lines.append("| {:^88} |".format("TIMING SUMMARY"))
    lines.append("+" + "-" * 30 + "+" + "-" * 29 + "+" + "-" * 28 + "+")
    lines.append("| {:^28} | {:^27} | {:^26} |".format("Finitary+Z3", "Native+Z3", "Native+CVC5"))
    lines.append("+" + "-" * 30 + "+" + "-" * 29 + "+" + "-" * 28 + "+")

    ts = output["timing_summary"]
    lines.append("| Total: {:>20.4f}s | Total: {:>18.4f}s | Total: {:>17.4f}s |".format(
        ts.get("finitary", {}).get("total_time_seconds", 0),
        ts.get("z3-native", {}).get("total_time_seconds", 0),
        ts.get("cvc5-native", {}).get("total_time_seconds", 0)))
    lines.append("| Avg:   {:>20.6f}s | Avg:   {:>18.6f}s | Avg:   {:>17.6f}s |".format(
        ts.get("finitary", {}).get("avg_time_seconds", 0),
        ts.get("z3-native", {}).get("avg_time_seconds", 0),
        ts.get("cvc5-native", {}).get("avg_time_seconds", 0)))
    lines.append("+" + "-" * 90 + "+")

    # Comparison Stats
    cs = output["comparison_stats"]
    lines.append("| {:^88} |".format("COMPARISON STATISTICS"))
    lines.append("+" + "-" * 90 + "+")
    lines.append("| Result Agreements: {:>5}     Disagreements: {:>5} {:>44} |".format(
        cs["result_agreements"], cs["result_disagreements"], ""))
    native_vs_fin = cs.get("native_vs_finitary_z3", {})
    lines.append("| Native vs Finitary (Z3): Native faster {:>3}, Finitary faster {:>3}, Ratio: {:>5.2f}x {:>5} |".format(
        native_vs_fin.get("native_faster", 0),
        native_vs_fin.get("finitary_faster", 0),
        native_vs_fin.get("ratio", 0),
        ""))
    lines.append("+" + "-" * 90 + "+")

    # Results table
    lines.append("| {:^88} |".format("EXAMPLE RESULTS"))
    lines.append("+" + "-" * 14 + "+" + "-" * 12 + "+" + "-" * 12 + "+" + "-" * 12 + "+" + "-" * 10 + "+" + "-" * 8 + "+" + "-" * 18 + "+")
    lines.append("| {:^12} | {:^10} | {:^10} | {:^10} | {:^8} | {:^6} | {:^16} |".format(
        "Example", "Finitary", "Z3-Native", "CVC5-Native", "Expected", "Agree", "Fastest"))
    lines.append("+" + "-" * 14 + "+" + "-" * 12 + "+" + "-" * 12 + "+" + "-" * 12 + "+" + "-" * 10 + "+" + "-" * 8 + "+" + "-" * 18 + "+")

    for r in output["results"]:
        fin_time = r.get("finitary", {}).get("time_seconds", 0)
        z3n_time = r.get("z3_native", {}).get("time_seconds", 0)
        cvc5n_time = r.get("cvc5_native", {}).get("time_seconds", 0)

        # Determine fastest
        times = {"finitary": fin_time, "z3-native": z3n_time, "cvc5-native": cvc5n_time}
        valid_times = {k: v for k, v in times.items() if v > 0}
        fastest = min(valid_times, key=valid_times.get) if valid_times else ""

        # Check agreement
        results_set = set()
        for mode in ["finitary", "z3_native", "cvc5_native"]:
            if mode in r and r[mode].get("result"):
                results_set.add(r[mode]["result"])
        agree = "Yes" if len(results_set) <= 1 else "NO"

        lines.append("| {:12} | {:>10.6f} | {:>10.6f} | {:>10.6f} | {:^8} | {:^6} | {:^16} |".format(
            r["example_name"][:12],
            fin_time,
            z3n_time,
            cvc5n_time,
            r["expected"],
            agree,
            fastest[:16]))

    lines.append("+" + "-" * 14 + "+" + "-" * 12 + "+" + "-" * 12 + "+" + "-" * 12 + "+" + "-" * 10 + "+" + "-" * 8 + "+" + "-" * 18 + "+")

    return "\n".join(lines)


def format_as_markdown(output: Dict[str, Any]) -> str:
    """Format benchmark results as Markdown.

    Args:
        output: Full benchmark output dict

    Returns:
        Markdown string
    """
    lines = []
    meta = output["metadata"]
    ts = output["timing_summary"]
    cs = output["comparison_stats"]

    lines.append("# Quantifier Benchmark: Finitary vs Native")
    lines.append("")
    lines.append("## Metadata")
    lines.append("")
    lines.append(f"- **Timestamp**: {meta['timestamp'][:19]}")
    lines.append(f"- **Z3 Version**: {meta['z3_version']}")
    lines.append(f"- **CVC5 Version**: {meta['cvc5_version']}")
    lines.append(f"- **Total Examples**: {meta['total_tests']}")
    lines.append(f"- **Total Runtime**: {meta['total_runtime_seconds']:.2f}s")
    lines.append("")

    # Timing Summary
    lines.append("## Timing Summary")
    lines.append("")
    lines.append("| Metric | Finitary+Z3 | Native+Z3 | Native+CVC5 |")
    lines.append("|--------|------------:|----------:|------------:|")
    lines.append("| Total Time | {:.4f}s | {:.4f}s | {:.4f}s |".format(
        ts.get("finitary", {}).get("total_time_seconds", 0),
        ts.get("z3-native", {}).get("total_time_seconds", 0),
        ts.get("cvc5-native", {}).get("total_time_seconds", 0)))
    lines.append("| Avg Time | {:.6f}s | {:.6f}s | {:.6f}s |".format(
        ts.get("finitary", {}).get("avg_time_seconds", 0),
        ts.get("z3-native", {}).get("avg_time_seconds", 0),
        ts.get("cvc5-native", {}).get("avg_time_seconds", 0)))
    lines.append("")

    # Comparison Statistics
    lines.append("## Comparison Statistics")
    lines.append("")
    lines.append("| Metric | Value |")
    lines.append("|--------|------:|")
    lines.append(f"| Result Agreements | {cs['result_agreements']} |")
    lines.append(f"| Result Disagreements | {cs['result_disagreements']} |")
    native_vs_fin = cs.get("native_vs_finitary_z3", {})
    lines.append(f"| Native Faster (Z3) | {native_vs_fin.get('native_faster', 0)} |")
    lines.append(f"| Finitary Faster (Z3) | {native_vs_fin.get('finitary_faster', 0)} |")
    lines.append(f"| Avg Time Ratio | {native_vs_fin.get('ratio', 0):.2f}x |")
    lines.append("")

    # Example Results
    lines.append("## Example Results")
    lines.append("")
    lines.append("| Example | Finitary (s) | Z3-Native (s) | CVC5-Native (s) | Expected | Agree |")
    lines.append("|---------|-------------:|--------------:|----------------:|:--------:|:-----:|")
    for r in output["results"]:
        fin_time = r.get("finitary", {}).get("time_seconds", 0)
        z3n_time = r.get("z3_native", {}).get("time_seconds", 0)
        cvc5n_time = r.get("cvc5_native", {}).get("time_seconds", 0)

        results_set = set()
        for mode in ["finitary", "z3_native", "cvc5_native"]:
            if mode in r and r[mode].get("result"):
                results_set.add(r[mode]["result"])
        agree = "Yes" if len(results_set) <= 1 else "**NO**"

        lines.append("| {} | {:.6f} | {:.6f} | {:.6f} | {} | {} |".format(
            r["example_name"],
            fin_time,
            z3n_time,
            cvc5n_time,
            r["expected"],
            agree))
    lines.append("")

    # Disagreements
    if output.get("disagreements"):
        lines.append("## Disagreements")
        lines.append("")
        lines.append("| Example | Expected | Finitary | Z3-Native | CVC5-Native |")
        lines.append("|---------|:--------:|:--------:|:---------:|:-----------:|")
        for d in output["disagreements"]:
            lines.append("| {} | {} | {} | {} | {} |".format(
                d["example_name"],
                d["expected"],
                d.get("finitary_result", "-"),
                d.get("z3_native_result", "-"),
                d.get("cvc5_native_result", "-")))
        lines.append("")

    return "\n".join(lines)


def run_benchmark(
    example_names: List[str],
    modes: List[str],
    timeout: int = 30,
    verbose: bool = False,
) -> Dict[str, Any]:
    """Run the benchmark across all examples and modes.

    Args:
        example_names: List of example names to run
        modes: List of modes to test
        timeout: Timeout per example in seconds
        verbose: Print progress

    Returns:
        Full benchmark output dict
    """
    start_time = time.perf_counter()
    results = []

    for example_name in example_names:
        if example_name not in SELECTED_EXAMPLES:
            print(f"Warning: {example_name} not in selected examples, skipping")
            continue

        example_info = SELECTED_EXAMPLES[example_name]
        example_result = ExampleResult(
            example_name=example_name,
            description=example_info["description"],
            expected=example_info["expected"],
        )

        for mode in modes:
            if verbose:
                print(f"Running {example_name} with {mode}...", end=" ", flush=True)

            # Configure mode
            configure_mode(mode)

            # Get fresh theory and examples (after mode switch)
            theory, cf_examples = get_theory_and_examples()

            if example_name not in cf_examples:
                print(f"Warning: {example_name} not found in counterfactual examples")
                continue

            example_case = cf_examples[example_name]

            # Run example
            mode_result = run_single_example(
                example_name, example_case, theory, timeout
            )

            if verbose:
                if mode_result.error:
                    print(f"ERROR: {mode_result.error}")
                else:
                    print(f"{mode_result.result} ({mode_result.time_seconds:.4f}s)")

            # Store result by mode
            mode_attr = mode.replace("-", "_")
            setattr(example_result, mode_attr, mode_result)

        results.append(example_result)

    total_runtime = time.perf_counter() - start_time

    # Compute summaries
    summaries = compute_summary(results, modes)
    timing_summary = compute_timing_summary(results, modes)
    comparison_stats = compute_comparison_stats(results, modes)
    disagreements = find_disagreements(results)

    # Build output structure
    output = {
        "metadata": {
            "timestamp": datetime.now().isoformat(),
            "z3_version": get_z3_version(),
            "cvc5_version": get_cvc5_version(),
            "platform": platform.platform(),
            "python_version": platform.python_version(),
            "total_tests": len(results),
            "total_runtime_seconds": round(total_runtime, 2),
            "modes_tested": modes,
            "description": "Z3 vs CVC5 Primitive Quantifier Benchmark",
        },
        "summary": {mode: asdict(summaries[mode]) for mode in modes},
        "timing_summary": timing_summary,
        "comparison_stats": comparison_stats,
        "results": [
            {
                "example_name": r.example_name,
                "description": r.description,
                "expected": r.expected,
                "finitary": asdict(r.finitary) if r.finitary else None,
                "z3_native": asdict(r.z3_native) if r.z3_native else None,
                "cvc5_native": asdict(r.cvc5_native) if r.cvc5_native else None,
            }
            for r in results
        ],
        "disagreements": disagreements,
    }

    return output


def main():
    """Main entry point."""
    parser = argparse.ArgumentParser(
        description="Benchmark finitary vs native quantifier implementations"
    )
    parser.add_argument(
        "--quick", "-q",
        action="store_true",
        help="Run quick test with 5 examples"
    )
    parser.add_argument(
        "--modes", "-m",
        type=str,
        default="finitary,z3-native,cvc5-native",
        help="Comma-separated list of modes to test (default: all three)"
    )
    parser.add_argument(
        "--timeout", "-t",
        type=int,
        default=30,
        help="Timeout per example in seconds (default: 30)"
    )
    parser.add_argument(
        "--format", "-f",
        choices=["json", "table", "markdown"],
        default="json",
        help="Output format (default: json)"
    )
    parser.add_argument(
        "--output", "-o",
        type=str,
        default=None,
        help="Output file path (default: quantifier_output.json)"
    )
    parser.add_argument(
        "--verbose", "-v",
        action="store_true",
        help="Print progress during benchmark"
    )

    args = parser.parse_args()

    # Parse modes
    modes = [m.strip() for m in args.modes.split(",")]
    valid_modes = {"finitary", "z3-native", "cvc5-native"}
    for mode in modes:
        if mode not in valid_modes:
            print(f"Error: Invalid mode '{mode}'. Valid modes: {valid_modes}")
            return 1

    # Select examples
    if args.quick:
        example_names = QUICK_EXAMPLES
    else:
        example_names = list(SELECTED_EXAMPLES.keys())

    if args.verbose:
        print(f"Running benchmark with {len(example_names)} examples, modes: {modes}")
        print(f"Timeout: {args.timeout}s per example")
        print()

    # Run benchmark
    output = run_benchmark(
        example_names=example_names,
        modes=modes,
        timeout=args.timeout,
        verbose=args.verbose,
    )

    # Format output
    if args.format == "table":
        formatted = format_as_table(output)
        print(formatted)
    elif args.format == "markdown":
        formatted = format_as_markdown(output)
        print(formatted)
    else:
        formatted = json.dumps(output, indent=2)
        print(formatted)

    # Write to file
    output_path = args.output
    if output_path is None:
        script_dir = os.path.dirname(os.path.abspath(__file__))
        output_path = os.path.join(script_dir, "quantifier_output.json")

    with open(output_path, "w") as f:
        json.dump(output, f, indent=2)

    if args.verbose:
        print(f"\nResults written to: {output_path}")

    return 0


if __name__ == "__main__":
    sys.exit(main())
