#!/usr/bin/env python3
"""Focused test of CVC5 solver options for modal logic performance.

This script tests the most promising CVC5 configurations identified from
initial testing, focusing on the impact of unsat cores and other compatible options.

Usage:
    python test_cvc5_options_focused.py
"""

import sys
import time
from typing import Dict, List, Any, Optional, Tuple
from dataclasses import dataclass

# Add the code/src directory to path
sys.path.insert(0, "/home/benjamin/Projects/Logos/ModelChecker/code/src")


@dataclass
class OptionResult:
    """Result from testing a specific option configuration."""
    option_name: str
    option_value: str
    times: Dict[str, float]  # example_name -> time
    avg_time: float
    total_time: float


def run_single_benchmark(example_name: str, options: Dict[str, str]) -> Tuple[float, str]:
    """Run a single example with the given CVC5 options."""
    from model_checker.theory_lib.logos.comparison import (
        switch_solver,
        create_test_module,
        get_required_subtheories,
    )
    from model_checker.theory_lib.logos import get_theory
    from model_checker.theory_lib.logos.examples import all_subtheory_examples
    from model_checker.builder.example import BuildExample

    # Find the example
    example_case = None
    subtheory = None
    for st_name, examples in all_subtheory_examples.items():
        for name, case in examples.items():
            if name == example_name:
                example_case = case
                subtheory = st_name
                break
        if example_case:
            break

    if not example_case:
        return -1, "NOT_FOUND"

    # Switch to CVC5 backend (with full cache invalidation)
    switch_solver("cvc5")

    # Patch the CVC5 adapter to use our options
    original_init = None
    try:
        from model_checker.solver.cvc5_adapter import CVC5SolverAdapter
        original_init = CVC5SolverAdapter.__init__

        def patched_init(self):
            from cvc5.pythonic import Solver as CVC5Solver
            self._solver = CVC5Solver()
            # Apply our options
            for opt, val in options.items():
                try:
                    self._solver.set(opt, val)
                except Exception as e:
                    pass  # Silently skip invalid options
            self._tracked = {}
            self._reverse = {}
            self._term_id_to_label = {}
            self._str_to_label = {}

        CVC5SolverAdapter.__init__ = patched_init

        # Get theory with required subtheories
        required = get_required_subtheories(subtheory)
        theory = get_theory(required)
        mock_module = create_test_module(theory)

        start_time = time.perf_counter()
        example = BuildExample(mock_module, theory, example_case)
        elapsed = time.perf_counter() - start_time

        result = bool(example.model_structure.z3_model_status)
        result_str = "SAT" if result else "UNSAT"

        return elapsed, result_str

    except Exception as e:
        return -1, f"ERROR: {e}"
    finally:
        if original_init:
            CVC5SolverAdapter.__init__ = original_init


def test_option_configurations() -> List[OptionResult]:
    """Test CVC5 option configurations - focused on compatible options."""

    # Expanded test set: worst-case UNSAT + competitive SAT examples
    test_examples_unsat = [
        "CL_TH_1",    # 34x ratio - constitutive
        "CF_TH_2",    # 30x ratio - counterfactual
        "MOD_TH_5",   # 28x ratio - modal
        "REL_TH_1",   # 24x ratio - relevance
        "MOD_TH_3",   # 25x ratio - modal
        "EXT_TH_7",   # 14x ratio - extensional
    ]

    test_examples_sat = [
        "CF_CM_1",    # CVC5 2.2x faster - SAT
        "MOD_CM_3",   # CVC5 1.4x faster - SAT
        "REL_CM_3",   # CVC5 1.1x faster - SAT
    ]

    all_examples = test_examples_unsat + test_examples_sat

    # Focused configurations based on initial findings
    test_configs = [
        # Baseline with unsat cores
        ("baseline-with-cores", {
            "produce-unsat-cores": "true",
        }),

        # Without unsat cores (big winner from initial test!)
        ("no-unsat-cores", {}),

        # No cores + decision heuristics
        ("no-cores+decision-stoponly", {
            "decision": "stoponly",
        }),
        ("no-cores+decision-justification", {
            "decision": "justification",
        }),

        # No cores + different SAT solvers
        ("no-cores+sat-kissat", {
            "bv-sat-solver": "kissat",
        }),
        ("no-cores+sat-cryptominisat", {
            "bv-sat-solver": "cryptominisat",
        }),
        ("no-cores+sat-minisat", {
            "bv-sat-solver": "minisat",
        }),

        # No cores + BV optimizations
        ("no-cores+bv-eager-eval", {
            "bv-eager-eval": "true",
        }),

        # No cores + simplification tweaks
        ("no-cores+simplification-none", {
            "simplification": "none",
        }),

        # No cores + int-blasting modes
        ("no-cores+solve-bv-as-int-bitwise", {
            "solve-bv-as-int": "bitwise",
        }),
        ("no-cores+solve-bv-as-int-iand", {
            "solve-bv-as-int": "iand",
        }),

        # Best combinations
        ("no-cores+stoponly+cryptominisat", {
            "decision": "stoponly",
            "bv-sat-solver": "cryptominisat",
        }),
        ("no-cores+stoponly+bv-eager-eval", {
            "decision": "stoponly",
            "bv-eager-eval": "true",
        }),
    ]

    results = []

    print("=" * 80)
    print("CVC5 Option Configuration Testing (Focused)")
    print("=" * 80)
    print(f"UNSAT examples: {test_examples_unsat}")
    print(f"SAT examples: {test_examples_sat}")
    print()

    for config_name, options in test_configs:
        print(f"\nTesting: {config_name}")
        print(f"  Options: {options}")

        times = {}
        for example in all_examples:
            elapsed, result_str = run_single_benchmark(example, options)
            times[example] = elapsed
            print(f"    {example}: {elapsed:.3f}s ({result_str})")

        valid_times = [t for t in times.values() if t > 0]
        avg_time = sum(valid_times) / len(valid_times) if valid_times else -1
        total_time = sum(valid_times)

        results.append(OptionResult(
            option_name=config_name,
            option_value=str(options),
            times=times,
            avg_time=avg_time,
            total_time=total_time,
        ))

        print(f"  Average: {avg_time:.3f}s, Total: {total_time:.3f}s")

    return results


def print_summary(results: List[OptionResult]):
    """Print summary of results."""
    print("\n" + "=" * 80)
    print("SUMMARY (sorted by total time)")
    print("=" * 80)

    # Sort by total_time
    sorted_results = sorted(results, key=lambda r: r.total_time if r.total_time > 0 else float('inf'))

    baseline = next((r for r in results if r.option_name == "baseline-with-cores"), None)
    baseline_time = baseline.total_time if baseline else 1.0

    print(f"{'Configuration':<35} {'Total(s)':<10} {'Avg(s)':<10} {'vs Baseline':<12}")
    print("-" * 80)

    for r in sorted_results:
        ratio = r.total_time / baseline_time if baseline_time > 0 else 0
        improvement = "BASELINE" if r.option_name == "baseline-with-cores" else f"{ratio:.2f}x"
        print(f"{r.option_name:<35} {r.total_time:<10.3f} {r.avg_time:<10.3f} {improvement:<12}")

    # Print per-example breakdown for top configurations
    print("\n" + "=" * 80)
    print("PER-EXAMPLE BREAKDOWN (top 5 configurations)")
    print("=" * 80)

    top_configs = sorted_results[:5]
    examples = list(top_configs[0].times.keys()) if top_configs else []

    header = f"{'Example':<12}"
    for r in top_configs:
        header += f" {r.option_name[:15]:<15}"
    print(header)
    print("-" * 80)

    for example in examples:
        row = f"{example:<12}"
        for r in top_configs:
            t = r.times.get(example, -1)
            row += f" {t:<15.3f}"
        print(row)


if __name__ == "__main__":
    results = test_option_configurations()
    print_summary(results)
