#!/usr/bin/env python3
"""Test CVC5 solver options for modal logic performance.

This script systematically tests CVC5 configuration options on worst-case
UNSAT examples to identify settings that improve performance.

Usage:
    python test_cvc5_options.py
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
    """Run a single example with the given CVC5 options.

    Returns:
        (time_seconds, result_str)
    """
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
        import traceback
        traceback.print_exc()
        return -1, f"ERROR: {e}"
    finally:
        if original_init:
            CVC5SolverAdapter.__init__ = original_init


def test_option_configurations() -> List[OptionResult]:
    """Test various CVC5 option configurations."""

    # Worst-case UNSAT examples from benchmark
    test_examples = [
        "CL_TH_1",    # 34x ratio - constitutive
        "CF_TH_2",    # 30x ratio - counterfactual
        "MOD_TH_5",   # 28x ratio - modal
    ]

    # Baseline: default configuration (just produce-unsat-cores)
    baseline_options = {
        "produce-unsat-cores": "true",
    }

    # Option configurations to test
    test_configs = [
        # Baseline
        ("baseline", baseline_options),

        # Without unsat cores
        ("no-unsat-cores", {}),

        # Eager bitblasting
        ("eager-bitblast", {
            "produce-unsat-cores": "true",
            "bitblast": "eager",
        }),

        # Different SAT solvers
        ("sat-kissat", {
            "produce-unsat-cores": "true",
            "bv-sat-solver": "kissat",
        }),
        ("sat-cryptominisat", {
            "produce-unsat-cores": "true",
            "bv-sat-solver": "cryptominisat",
        }),
        ("sat-minisat", {
            "produce-unsat-cores": "true",
            "bv-sat-solver": "minisat",
        }),

        # Decision heuristics
        ("decision-justification", {
            "produce-unsat-cores": "true",
            "decision": "justification",
        }),
        ("decision-stoponly", {
            "produce-unsat-cores": "true",
            "decision": "stoponly",
        }),

        # BV-to-int (int-blasting)
        ("solve-bv-as-int-sum", {
            "produce-unsat-cores": "true",
            "solve-bv-as-int": "sum",
        }),
        ("solve-bv-as-int-iand", {
            "produce-unsat-cores": "true",
            "solve-bv-as-int": "iand",
        }),
        ("solve-bv-as-int-bitwise", {
            "produce-unsat-cores": "true",
            "solve-bv-as-int": "bitwise",
        }),

        # Simplification options
        ("simplification-none", {
            "produce-unsat-cores": "true",
            "simplification": "none",
        }),
        ("ite-simp", {
            "produce-unsat-cores": "true",
            "ite-simp": "true",
        }),
        ("repeat-simp", {
            "produce-unsat-cores": "true",
            "repeat-simp": "true",
        }),
        ("unconstrained-simp", {
            "produce-unsat-cores": "true",
            "unconstrained-simp": "true",
        }),

        # BV options
        ("bv-eager-eval", {
            "produce-unsat-cores": "true",
            "bv-eager-eval": "true",
        }),
        ("bv-gauss-elim", {
            "produce-unsat-cores": "true",
            "bv-gauss-elim": "true",
        }),
        ("bv-to-bool", {
            "produce-unsat-cores": "true",
            "bv-to-bool": "true",
        }),

        # Combined optimizations
        ("eager+kissat", {
            "produce-unsat-cores": "true",
            "bitblast": "eager",
            "bv-sat-solver": "kissat",
        }),
        ("eager+justification", {
            "produce-unsat-cores": "true",
            "bitblast": "eager",
            "decision": "justification",
        }),
    ]

    results = []

    print("=" * 70)
    print("CVC5 Option Configuration Testing")
    print("=" * 70)
    print(f"Test examples: {test_examples}")
    print()

    for config_name, options in test_configs:
        print(f"\nTesting: {config_name}")
        print(f"  Options: {options}")

        times = {}
        for example in test_examples:
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
    """Print summary of results sorted by total time."""
    print("\n" + "=" * 70)
    print("SUMMARY (sorted by total time)")
    print("=" * 70)

    # Sort by total_time
    sorted_results = sorted(results, key=lambda r: r.total_time if r.total_time > 0 else float('inf'))

    baseline = next((r for r in results if r.option_name == "baseline"), None)
    baseline_time = baseline.total_time if baseline else 1.0

    print(f"{'Configuration':<30} {'Total(s)':<10} {'Avg(s)':<10} {'vs Baseline':<12}")
    print("-" * 70)

    for r in sorted_results:
        ratio = r.total_time / baseline_time if baseline_time > 0 else 0
        improvement = "BASELINE" if r.option_name == "baseline" else f"{ratio:.2f}x"
        print(f"{r.option_name:<30} {r.total_time:<10.3f} {r.avg_time:<10.3f} {improvement:<12}")


if __name__ == "__main__":
    results = test_option_configurations()
    print_summary(results)
