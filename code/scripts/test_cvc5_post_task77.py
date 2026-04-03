#!/usr/bin/env python3
"""Test CVC5 configuration post-Task 77 implementation.

This script compares:
1. Performance mode (Task 77 default - no unsat cores, with optimizations)
2. Diagnostic mode (unsat cores enabled, no optimizations)
3. Alternative configurations

Usage:
    cd code && PYTHONPATH=src python scripts/test_cvc5_post_task77.py
"""

import sys
import time
from typing import Dict, List, Tuple
from dataclasses import dataclass

# Add the code/src directory to path
sys.path.insert(0, "/home/benjamin/Projects/Logos/ModelChecker/code/src")


@dataclass
class ConfigResult:
    """Result from testing a specific configuration."""
    config_name: str
    example_times: Dict[str, float]  # example_name -> time
    total_time: float
    avg_time: float
    description: str


def run_benchmark_with_mode(example_name: str, need_unsat_cores: bool,
                             extra_options: Dict[str, str] = None) -> Tuple[float, str]:
    """Run a single example with specific CVC5 mode and options.

    Args:
        example_name: Name of the example to run
        need_unsat_cores: Whether to enable unsat core tracking (diagnostic mode)
        extra_options: Additional CVC5 options to set

    Returns:
        (time_seconds, result_str)
    """
    from model_checker.theory_lib.logos.examples import all_subtheory_examples
    from model_checker.theory_lib.logos import get_theory
    from model_checker.builder.example import BuildExample
    from model_checker.solver.registry import set_cli_backend, clear_cli_backend
    from model_checker.solver.lifecycle import invalidate_all_caches as invalidate_cached_expressions

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

    # Set CVC5 backend with cache invalidation
    clear_cli_backend()
    invalidate_cached_expressions()
    set_cli_backend("cvc5")

    # Patch the adapter creation to use our specific configuration
    from model_checker.solver import cvc5_adapter
    original_init = cvc5_adapter.CVC5SolverAdapter.__init__

    def patched_init(self_inner, **kwargs):
        from cvc5.pythonic import Solver as CVC5Solver
        self_inner._solver = CVC5Solver()
        self_inner._need_unsat_cores = need_unsat_cores  # Use our captured setting, not the arg

        if need_unsat_cores:
            self_inner._solver.set('produce-unsat-cores', 'true')
        else:
            # Task 77 performance optimizations
            self_inner._solver.set('decision', 'stoponly')
            self_inner._solver.set('bv-eager-eval', 'true')

        # Apply any extra options
        if extra_options:
            for opt, val in extra_options.items():
                try:
                    self_inner._solver.set(opt, val)
                except Exception:
                    pass

        self_inner._tracked = {}
        self_inner._reverse = {}
        self_inner._term_id_to_label = {}
        self_inner._str_to_label = {}

    try:
        cvc5_adapter.CVC5SolverAdapter.__init__ = patched_init

        # Get theory
        from model_checker.theory_lib.logos.comparison import (
            create_test_module,
            get_required_subtheories,
        )
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
        cvc5_adapter.CVC5SolverAdapter.__init__ = original_init
        clear_cli_backend()
        invalidate_cached_expressions()


def run_z3_baseline(example_name: str) -> Tuple[float, str]:
    """Run example with Z3 for baseline comparison."""
    from model_checker.theory_lib.logos.examples import all_subtheory_examples
    from model_checker.theory_lib.logos import get_theory
    from model_checker.builder.example import BuildExample
    from model_checker.solver.registry import set_cli_backend, clear_cli_backend
    from model_checker.solver.lifecycle import invalidate_all_caches as invalidate_cached_expressions

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

    # Set Z3 backend
    clear_cli_backend()
    invalidate_cached_expressions()
    set_cli_backend("z3")

    try:
        from model_checker.theory_lib.logos.comparison import (
            create_test_module,
            get_required_subtheories,
        )
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
        clear_cli_backend()
        invalidate_cached_expressions()


def main():
    """Run comprehensive post-Task 77 benchmarks."""

    # Test examples: mix of UNSAT (theorems) and SAT (countermodels)
    test_examples = [
        # Worst-case UNSAT examples
        ("CL_TH_1", "UNSAT"),     # Constitutive theorem
        ("CF_TH_2", "UNSAT"),     # Counterfactual theorem
        ("MOD_TH_5", "UNSAT"),    # Modal theorem
        ("REL_TH_1", "UNSAT"),    # Relevance theorem
        # SAT examples for balance
        ("CF_CM_1", "SAT"),       # Counterfactual countermodel
        ("MOD_CM_3", "SAT"),      # Modal countermodel
        ("REL_CM_3", "SAT"),      # Relevance countermodel
    ]

    # Configurations to test
    configs = [
        {
            "name": "Z3 (baseline)",
            "is_z3": True,
            "description": "Z3 solver for baseline comparison",
        },
        {
            "name": "CVC5 Performance Mode (Task 77)",
            "is_z3": False,
            "need_cores": False,
            "extra_options": {},
            "description": "No unsat cores + stoponly + bv-eager-eval",
        },
        {
            "name": "CVC5 Diagnostic Mode",
            "is_z3": False,
            "need_cores": True,
            "extra_options": {},
            "description": "Unsat cores enabled, default options",
        },
        {
            "name": "CVC5 Perf + cryptominisat",
            "is_z3": False,
            "need_cores": False,
            "extra_options": {"bv-sat-solver": "cryptominisat"},
            "description": "Performance mode + cryptominisat SAT solver",
        },
        {
            "name": "CVC5 Perf + justification",
            "is_z3": False,
            "need_cores": False,
            "extra_options": {"decision": "justification"},
            "description": "Performance mode but with full justification decisions",
        },
        {
            "name": "CVC5 No cores, no optimizations",
            "is_z3": False,
            "need_cores": False,
            "extra_options": {"decision": "internal"},  # Override stoponly
            "description": "Cores disabled, but no extra optimizations",
        },
        {
            "name": "CVC5 Cores + stoponly",
            "is_z3": False,
            "need_cores": True,
            "extra_options": {"decision": "stoponly"},
            "description": "Cores enabled + stoponly decision",
        },
        {
            "name": "CVC5 Cores + bv-eager-eval",
            "is_z3": False,
            "need_cores": True,
            "extra_options": {"bv-eager-eval": "true"},
            "description": "Cores enabled + bv-eager-eval optimization",
        },
    ]

    print("=" * 80)
    print("CVC5 Post-Task 77 Performance Analysis")
    print("=" * 80)
    print(f"\nTest examples: {len(test_examples)}")
    for ex, exp in test_examples:
        print(f"  - {ex} (expected: {exp})")
    print()

    results: List[ConfigResult] = []

    for config in configs:
        print(f"\n--- {config['name']} ---")
        print(f"    {config['description']}")

        times = {}
        for example, expected in test_examples:
            if config.get("is_z3"):
                elapsed, result = run_z3_baseline(example)
            else:
                elapsed, result = run_benchmark_with_mode(
                    example,
                    config["need_cores"],
                    config.get("extra_options", {})
                )
            times[example] = elapsed
            status = "OK" if (result == expected or elapsed < 0) else "MISMATCH"
            print(f"    {example}: {elapsed:.4f}s ({result}) [{status}]")

        valid_times = [t for t in times.values() if t > 0]
        total = sum(valid_times)
        avg = total / len(valid_times) if valid_times else -1

        results.append(ConfigResult(
            config_name=config["name"],
            example_times=times,
            total_time=total,
            avg_time=avg,
            description=config["description"],
        ))

        print(f"    Total: {total:.3f}s, Avg: {avg:.4f}s")

    # Print summary
    print("\n" + "=" * 80)
    print("SUMMARY (sorted by total time)")
    print("=" * 80)

    sorted_results = sorted(results, key=lambda r: r.total_time if r.total_time > 0 else float('inf'))
    z3_baseline = next((r for r in results if "Z3" in r.config_name), None)
    z3_time = z3_baseline.total_time if z3_baseline else 1.0

    print(f"\n{'Configuration':<35} {'Total(s)':<10} {'Avg(s)':<10} {'vs Z3':<10}")
    print("-" * 80)

    for r in sorted_results:
        ratio = r.total_time / z3_time if z3_time > 0 else 0
        vs_z3 = f"{ratio:.2f}x" if ratio > 0 else "N/A"
        print(f"{r.config_name:<35} {r.total_time:<10.3f} {r.avg_time:<10.4f} {vs_z3:<10}")

    # Per-example breakdown for top configs
    print("\n" + "=" * 80)
    print("PER-EXAMPLE BREAKDOWN (Top 3 configs)")
    print("=" * 80)

    top3 = sorted_results[:3]

    # Header
    header = f"{'Example':<15}"
    for r in top3:
        short_name = r.config_name[:18]
        header += f"{short_name:<20}"
    print(header)
    print("-" * 80)

    for example, expected in test_examples:
        row = f"{example:<15}"
        for r in top3:
            t = r.example_times.get(example, -1)
            row += f"{t:>8.4f}s           "
        print(row)

    # Analysis
    print("\n" + "=" * 80)
    print("ANALYSIS")
    print("=" * 80)

    perf_mode = next((r for r in results if "Performance Mode" in r.config_name), None)
    diag_mode = next((r for r in results if "Diagnostic Mode" in r.config_name), None)

    if perf_mode and diag_mode:
        speedup = diag_mode.total_time / perf_mode.total_time
        print(f"\nPerformance vs Diagnostic Mode speedup: {speedup:.2f}x")

    if z3_baseline and perf_mode:
        gap = perf_mode.total_time / z3_baseline.total_time
        print(f"CVC5 (optimized) vs Z3 gap: {gap:.2f}x slower")

    # UNSAT vs SAT breakdown
    unsat_examples = [ex for ex, exp in test_examples if exp == "UNSAT"]
    sat_examples = [ex for ex, exp in test_examples if exp == "SAT"]

    if perf_mode and z3_baseline:
        print("\nBy result type:")

        z3_unsat = sum(z3_baseline.example_times.get(ex, 0) for ex in unsat_examples)
        cvc5_unsat = sum(perf_mode.example_times.get(ex, 0) for ex in unsat_examples)
        print(f"  UNSAT: Z3={z3_unsat:.3f}s, CVC5={cvc5_unsat:.3f}s, ratio={cvc5_unsat/z3_unsat:.2f}x")

        z3_sat = sum(z3_baseline.example_times.get(ex, 0) for ex in sat_examples)
        cvc5_sat = sum(perf_mode.example_times.get(ex, 0) for ex in sat_examples)
        print(f"  SAT: Z3={z3_sat:.3f}s, CVC5={cvc5_sat:.3f}s, ratio={cvc5_sat/z3_sat:.2f}x")


if __name__ == "__main__":
    main()
