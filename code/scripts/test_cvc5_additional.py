#!/usr/bin/env python3
"""Test additional CVC5 configuration options post-Task 77.

This script explores options beyond the Task 77 defaults:
- Alternative decision strategies in performance mode
- BV solver variations
- Combined option effects

Usage:
    cd code && PYTHONPATH=src python scripts/test_cvc5_additional.py
"""

import sys
import time
from typing import Dict, List, Tuple
from dataclasses import dataclass

sys.path.insert(0, "/home/benjamin/Projects/Logos/ModelChecker/code/src")


@dataclass
class ConfigResult:
    """Result from testing a specific configuration."""
    config_name: str
    example_times: Dict[str, float]
    total_time: float
    avg_time: float
    description: str


def run_benchmark_with_options(example_name: str, core_mode: bool,
                               options: Dict[str, str]) -> Tuple[float, str]:
    """Run a single example with specific CVC5 options.

    Args:
        example_name: Name of the example to run
        core_mode: If True, enable produce-unsat-cores
        options: Dict of CVC5 options to set

    Returns:
        (time_seconds, result_str)
    """
    from model_checker.theory_lib.logos.examples import all_subtheory_examples
    from model_checker.theory_lib.logos import get_theory
    from model_checker.builder.example import BuildExample
    from model_checker.solver.registry import set_cli_backend, clear_cli_backend
    from model_checker.solver.lifecycle import invalidate_all_caches

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

    clear_cli_backend()
    invalidate_all_caches()
    set_cli_backend("cvc5")

    from model_checker.solver import cvc5_adapter
    original_init = cvc5_adapter.CVC5SolverAdapter.__init__

    # Capture variables for closure
    enable_cores = core_mode
    solver_options = options

    def patched_init(self_inner, **kwargs):
        from cvc5.pythonic import Solver as CVC5Solver
        self_inner._solver = CVC5Solver()
        self_inner._need_unsat_cores = enable_cores

        if enable_cores:
            self_inner._solver.set('produce-unsat-cores', 'true')

        # Apply all provided options
        for opt, val in solver_options.items():
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
        return elapsed, "SAT" if result else "UNSAT"

    except Exception as e:
        import traceback
        traceback.print_exc()
        return -1, f"ERROR: {e}"
    finally:
        cvc5_adapter.CVC5SolverAdapter.__init__ = original_init
        clear_cli_backend()
        invalidate_all_caches()


def main():
    """Run additional CVC5 configuration tests."""

    # Focus on UNSAT examples where the biggest gains were seen
    test_examples = [
        ("CL_TH_1", "UNSAT"),
        ("CF_TH_2", "UNSAT"),
        ("MOD_TH_5", "UNSAT"),
        ("REL_TH_1", "UNSAT"),
        # Also include some SAT for balance
        ("CF_CM_1", "SAT"),
        ("MOD_CM_3", "SAT"),
    ]

    # Additional configurations to test (building on Task 77 findings)
    configs = [
        # Baseline: Task 77 performance mode
        {
            "name": "Task 77 default (perf mode)",
            "core_mode": False,
            "options": {"decision": "stoponly", "bv-eager-eval": "true"},
            "description": "Current Task 77 performance mode",
        },
        # Test: remove bv-eager-eval from perf mode
        {
            "name": "Perf: stoponly only",
            "core_mode": False,
            "options": {"decision": "stoponly"},
            "description": "Performance mode with only stoponly decision",
        },
        # Test: remove stoponly from perf mode
        {
            "name": "Perf: bv-eager-eval only",
            "core_mode": False,
            "options": {"bv-eager-eval": "true"},
            "description": "Performance mode with only bv-eager-eval",
        },
        # Test: add additional options to perf mode
        {
            "name": "Perf + bv-gauss-elim",
            "core_mode": False,
            "options": {"decision": "stoponly", "bv-eager-eval": "true", "bv-gauss-elim": "true"},
            "description": "Task 77 perf + Gaussian elimination",
        },
        # Test: different SAT solvers in perf mode
        {
            "name": "Perf + kissat",
            "core_mode": False,
            "options": {"decision": "stoponly", "bv-eager-eval": "true", "bv-sat-solver": "kissat"},
            "description": "Task 77 perf + kissat SAT solver",
        },
        {
            "name": "Perf + minisat",
            "core_mode": False,
            "options": {"decision": "stoponly", "bv-eager-eval": "true", "bv-sat-solver": "minisat"},
            "description": "Task 77 perf + minisat SAT solver",
        },
        # Test: simplification options
        {
            "name": "Perf + repeat-simp",
            "core_mode": False,
            "options": {"decision": "stoponly", "bv-eager-eval": "true", "repeat-simp": "true"},
            "description": "Task 77 perf + repeated simplification",
        },
        # Test: minimal options (cores disabled only)
        {
            "name": "No cores, no opts",
            "core_mode": False,
            "options": {},
            "description": "Just disabling cores, no other options",
        },
        # Test: different decision strategies
        {
            "name": "Perf with decision=internal",
            "core_mode": False,
            "options": {"decision": "internal", "bv-eager-eval": "true"},
            "description": "Using internal decision instead of stoponly",
        },
    ]

    print("=" * 80)
    print("Additional CVC5 Configuration Testing")
    print("=" * 80)
    print(f"\nTest examples: {len(test_examples)}")
    for ex, exp in test_examples:
        print(f"  - {ex} ({exp})")
    print()

    results: List[ConfigResult] = []

    for config in configs:
        print(f"\n--- {config['name']} ---")
        print(f"    {config['description']}")
        print(f"    Options: {config['options']}")

        times = {}
        for example, expected in test_examples:
            elapsed, result = run_benchmark_with_options(
                example,
                config["core_mode"],
                config["options"]
            )
            times[example] = elapsed
            status = "OK" if result == expected else "MISMATCH"
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

    # Summary
    print("\n" + "=" * 80)
    print("SUMMARY (sorted by total time)")
    print("=" * 80)

    sorted_results = sorted(results, key=lambda r: r.total_time if r.total_time > 0 else float('inf'))
    baseline = next((r for r in results if "Task 77 default" in r.config_name), None)
    baseline_time = baseline.total_time if baseline else 1.0

    print(f"\n{'Configuration':<30} {'Total(s)':<10} {'Avg(s)':<10} {'vs Task77':<12}")
    print("-" * 80)

    for r in sorted_results:
        ratio = r.total_time / baseline_time if baseline_time > 0 else 0
        vs_baseline = f"{ratio:.2f}x"
        print(f"{r.config_name:<30} {r.total_time:<10.3f} {r.avg_time:<10.4f} {vs_baseline:<12}")

    # Per-example for best configs
    print("\n" + "=" * 80)
    print("PER-EXAMPLE: Top 4 configurations")
    print("=" * 80)

    top4 = sorted_results[:4]
    header = f"{'Example':<12}"
    for r in top4:
        header += f"{r.config_name[:16]:<18}"
    print(header)
    print("-" * 80)

    for example, expected in test_examples:
        row = f"{example:<12}"
        for r in top4:
            t = r.example_times.get(example, -1)
            row += f"{t:>8.4f}s         "
        print(row)

    # Analysis of option contributions
    print("\n" + "=" * 80)
    print("OPTION CONTRIBUTION ANALYSIS")
    print("=" * 80)

    task77 = next((r for r in results if "Task 77 default" in r.config_name), None)
    stoponly_only = next((r for r in results if "stoponly only" in r.config_name), None)
    eager_only = next((r for r in results if "bv-eager-eval only" in r.config_name), None)
    no_opts = next((r for r in results if "No cores, no opts" in r.config_name), None)

    if task77 and stoponly_only and eager_only and no_opts:
        print(f"\nBaseline (no cores, no opts):      {no_opts.total_time:.3f}s")
        print(f"+ stoponly only:                   {stoponly_only.total_time:.3f}s (delta: {stoponly_only.total_time - no_opts.total_time:+.3f}s)")
        print(f"+ bv-eager-eval only:              {eager_only.total_time:.3f}s (delta: {eager_only.total_time - no_opts.total_time:+.3f}s)")
        print(f"+ both (Task 77):                  {task77.total_time:.3f}s (delta: {task77.total_time - no_opts.total_time:+.3f}s)")

        # Check for synergy
        individual_gains = (no_opts.total_time - stoponly_only.total_time) + (no_opts.total_time - eager_only.total_time)
        combined_gain = no_opts.total_time - task77.total_time
        synergy = combined_gain - individual_gains
        print(f"\nSynergy effect: {synergy:+.3f}s (combined vs sum of individual)")


if __name__ == "__main__":
    main()
