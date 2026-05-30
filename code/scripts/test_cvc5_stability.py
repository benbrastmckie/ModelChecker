#!/usr/bin/env python3
"""CVC5 vs Z3 performance stability benchmark.

Runs curated logos theory examples multiple times through both Z3 and CVC5
to measure timing variance and produce statistically meaningful comparisons.
Reports mean, stddev, min, max per example, and breaks down UNSAT vs SAT
performance ratios.

Useful for:
- Validating that a single-run measurement is trustworthy (low variance)
- Detecting high-variance examples where single runs can be misleading
- Comparing CVC5 configurations with statistical confidence

Usage:
    cd code && PYTHONPATH=src python scripts/test_cvc5_stability.py
"""

import os
import sys
import time
from typing import Dict, List, Tuple
from dataclasses import dataclass
import statistics

sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "src"))


def run_z3_baseline(example_name: str) -> Tuple[float, str]:
    """Run example with Z3 for baseline comparison."""
    from model_checker.theory_lib.logos.examples import all_subtheory_examples
    from model_checker.theory_lib.logos import get_theory
    from model_checker.builder.example import BuildExample
    from model_checker.solver.registry import set_cli_backend, clear_cli_backend
    from model_checker.solver.lifecycle import invalidate_all_caches

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
        return elapsed, "SAT" if result else "UNSAT"

    except Exception as e:
        return -1, f"ERROR: {e}"
    finally:
        clear_cli_backend()
        invalidate_all_caches()


def run_cvc5_with_options(example_name: str, options: Dict[str, str]) -> Tuple[float, str]:
    """Run example with CVC5, monkey-patching the adapter to inject custom options.

    This bypasses the normal settings-based config so we can test arbitrary
    CVC5 option combinations without modifying the adapter code."""
    from model_checker.theory_lib.logos.examples import all_subtheory_examples
    from model_checker.theory_lib.logos import get_theory
    from model_checker.builder.example import BuildExample
    from model_checker.solver.registry import set_cli_backend, clear_cli_backend
    from model_checker.solver.lifecycle import invalidate_all_caches

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

    captured_options = options.copy()

    def patched_init(self_inner, **kwargs):
        from cvc5.pythonic import Solver as CVC5Solver
        self_inner._solver = CVC5Solver()
        self_inner._need_unsat_cores = False

        for opt, val in captured_options.items():
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
        return -1, f"ERROR: {e}"
    finally:
        cvc5_adapter.CVC5SolverAdapter.__init__ = original_init
        clear_cli_backend()
        invalidate_all_caches()


def main():
    """Run stability test with multiple iterations."""

    # Curated worst-case examples from task 76 benchmark.
    # Mix of UNSAT (theorem proving) and SAT (countermodel) workloads.
    test_examples = [
        ("CL_TH_1", "UNSAT"),   # constitutive logic theorem
        ("CF_TH_2", "UNSAT"),   # counterfactual theorem
        ("MOD_TH_5", "UNSAT"),  # modal logic theorem
        ("CF_CM_1", "SAT"),     # counterfactual countermodel
    ]

    # CVC5 configurations to compare. Edit this list to test new options.
    # "Task 77 optimal" is the production config (decision=stoponly + bv-eager-eval).
    configs = [
        {
            "name": "Task 77 optimal",
            "options": {"decision": "stoponly", "bv-eager-eval": "true"},
        },
        {
            "name": "Explicit CaDiCaL",
            "options": {"decision": "stoponly", "bv-eager-eval": "true", "bv-sat-solver": "cadical"},
        },
    ]

    ITERATIONS = 5  # increase for tighter confidence intervals
    print("=" * 80)
    print(f"CVC5 Stability Test - {ITERATIONS} iterations per example")
    print("=" * 80)

    # Collect results
    z3_results = {ex: [] for ex, _ in test_examples}
    cvc5_results = {cfg["name"]: {ex: [] for ex, _ in test_examples} for cfg in configs}

    for iteration in range(ITERATIONS):
        print(f"\n--- Iteration {iteration + 1}/{ITERATIONS} ---")

        # Run Z3
        for example, expected in test_examples:
            elapsed, result = run_z3_baseline(example)
            z3_results[example].append(elapsed)
            print(f"  Z3 {example}: {elapsed:.4f}s")

        # Run each CVC5 config
        for config in configs:
            for example, expected in test_examples:
                elapsed, result = run_cvc5_with_options(example, config["options"])
                cvc5_results[config["name"]][example].append(elapsed)
                print(f"  {config['name'][:12]} {example}: {elapsed:.4f}s")

    # Analysis
    print("\n" + "=" * 80)
    print("STATISTICAL ANALYSIS")
    print("=" * 80)

    print(f"\n{'Config/Example':<30} {'Mean':<10} {'StdDev':<10} {'Min':<10} {'Max':<10}")
    print("-" * 70)

    for example, _ in test_examples:
        times = z3_results[example]
        mean = statistics.mean(times)
        stdev = statistics.stdev(times) if len(times) > 1 else 0
        print(f"Z3 {example:<26} {mean:<10.4f} {stdev:<10.4f} {min(times):<10.4f} {max(times):<10.4f}")

    for config in configs:
        print()
        for example, _ in test_examples:
            times = cvc5_results[config["name"]][example]
            mean = statistics.mean(times)
            stdev = statistics.stdev(times) if len(times) > 1 else 0
            print(f"{config['name'][:10]} {example:<18} {mean:<10.4f} {stdev:<10.4f} {min(times):<10.4f} {max(times):<10.4f}")

    # Compare means
    print("\n" + "=" * 80)
    print("MEAN COMPARISON")
    print("=" * 80)

    z3_total_mean = sum(statistics.mean(z3_results[ex]) for ex, _ in test_examples)
    print(f"\nZ3 total mean: {z3_total_mean:.3f}s")

    for config in configs:
        cvc5_total_mean = sum(statistics.mean(cvc5_results[config["name"]][ex]) for ex, _ in test_examples)
        ratio = cvc5_total_mean / z3_total_mean
        print(f"{config['name']} total mean: {cvc5_total_mean:.3f}s ({ratio:.2f}x vs Z3)")

    # UNSAT vs SAT breakdown
    unsat_examples = [ex for ex, exp in test_examples if exp == "UNSAT"]
    sat_examples = [ex for ex, exp in test_examples if exp == "SAT"]

    print("\n" + "=" * 80)
    print("UNSAT vs SAT MEAN BREAKDOWN")
    print("=" * 80)

    z3_unsat_mean = sum(statistics.mean(z3_results[ex]) for ex in unsat_examples)
    z3_sat_mean = sum(statistics.mean(z3_results[ex]) for ex in sat_examples)
    print(f"\nZ3: UNSAT={z3_unsat_mean:.3f}s, SAT={z3_sat_mean:.3f}s")

    for config in configs:
        cvc5_unsat_mean = sum(statistics.mean(cvc5_results[config["name"]][ex]) for ex in unsat_examples)
        cvc5_sat_mean = sum(statistics.mean(cvc5_results[config["name"]][ex]) for ex in sat_examples)
        unsat_ratio = cvc5_unsat_mean / z3_unsat_mean
        sat_ratio = cvc5_sat_mean / z3_sat_mean
        print(f"{config['name']}: UNSAT={cvc5_unsat_mean:.3f}s ({unsat_ratio:.2f}x), SAT={cvc5_sat_mean:.3f}s ({sat_ratio:.2f}x)")


if __name__ == "__main__":
    main()
