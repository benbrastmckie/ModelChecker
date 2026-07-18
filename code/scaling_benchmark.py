#!/usr/bin/env python3
"""scaling_benchmark.py - Scale model sizes to find z3 vs cvc5 divergence points.

This script progressively scales N (model size) for each example to find the
maximum solvable N for each solver, collecting timing data to identify where
solvers diverge in performance.

Usage:
    python scaling_benchmark.py                    # Run with defaults
    python scaling_benchmark.py --max-n 10 --timeout 30  # Quick test
    python scaling_benchmark.py --examples MOD_TH_1 --verbose  # Single example
    python scaling_benchmark.py --subtheory modal  # Filter by subtheory
    python scaling_benchmark.py --solver z3        # Single solver only

Output JSON includes:
- metadata: timestamp, solver versions, parameters
- summary: aggregate statistics (z3_wins, cvc5_wins, ties)
- by_subtheory: breakdown by logos subtheory
- results: per-example scaling curves with timing data
"""

import argparse
import json
import os
import platform
import sys
import time
from dataclasses import dataclass, field, asdict
from datetime import datetime
from typing import Any, Dict, List, Optional, Tuple

# Ensure local src is prioritized
src_path = os.path.abspath(os.path.join(os.path.dirname(__file__), 'src'))
sys.path.insert(0, src_path)

from model_checker.solver import detect_cvc5, detect_z3
from model_checker.solver.registry import (
    set_cli_backend,
    clear_cli_backend,
    reset_registry,
)
from model_checker import z3_shim
from model_checker.theory_lib.logos import get_theory
from model_checker.theory_lib.logos.examples import (
    all_subtheory_examples,
    theorem_examples,
    countermodel_examples,
)
from model_checker.builder.runner import try_single_N_static
from model_checker.builder.serialize import serialize_semantic_theory


# ============================================================================
# Data Classes
# ============================================================================

@dataclass
class ScalingPoint:
    """Single measurement point at a specific N."""
    n: int
    time_seconds: float
    success: bool

    def to_dict(self) -> Dict[str, Any]:
        return {
            "n": self.n,
            "time_ms": round(self.time_seconds * 1000, 2),
            "success": self.success,
        }


@dataclass
class ScalingResult:
    """Complete scaling result for one example/solver combination."""
    example_name: str
    subtheory: str
    solver: str
    max_n: int
    points: List[ScalingPoint] = field(default_factory=list)
    error: Optional[str] = None

    def to_dict(self) -> Dict[str, Any]:
        return {
            "example_name": self.example_name,
            "subtheory": self.subtheory,
            "solver": self.solver,
            "max_n": self.max_n,
            "points": [p.to_dict() for p in self.points],
            "growth_factor": self.calculate_growth_factor(),
            "error": self.error,
        }

    def calculate_growth_factor(self) -> Optional[float]:
        """Calculate average time growth factor between successive N values.

        Returns ratio of time(n+1)/time(n) averaged across all successful points.
        Returns None if insufficient data.
        """
        successful = [p for p in self.points if p.success and p.time_seconds > 0.001]
        if len(successful) < 2:
            return None

        ratios = []
        for i in range(1, len(successful)):
            if successful[i-1].time_seconds > 0:
                ratio = successful[i].time_seconds / successful[i-1].time_seconds
                ratios.append(ratio)

        if not ratios:
            return None
        return round(sum(ratios) / len(ratios), 2)


# ============================================================================
# Solver Management
# ============================================================================

def switch_solver(backend: str) -> None:
    """Switch to specified solver backend with full cache invalidation.

    Uses the three-step reset pattern:
    1. Clear CLI backend first
    2. Reset registry caches
    3. Reset z3_shim cached module
    4. Set new backend

    Args:
        backend: Either 'z3' or 'cvc5'
    """
    clear_cli_backend()
    reset_registry()
    z3_shim._reset_backend()
    set_cli_backend(backend)


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


def check_solver_availability() -> Tuple[bool, bool]:
    """Check if z3 and cvc5 are available.

    Returns:
        Tuple of (z3_available, cvc5_available)
    """
    return detect_z3(), detect_cvc5()


# ============================================================================
# Theory and Example Management
# ============================================================================

def get_required_subtheories(subtheory: str) -> List[str]:
    """Get the subtheory list required for a given subtheory's examples.

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


def get_subtheory_for_example(example_name: str) -> str:
    """Determine which subtheory an example belongs to based on its prefix.

    Args:
        example_name: Name like 'MOD_TH_1', 'EXT_CM_2', etc.

    Returns:
        Subtheory name
    """
    prefix_map = {
        "EXT_": "extensional",
        "MOD_": "modal",
        "CON_": "constitutive",
        "CL_": "constitutive",  # Legacy prefix
        "CF_": "counterfactual",
        "REL_": "relevance",
    }
    for prefix, subtheory in prefix_map.items():
        if example_name.startswith(prefix):
            return subtheory
    return "extensional"  # Default fallback


def get_curated_benchmark_examples() -> Dict[str, List[Any]]:
    """Get curated set of examples for scaling benchmark.

    Selects ~20 examples across all subtheories, preferring theorem examples
    (UNSAT) which exercise full search space exploration.

    Returns:
        Dictionary mapping example names to example cases
    """
    # Start with theorem examples (UNSAT problems - more demanding)
    curated = {}

    # Select representative examples from each subtheory
    # Prefer theorem examples (_TH_) over countermodel (_CM_) for scaling
    subtheory_targets = {
        "extensional": 1,
        "modal": 1,
        "constitutive": 1,
        "counterfactual": 1,
        "relevance": 1,
    }

    for subtheory, count in subtheory_targets.items():
        if subtheory not in all_subtheory_examples:
            continue

        examples = all_subtheory_examples[subtheory]

        # Sort to get consistent selection (TH before CM, then by number)
        sorted_names = sorted(examples.keys(),
                              key=lambda x: (0 if "_TH_" in x else 1, x))

        selected = 0
        for name in sorted_names:
            if selected >= count:
                break
            curated[name] = examples[name]
            selected += 1

    return curated


def flatten_examples(
    subtheory_filter: Optional[str] = None,
    example_filter: Optional[List[str]] = None,
) -> List[Tuple[str, str, List[Any]]]:
    """Flatten examples into (subtheory, name, example) tuples.

    Args:
        subtheory_filter: If provided, only return examples from this subtheory
        example_filter: If provided, only return examples with these names

    Returns:
        List of (subtheory, example_name, example_case) tuples
    """
    examples = []

    for subtheory, subtheory_examples in all_subtheory_examples.items():
        if subtheory_filter and subtheory != subtheory_filter:
            continue
        for name, example in subtheory_examples.items():
            if example_filter and name not in example_filter:
                continue
            examples.append((subtheory, name, example))

    return examples


# ============================================================================
# Core Scaling Algorithm
# ============================================================================

def find_scaling_limit(
    example_name: str,
    subtheory: str,
    solver: str,
    theory_config: Dict[str, Any],
    example_case: List[Any],
    start_n: int = 3,
    max_n: int = 16,
    timeout: float = 60.0,
    verbose: bool = False,
) -> ScalingResult:
    """Progressively scale N to find the maximum solvable model size.

    Increments N from start_n until either:
    - max_n is reached
    - A timeout occurs (runtime >= timeout)

    Collects timing data at each N for growth factor analysis.

    Args:
        example_name: Name of the example (for logging)
        subtheory: Subtheory the example belongs to
        solver: Current solver backend ('z3' or 'cvc5')
        theory_config: Serialized theory configuration
        example_case: [premises, conclusions, settings] tuple
        start_n: Starting N value (default: 3)
        max_n: Maximum N to try (default: 16)
        timeout: Per-N timeout in seconds (default: 60.0)
        verbose: Print progress per N

    Returns:
        ScalingResult with max_n found and timing points
    """
    premises, conclusions, base_settings = example_case
    points = []
    max_successful_n = 0

    for n in range(start_n, max_n + 1):
        # Create modified settings with current N and timeout
        settings = base_settings.copy()
        settings['N'] = n
        settings['max_time'] = timeout

        test_case = [premises, conclusions, settings]

        try:
            success, runtime = try_single_N_static(
                "logos", theory_config, test_case
            )
        except Exception as e:
            # Record failure and stop scaling
            points.append(ScalingPoint(n=n, time_seconds=0.0, success=False))
            return ScalingResult(
                example_name=example_name,
                subtheory=subtheory,
                solver=solver,
                max_n=max_successful_n,
                points=points,
                error=str(e),
            )

        points.append(ScalingPoint(n=n, time_seconds=runtime, success=success))

        if verbose:
            status = "OK" if success else "TIMEOUT"
            print(f"    N={n}: {runtime:.3f}s [{status}]")

        if success:
            max_successful_n = n
        else:
            # Timeout - stop scaling
            break

    return ScalingResult(
        example_name=example_name,
        subtheory=subtheory,
        solver=solver,
        max_n=max_successful_n,
        points=points,
    )


# ============================================================================
# Main Orchestration
# ============================================================================

def run_scaling_benchmark(
    subtheory_filter: Optional[str] = None,
    example_filter: Optional[List[str]] = None,
    solvers: List[str] = None,
    min_n: int = 3,
    max_n: int = 16,
    timeout: float = 60.0,
    verbose: bool = False,
) -> Dict[str, Any]:
    """Run scaling benchmark across examples and solvers.

    Args:
        subtheory_filter: Only run examples from this subtheory
        example_filter: Only run these specific examples
        solvers: List of solvers to test (default: ['z3', 'cvc5'])
        min_n: Starting N value
        max_n: Maximum N to try
        timeout: Per-N timeout in seconds
        verbose: Print detailed progress

    Returns:
        Complete benchmark output dictionary
    """
    if solvers is None:
        solvers = ['z3', 'cvc5']

    start_time = time.perf_counter()

    # Get examples to run
    if example_filter:
        # Use specified examples
        examples = flatten_examples(subtheory_filter, example_filter)
    elif subtheory_filter:
        # Use all examples from subtheory
        examples = flatten_examples(subtheory_filter)
    else:
        # Use curated benchmark set
        curated = get_curated_benchmark_examples()
        examples = [
            (get_subtheory_for_example(name), name, case)
            for name, case in curated.items()
        ]

    total_examples = len(examples)
    print(f"Running scaling benchmark on {total_examples} examples")
    print(f"Parameters: min_N={min_n}, max_N={max_n}, timeout={timeout}s")
    print(f"Solvers: {', '.join(solvers)}")
    print()

    # Results storage
    results: List[Dict[str, Any]] = []

    # Per-solver aggregate stats
    solver_stats = {s: {"max_ns": [], "total_time": 0.0} for s in solvers}

    # Per-subtheory stats
    subtheory_stats: Dict[str, Dict[str, Any]] = {}

    # Run each example with each solver
    for idx, (subtheory, name, example_case) in enumerate(examples, 1):
        print(f"[{idx}/{total_examples}] {name}")

        # Initialize subtheory tracking
        if subtheory not in subtheory_stats:
            subtheory_stats[subtheory] = {
                s: {"max_ns": [], "examples": 0} for s in solvers
            }

        example_results = {
            "example_name": name,
            "subtheory": subtheory,
        }

        for solver in solvers:
            switch_solver(solver)

            # Get theory for this subtheory
            theory = get_theory(get_required_subtheories(subtheory))
            theory_config = serialize_semantic_theory("logos", theory)

            if verbose:
                print(f"  {solver}:")

            result = find_scaling_limit(
                example_name=name,
                subtheory=subtheory,
                solver=solver,
                theory_config=theory_config,
                example_case=example_case,
                start_n=min_n,
                max_n=max_n,
                timeout=timeout,
                verbose=verbose,
            )

            # Store result
            example_results[solver] = result.to_dict()

            # Aggregate stats
            solver_stats[solver]["max_ns"].append(result.max_n)
            total_time = sum(p.time_seconds for p in result.points)
            solver_stats[solver]["total_time"] += total_time

            subtheory_stats[subtheory][solver]["max_ns"].append(result.max_n)
            subtheory_stats[subtheory][solver]["examples"] += 1

            if not verbose:
                print(f"  {solver}: max_N={result.max_n}")

        results.append(example_results)
        print()

    total_runtime = time.perf_counter() - start_time

    # Build summary
    summary = _build_summary(solver_stats, solvers)

    # Build by_subtheory
    by_subtheory = _build_subtheory_summary(subtheory_stats)

    # Build output structure
    output = {
        "metadata": {
            "timestamp": datetime.now().isoformat(),
            "z3_version": get_z3_version(),
            "cvc5_version": get_cvc5_version(),
            "platform": platform.system(),
            "python_version": platform.python_version(),
            "parameters": {
                "min_n": min_n,
                "max_n": max_n,
                "timeout": timeout,
            },
            "total_examples": total_examples,
            "total_runtime_seconds": round(total_runtime, 2),
        },
        "summary": summary,
        "by_subtheory": by_subtheory,
        "results": results,
    }

    # Print summary
    _print_summary(summary, by_subtheory, total_runtime)

    return output


def _build_summary(
    solver_stats: Dict[str, Dict[str, Any]],
    solvers: List[str]
) -> Dict[str, Any]:
    """Build aggregate summary statistics."""
    summary = {}

    for solver in solvers:
        stats = solver_stats[solver]
        max_ns = stats["max_ns"]
        summary[solver] = {
            "total_examples": len(max_ns),
            "avg_max_n": round(sum(max_ns) / len(max_ns), 2) if max_ns else 0,
            "max_max_n": max(max_ns) if max_ns else 0,
            "min_max_n": min(max_ns) if max_ns else 0,
            "total_time_seconds": round(stats["total_time"], 2),
        }

    # Compute wins/ties if both solvers present
    if len(solvers) == 2 and 'z3' in solvers and 'cvc5' in solvers:
        z3_max = solver_stats['z3']["max_ns"]
        cvc5_max = solver_stats['cvc5']["max_ns"]

        z3_wins = sum(1 for z, c in zip(z3_max, cvc5_max) if z > c)
        cvc5_wins = sum(1 for z, c in zip(z3_max, cvc5_max) if c > z)
        ties = sum(1 for z, c in zip(z3_max, cvc5_max) if z == c)

        summary["comparison"] = {
            "z3_wins": z3_wins,
            "cvc5_wins": cvc5_wins,
            "ties": ties,
        }

    return summary


def _build_subtheory_summary(
    subtheory_stats: Dict[str, Dict[str, Any]]
) -> Dict[str, Any]:
    """Build per-subtheory summary statistics."""
    by_subtheory = {}

    for subtheory, stats in subtheory_stats.items():
        by_subtheory[subtheory] = {}
        for solver, solver_data in stats.items():
            max_ns = solver_data["max_ns"]
            by_subtheory[subtheory][solver] = {
                "examples": solver_data["examples"],
                "avg_max_n": round(sum(max_ns) / len(max_ns), 2) if max_ns else 0,
            }

    return by_subtheory


def _print_summary(
    summary: Dict[str, Any],
    by_subtheory: Dict[str, Any],
    total_runtime: float
) -> None:
    """Print human-readable summary."""
    print("=" * 60)
    print("SCALING BENCHMARK SUMMARY")
    print("=" * 60)

    for solver in ['z3', 'cvc5']:
        if solver not in summary:
            continue
        s = summary[solver]
        print(f"{solver.upper()}: avg_max_N={s['avg_max_n']}, "
              f"range=[{s['min_max_n']}, {s['max_max_n']}], "
              f"time={s['total_time_seconds']}s")

    if "comparison" in summary:
        c = summary["comparison"]
        print(f"\nComparison: z3 wins={c['z3_wins']}, "
              f"cvc5 wins={c['cvc5_wins']}, ties={c['ties']}")

    print("\nBy Subtheory:")
    for subtheory, stats in sorted(by_subtheory.items()):
        parts = []
        for solver in ['z3', 'cvc5']:
            if solver in stats:
                parts.append(f"{solver}={stats[solver]['avg_max_n']}")
        print(f"  {subtheory}: {', '.join(parts)}")

    print(f"\nTotal runtime: {total_runtime:.2f}s")
    print("=" * 60)


# ============================================================================
# CLI
# ============================================================================

def parse_args() -> argparse.Namespace:
    """Parse command line arguments."""
    parser = argparse.ArgumentParser(
        description="Scale model sizes to find z3 vs cvc5 divergence points"
    )
    parser.add_argument(
        "--output", "-o",
        default=os.path.join(os.path.dirname(os.path.abspath(__file__)), "scaling_results.json"),
        help="Output JSON file (default: code/scaling_results.json)",
    )
    parser.add_argument(
        "--min-n",
        type=int,
        default=3,
        help="Starting N value (default: 3)",
    )
    parser.add_argument(
        "--max-n",
        type=int,
        default=8,
        help="Maximum N to try (default: 8)",
    )
    parser.add_argument(
        "--timeout", "-t",
        type=float,
        default=10.0,
        help="Per-N timeout in seconds (default: 10.0)",
    )
    parser.add_argument(
        "--subtheory", "-s",
        choices=[
            "extensional", "modal", "constitutive",
            "counterfactual", "relevance",
        ],
        help="Run only examples from this subtheory",
    )
    parser.add_argument(
        "--examples", "-e",
        nargs="+",
        help="Run only these specific examples",
    )
    parser.add_argument(
        "--solver",
        choices=["z3", "cvc5", "both"],
        default="both",
        help="Which solver(s) to test (default: both)",
    )
    parser.add_argument(
        "--verbose", "-v",
        action="store_true",
        help="Show detailed per-N progress",
    )
    return parser.parse_args()


def main() -> int:
    """Main entry point.

    Returns:
        Exit code (0 for success, 1 for error)
    """
    args = parse_args()

    # Check solver availability
    z3_available, cvc5_available = check_solver_availability()

    solvers = []
    if args.solver in ["z3", "both"]:
        if not z3_available:
            print("Error: z3 is not installed or not available")
            return 1
        solvers.append("z3")

    if args.solver in ["cvc5", "both"]:
        if not cvc5_available:
            print("Error: cvc5 is not installed or not available")
            return 1
        solvers.append("cvc5")

    if not solvers:
        print("Error: No solvers available")
        return 1

    print("Solver availability:")
    if "z3" in solvers:
        print(f"  z3: {get_z3_version()}")
    if "cvc5" in solvers:
        print(f"  cvc5: {get_cvc5_version()}")
    print()

    # Run benchmark
    results = run_scaling_benchmark(
        subtheory_filter=args.subtheory,
        example_filter=args.examples,
        solvers=solvers,
        min_n=args.min_n,
        max_n=args.max_n,
        timeout=args.timeout,
        verbose=args.verbose,
    )

    # Write output
    with open(args.output, "w") as f:
        json.dump(results, f, indent=2)

    print(f"\nResults written to {args.output}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
