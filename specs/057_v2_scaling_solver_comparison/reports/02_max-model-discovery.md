# Max Model Size Discovery Benchmark

## Executive Summary

This report designs a targeted benchmark to discover the maximum model size (N) that z3 and cvc5 can handle for each selected example. Unlike the v1 comparison (which tests at fixed N values), this benchmark progressively scales N upward until timeout, recording the maximum achievable size for each solver.

## Research Findings

### Existing Example Analysis

The Logos theory provides 138 examples categorized by:
1. **Countermodel status**: `_CM_` examples expect countermodels (SAT), `_TH_` examples expect no countermodels (UNSAT)
2. **Subtheory**: extensional, modal, constitutive, counterfactual, relevance, first_order

Current examples use small N values (typically N=3-4). From `output.json`, timing data at these scales shows:

| Subtheory | Examples | z3 Time | cvc5 Time | Character |
|-----------|----------|---------|-----------|-----------|
| extensional | 14 | 0.40s | 0.40s | Fast baseline |
| modal | 21 | 1.08s | 1.05s | Moderate |
| constitutive | 34 | 10.22s | 10.11s | Slow (ground/essence) |
| counterfactual | 37 | 24.64s | 28.90s | Very slow (similarity) |
| relevance | 20 | 1.46s | 1.48s | Moderate |
| first_order | 12 | 0.26s | 0.26s | Fast |

### Countermodel vs Theorem Behavior

Key insight: The computational profiles differ between:
- **Countermodel examples (CM)**: Solver must find a satisfying model (SAT). Typically faster if models exist.
- **Theorem examples (TH)**: Solver must prove no countermodel exists (UNSAT). Often harder as N grows because the search space expands exponentially.

## Selected Example Candidates

### Examples Expected to Have Countermodels (~10)

Selected for diversity across subtheories and computational complexity:

| ID | Example | Subtheory | Description | Base N |
|----|---------|-----------|-------------|--------|
| 1 | EXT_CM_1 | extensional | Contradiction (A |- ~A) | 3 |
| 2 | EXT_CM_2 | extensional | Affirming consequent | 4 |
| 3 | MOD_CM_1 | modal | Diamond A |- Box A | 4 |
| 4 | MOD_CM_2 | modal | Diamond A |- A | 4 |
| 5 | CL_CM_1 | constitutive | Equivalence of tautologies | 4 |
| 6 | CL_CM_7 | constitutive | Distribution identity | 3 |
| 7 | CF_CM_1 | counterfactual | Antecedent strengthening | 4 |
| 8 | CF_CM_7 | counterfactual | Contraposition | 4 |
| 9 | REL_CM_1 | relevance | Relevance failure | (varies) |
| 10 | FO_CM_1 | first_order | Quantifier failure | (varies) |

### Examples Expected to NOT Have Countermodels (~10)

These are theorems that should be UNSAT (no countermodel found):

| ID | Example | Subtheory | Description | Base N |
|----|---------|-----------|-------------|--------|
| 11 | EXT_TH_1 | extensional | Modus Ponens | 3 |
| 12 | EXT_TH_6 | extensional | Excluded Middle | 3 |
| 13 | MOD_TH_1 | modal | Box distribution | 4 |
| 14 | MOD_TH_5 | modal | K axiom | 4 |
| 15 | CL_TH_1 | constitutive | Ground to essence | 4 |
| 16 | CL_TH_16 | constitutive | Grounding antisymmetry | 2 |
| 17 | CF_TH_1 | counterfactual | Identity | 3 |
| 18 | CF_TH_6 | counterfactual | Consequent weakening | 3 |
| 19 | REL_TH_1 | relevance | Relevance theorem | (varies) |
| 20 | FO_TH_1 | first_order | Universal instantiation | (varies) |

## Max-N Discovery Algorithm

### Core Algorithm: Progressive Scaling

```python
def find_max_solvable_N(
    example: Example,
    solver: str,  # 'z3' or 'cvc5'
    start_N: int = 3,
    max_N: int = 20,
    timeout_seconds: float = 60.0,
) -> MaxNResult:
    """
    Find the maximum N where solver completes within timeout.

    Returns:
        MaxNResult with max_N, timing curve, and reason for stopping
    """
    timing_curve = []
    last_successful_N = None

    for N in range(start_N, max_N + 1):
        # Modify example settings with new N
        modified_settings = {**example.settings, 'N': N, 'max_time': timeout_seconds}

        start_time = time.time()
        result = run_example_with_solver(example, modified_settings, solver)
        elapsed = time.time() - start_time

        timing_curve.append(TimingPoint(N=N, time=elapsed, result=result))

        if result.timed_out or elapsed >= timeout_seconds:
            # Solver couldn't complete at this N
            return MaxNResult(
                max_N=last_successful_N,
                timing_curve=timing_curve,
                reason='timeout',
                timeout_N=N,
            )

        if result.error:
            # Solver error (memory, etc.)
            return MaxNResult(
                max_N=last_successful_N,
                timing_curve=timing_curve,
                reason='error',
                error_N=N,
                error_msg=result.error,
            )

        last_successful_N = N

    # Completed all N values without issue
    return MaxNResult(
        max_N=max_N,
        timing_curve=timing_curve,
        reason='completed',
    )
```

### Optimization: Adaptive Step Size

For efficiency, use larger initial steps then refine:

```python
def find_max_N_adaptive(example, solver, timeout):
    """Adaptive step size for faster discovery."""

    # Phase 1: Coarse search (step=4)
    coarse_max = None
    for N in [4, 8, 12, 16, 20]:
        if can_solve(example, solver, N, timeout):
            coarse_max = N
        else:
            break

    if coarse_max is None:
        return fine_search(example, solver, 3, 4, timeout)

    # Phase 2: Fine search around boundary
    lower = coarse_max
    upper = coarse_max + 4
    return fine_search(example, solver, lower, upper, timeout)

def fine_search(example, solver, lower, upper, timeout):
    """Linear search in range [lower, upper]."""
    max_N = lower
    for N in range(lower, upper + 1):
        if can_solve(example, solver, N, timeout):
            max_N = N
        else:
            break
    return max_N
```

## Output Format Specification

### Per-Example Output

```json
{
  "example_id": "CF_CM_1",
  "subtheory": "counterfactual",
  "description": "Antecedent strengthening",
  "expects_countermodel": true,
  "z3": {
    "max_N": 8,
    "timing_curve": [
      {"N": 4, "time_seconds": 0.28, "result": "sat"},
      {"N": 5, "time_seconds": 0.89, "result": "sat"},
      {"N": 6, "time_seconds": 2.45, "result": "sat"},
      {"N": 7, "time_seconds": 8.12, "result": "sat"},
      {"N": 8, "time_seconds": 24.67, "result": "sat"},
      {"N": 9, "time_seconds": null, "result": "timeout"}
    ],
    "reason": "timeout",
    "timeout_N": 9
  },
  "cvc5": {
    "max_N": 7,
    "timing_curve": [
      {"N": 4, "time_seconds": 1.00, "result": "sat"},
      {"N": 5, "time_seconds": 3.21, "result": "sat"},
      {"N": 6, "time_seconds": 12.45, "result": "sat"},
      {"N": 7, "time_seconds": 45.23, "result": "sat"},
      {"N": 8, "time_seconds": null, "result": "timeout"}
    ],
    "reason": "timeout",
    "timeout_N": 8
  },
  "comparison": {
    "max_N_winner": "z3",
    "max_N_delta": 1,
    "time_ratio_at_max_common_N": 0.55
  }
}
```

### Aggregate Output

```json
{
  "metadata": {
    "timestamp": "2026-03-30T...",
    "timeout_seconds": 60,
    "N_range": [3, 20],
    "z3_version": "4.15.8",
    "cvc5_version": "1.3.3"
  },
  "summary": {
    "total_examples": 20,
    "countermodel_examples": 10,
    "theorem_examples": 10,
    "z3_avg_max_N": 9.5,
    "cvc5_avg_max_N": 8.2,
    "z3_wins": 12,
    "cvc5_wins": 5,
    "ties": 3
  },
  "by_category": {
    "countermodel": {
      "z3_avg_max_N": 11.2,
      "cvc5_avg_max_N": 9.8
    },
    "theorem": {
      "z3_avg_max_N": 7.8,
      "cvc5_avg_max_N": 6.6
    }
  },
  "by_subtheory": {
    "extensional": {"z3_avg_max_N": 14, "cvc5_avg_max_N": 13},
    "modal": {"z3_avg_max_N": 10, "cvc5_avg_max_N": 9},
    "constitutive": {"z3_avg_max_N": 7, "cvc5_avg_max_N": 6},
    "counterfactual": {"z3_avg_max_N": 6, "cvc5_avg_max_N": 5},
    "relevance": {"z3_avg_max_N": 11, "cvc5_avg_max_N": 10},
    "first_order": {"z3_avg_max_N": 12, "cvc5_avg_max_N": 11}
  },
  "examples": [/* per-example results */]
}
```

## Implementation Sketch

### File Structure

```
code/
  max_model_benchmark.py      # Main benchmark script
  src/model_checker/
    benchmark/
      __init__.py
      max_n_discovery.py      # Core algorithm
      example_selector.py     # Selected examples
      output_formatter.py     # JSON output
```

### Core Implementation

```python
#!/usr/bin/env python3
"""max_model_benchmark.py - Discover maximum model sizes for z3 vs cvc5."""

import argparse
import json
import time
from dataclasses import dataclass, asdict
from datetime import datetime
from typing import List, Optional, Dict, Any

from model_checker.solver import detect_cvc5, detect_z3
from model_checker.solver.registry import set_cli_backend, clear_cli_backend, reset_registry
from model_checker import z3_shim
from model_checker.theory_lib.logos import get_theory
from model_checker.builder.example import BuildExample


# Selected examples (curated list)
BENCHMARK_EXAMPLES = {
    # Countermodel examples
    'EXT_CM_1': ('extensional', True, 'Contradiction'),
    'EXT_CM_2': ('extensional', True, 'Affirming consequent'),
    'MOD_CM_1': ('modal', True, 'Diamond to Box'),
    'MOD_CM_2': ('modal', True, 'Diamond to actual'),
    'CL_CM_1': ('constitutive', True, 'Tautology equivalence'),
    'CL_CM_7': ('constitutive', True, 'Distribution identity'),
    'CF_CM_1': ('counterfactual', True, 'Antecedent strengthening'),
    'CF_CM_7': ('counterfactual', True, 'Contraposition'),
    'REL_CM_1': ('relevance', True, 'Relevance failure'),
    'FO_CM_1': ('first_order', True, 'Quantifier countermodel'),

    # Theorem examples
    'EXT_TH_1': ('extensional', False, 'Modus Ponens'),
    'EXT_TH_6': ('extensional', False, 'Excluded Middle'),
    'MOD_TH_1': ('modal', False, 'Box distribution'),
    'MOD_TH_5': ('modal', False, 'K axiom'),
    'CL_TH_1': ('constitutive', False, 'Ground to essence'),
    'CL_TH_16': ('constitutive', False, 'Ground antisymmetry'),
    'CF_TH_1': ('counterfactual', False, 'Identity'),
    'CF_TH_6': ('counterfactual', False, 'Consequent weakening'),
    'REL_TH_1': ('relevance', False, 'Relevance theorem'),
    'FO_TH_1': ('first_order', False, 'Universal instantiation'),
}


@dataclass
class TimingPoint:
    N: int
    time_seconds: Optional[float]
    result: str  # 'sat', 'unsat', 'timeout', 'error'


@dataclass
class MaxNResult:
    max_N: Optional[int]
    timing_curve: List[TimingPoint]
    reason: str  # 'timeout', 'error', 'completed', 'max_reached'
    timeout_N: Optional[int] = None
    error_N: Optional[int] = None
    error_msg: Optional[str] = None


def switch_solver(backend: str) -> None:
    """Switch solver with full cache invalidation."""
    clear_cli_backend()
    reset_registry()
    z3_shim._reset_backend()
    set_cli_backend(backend)


def run_example(example_name: str, N: int, solver: str, timeout: float) -> TimingPoint:
    """Run a single example at given N with specified solver."""
    switch_solver(solver)

    # Load example data
    from model_checker.theory_lib.logos.examples import all_subtheory_examples
    subtheory, _, _ = BENCHMARK_EXAMPLES[example_name]
    example_data = all_subtheory_examples[subtheory][example_name]

    # Modify settings
    premises, conclusions, settings = example_data
    modified_settings = {**settings, 'N': N, 'max_time': timeout}

    # Build and run
    theory = get_theory(get_required_subtheories(subtheory))

    start = time.time()
    try:
        # Run the example through BuildExample
        build = BuildExample(
            premises=premises,
            conclusions=conclusions,
            settings=modified_settings,
            theory=theory,
        )
        result = build.run()
        elapsed = time.time() - start

        if elapsed >= timeout * 0.95:  # Allow 5% tolerance
            return TimingPoint(N, elapsed, 'timeout')

        # Determine SAT/UNSAT from result
        found_countermodel = result.has_countermodel if hasattr(result, 'has_countermodel') else result
        return TimingPoint(N, elapsed, 'sat' if found_countermodel else 'unsat')

    except Exception as e:
        elapsed = time.time() - start
        if 'timeout' in str(e).lower() or elapsed >= timeout:
            return TimingPoint(N, None, 'timeout')
        return TimingPoint(N, None, 'error')


def find_max_N(example_name: str, solver: str,
               start_N: int = 3, max_N: int = 16,
               timeout: float = 60.0) -> MaxNResult:
    """Find maximum N for an example with given solver."""
    curve = []
    last_success = None

    for N in range(start_N, max_N + 1):
        point = run_example(example_name, N, solver, timeout)
        curve.append(point)

        if point.result in ('timeout', 'error'):
            return MaxNResult(
                max_N=last_success,
                timing_curve=curve,
                reason=point.result,
                timeout_N=N if point.result == 'timeout' else None,
                error_N=N if point.result == 'error' else None,
            )

        last_success = N

    return MaxNResult(max_N=max_N, timing_curve=curve, reason='max_reached')


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', default='max_model_results.json')
    parser.add_argument('--timeout', type=float, default=60.0)
    parser.add_argument('--max-N', type=int, default=16)
    parser.add_argument('--examples', nargs='*', help='Specific examples to run')
    args = parser.parse_args()

    examples = args.examples or list(BENCHMARK_EXAMPLES.keys())
    results = []

    for name in examples:
        print(f"Testing {name}...")
        subtheory, expects_cm, desc = BENCHMARK_EXAMPLES[name]

        z3_result = find_max_N(name, 'z3', timeout=args.timeout, max_N=args.max_N)
        cvc5_result = find_max_N(name, 'cvc5', timeout=args.timeout, max_N=args.max_N)

        results.append({
            'example_id': name,
            'subtheory': subtheory,
            'description': desc,
            'expects_countermodel': expects_cm,
            'z3': asdict(z3_result),
            'cvc5': asdict(cvc5_result),
        })

    # Write output
    output = {
        'metadata': {
            'timestamp': datetime.now().isoformat(),
            'timeout_seconds': args.timeout,
            'max_N': args.max_N,
        },
        'examples': results,
    }

    with open(args.output, 'w') as f:
        json.dump(output, f, indent=2, default=str)

    print(f"Results written to {args.output}")


if __name__ == '__main__':
    main()
```

## Usage

```bash
# Run full benchmark (20 examples, ~40 minutes with 60s timeout)
python max_model_benchmark.py --output max_results.json

# Quick test (shorter timeout)
python max_model_benchmark.py --timeout 30 --max-N 12

# Specific examples only
python max_model_benchmark.py --examples CF_CM_1 CF_CM_7 CF_TH_1

# Focus on counterfactual (hardest subtheory)
python max_model_benchmark.py --examples CF_CM_1 CF_CM_7 CF_TH_1 CF_TH_6
```

## Expected Outcomes

Based on v1 timing data and scaling analysis:

### Predictions by Subtheory

| Subtheory | Expected Max N (z3) | Expected Max N (cvc5) | Notes |
|-----------|---------------------|----------------------|-------|
| extensional | 14-16 | 13-15 | Fast, should scale well |
| modal | 10-12 | 9-11 | Moderate, quantifiers add cost |
| constitutive | 6-8 | 5-7 | Slow, ground/essence expensive |
| counterfactual | 5-7 | 4-6 | Very slow, similarity is O(n^2) |
| relevance | 10-12 | 9-11 | Moderate |
| first_order | 11-13 | 10-12 | Fast base, quantifiers scale |

### Predictions by Category

| Category | z3 Advantage | Reasoning |
|----------|--------------|-----------|
| Countermodels (SAT) | Slight | z3's default heuristics favor SAT |
| Theorems (UNSAT) | Moderate | z3's proof strategies may be faster |

## Recommendations

1. **Start with counterfactual examples** - Most likely to reveal divergence at small N
2. **Use 60-second timeout** - Balances thoroughness with runtime
3. **Run constitutive after counterfactual** - Second-hardest subtheory
4. **Save timing curves** - Enables exponential fit analysis post-hoc
5. **Consider memory limits** - Add ulimit protection for large N

## References

- V1 Scaling Benchmark Design: `specs/057_v2_scaling_solver_comparison/reports/01_scaling-benchmark-design.md`
- Current comparison results: `code/output.json`
- Logos examples: `code/src/model_checker/theory_lib/logos/examples.py`
- SMT-COMP methodology: https://smt-comp.github.io/
