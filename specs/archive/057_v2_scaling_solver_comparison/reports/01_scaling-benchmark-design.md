# V2 Scaling Solver Comparison Benchmark Design

## Executive Summary

This research report analyzes the current v1 comparison implementation (`code/comparison.py` and `code/src/model_checker/theory_lib/logos/comparison.py`) and proposes a v2 architecture for a scaling benchmark that progressively increases model sizes to identify divergence points between z3 and cvc5 solvers.

## Analysis of V1 Implementation

### Current Architecture

The v1 benchmark (`comparison.py`) provides:

1. **Example-based testing**: Runs 138 pre-defined examples from `all_subtheory_examples`
2. **Dual-solver execution**: Tests each example against both z3 and cvc5 with proper cache invalidation
3. **Result comparison**: Tracks pass/fail, timing, and disagreements
4. **Subtheory breakdown**: Reports results grouped by subtheory (extensional, modal, constitutive, counterfactual, relevance, first_order)

### Key Components

```python
# Solver switching with full cache invalidation
def switch_solver(backend: str) -> None:
    clear_cli_backend()
    reset_registry()
    z3_shim._reset_backend()
    set_cli_backend(backend)

# Example structure: [premises, conclusions, settings]
# Settings include: N, contingent, non_null, non_empty, disjoint, max_time, iterate
```

### V1 Results (from output.json)

- **Total examples**: 138
- **z3**: 138/138 passed, avg 0.276s, total 38.07s
- **cvc5**: 138/138 passed, avg 0.306s, total 42.20s
- **Disagreements**: 0

The lack of disagreements at current example sizes (typically N=3-4) indicates the need for scaling to find divergence points.

## Identified Scaling Dimensions

Based on codebase analysis, the following dimensions control model complexity:

### Primary Dimension: N (State Space Size)

```python
# From LogosSemantics DEFAULT_EXAMPLE_SETTINGS
'N': 16,  # Default bit-width for state representation
```

- **N** = bit-width for BitVec states
- **Impact**: 2^N possible states (exponential growth)
- **Current range**: Examples use N=3-4
- **Scaling potential**: N=5 to N=16+ for stress testing

The state space grows as 2^N, meaning:
- N=4: 16 states
- N=6: 64 states
- N=8: 256 states
- N=10: 1024 states
- N=12: 4096 states

### Secondary Dimension: Proposition Count

Atomic propositions (sentence letters) in premises and conclusions affect constraint complexity:

```python
# From constraint generation
self.model_constraints = [
    constraint
    for sentence_letter in self.sentence_letters
    for constraint in self.proposition_class.proposition_constraints(...)
]
```

- Each proposition adds verify/falsify functions
- More propositions = more Z3 functions to reason about
- Current examples: 1-3 propositions typically

### Tertiary Dimension: Operator Complexity

Different subtheories have different computational profiles:

| Subtheory | Operators | V1 Time (z3) | Computational Character |
|-----------|-----------|--------------|------------------------|
| extensional | 8 | 0.40s | Basic propositional |
| modal | 4 | 1.08s | Quantification over worlds |
| constitutive | 5 | 10.22s | Ground/essence relations |
| counterfactual | 4 | 24.64s | Similarity comparisons |
| relevance | 1 | 1.46s | Content connection |
| first_order | 4+ | 0.27s | Quantifier handling |

The counterfactual subtheory is already 60x slower than extensional, suggesting it will diverge earliest under scaling.

### Quaternary Dimension: Frame Constraints

```python
# From LogosSemantics.__init__
self.frame_constraints = [
    possibility_downward_closure,  # ForAll quantifier
    self.is_world(self.main_world),  # World constraint
]
```

Additional constraints like `contingent`, `non_empty`, `non_null`, and `disjoint` affect solver workload.

## Research: Z3 vs CVC5 Behavior Patterns

### Expected Divergence Scenarios

Based on SMT solver research:

1. **Quantifier handling**: Z3 and cvc5 use different quantifier instantiation heuristics
2. **Theory combination**: BitVec + Bool combination may trigger different decision procedures
3. **Search strategy**: Random seed sensitivity varies between solvers
4. **Memory pressure**: Different GC and memory management under load

### Known Performance Characteristics

- **Z3**: Generally faster on bitvector arithmetic, strong default heuristics
- **cvc5**: Better on certain quantified formulas, newer preprocessing techniques
- Both show complementary strengths on different benchmark classes

### Instability Detection

SMT solver instability occurs when:
- Same formula produces different results across runs
- Minor perturbations cause large timing variance
- Timeout behavior is inconsistent

## Proposed V2 Architecture

### Design Goals

1. **Parameterized scaling**: Systematic variation of N, proposition count, constraint density
2. **Divergence detection**: Identify exact threshold where solvers disagree or timeout differently
3. **Per-subtheory curves**: Generate scaling profiles for each subtheory
4. **Reproducible results**: Fixed seeds, deterministic example generation

### Core Data Structures

```python
@dataclass
class ScalingPoint:
    """Single data point in scaling curve."""
    N: int
    proposition_count: int
    subtheory: str
    z3_result: Optional[bool]      # SAT/UNSAT/None(timeout)
    cvc5_result: Optional[bool]
    z3_time: float
    cvc5_time: float
    z3_reason_unknown: Optional[str]
    cvc5_reason_unknown: Optional[str]
    diverged: bool                  # Results disagree

@dataclass
class ScalingCurve:
    """Scaling behavior for one subtheory/example."""
    subtheory: str
    example_template: str
    points: List[ScalingPoint]
    divergence_point: Optional[int]  # N where first divergence
    z3_timeout_point: Optional[int]  # N where z3 times out
    cvc5_timeout_point: Optional[int]  # N where cvc5 times out
```

### Scaling Strategy

#### Phase 1: Binary Search for Divergence

```python
def find_divergence_point(example_template, subtheory, min_N=4, max_N=16):
    """Binary search to find smallest N where solvers diverge."""
    lo, hi = min_N, max_N

    while lo < hi:
        mid = (lo + hi) // 2
        z3_result, cvc5_result = run_both(example_template, N=mid)

        if diverged(z3_result, cvc5_result):
            hi = mid  # Divergence found, search lower
        else:
            lo = mid + 1  # No divergence, search higher

    return lo if diverged_at(lo) else None
```

#### Phase 2: Linear Scaling Curve

Once divergence bounds are known, collect detailed timing data:

```python
def collect_scaling_curve(example_template, subtheory, start_N, end_N):
    """Collect timing data across N range."""
    points = []
    for N in range(start_N, end_N + 1):
        point = run_scaling_point(example_template, N)
        points.append(point)

        # Early termination on double timeout
        if point.z3_time >= TIMEOUT and point.cvc5_time >= TIMEOUT:
            break

    return ScalingCurve(subtheory, example_template, points)
```

### Example Templates

Instead of fixed examples, use parameterized templates:

```python
SCALING_TEMPLATES = {
    'extensional_conjunction': {
        'generator': lambda n_props: (
            [f'({" \\wedge ".join([chr(65+i) for i in range(n_props)])})'],
            [f'({chr(65)} \\wedge {chr(65+n_props-1)})'],
            {}  # Settings filled by scaler
        ),
        'subtheory': 'extensional',
        'prop_range': (2, 10),
    },
    'modal_necessity': {
        'generator': lambda n_props: (
            [f'\\Box {chr(65+i)}' for i in range(n_props)],
            [f'\\Box ({" \\wedge ".join([chr(65+i) for i in range(n_props)])})'],
            {}
        ),
        'subtheory': 'modal',
        'prop_range': (1, 6),
    },
    'counterfactual_chain': {
        'generator': lambda depth: (
            [f'({"(A \\boxright ".replace("A", chr(65+i)) * depth}A{")"}'],
            ['B'],
            {}
        ),
        'subtheory': 'counterfactual',
        'prop_range': (1, 4),
    },
}
```

### Output Format

```json
{
  "metadata": {
    "timestamp": "...",
    "z3_version": "...",
    "cvc5_version": "...",
    "timeout_ms": 30000,
    "scaling_strategy": "binary_search_then_linear"
  },
  "divergence_summary": {
    "total_templates": 12,
    "templates_with_divergence": 3,
    "earliest_divergence_N": 7
  },
  "by_subtheory": {
    "extensional": {
      "templates_tested": 3,
      "divergence_found": false,
      "max_N_tested": 16,
      "scaling_curves": [...]
    },
    "counterfactual": {
      "templates_tested": 2,
      "divergence_found": true,
      "first_divergence_N": 7,
      "scaling_curves": [...]
    }
  },
  "scaling_curves": [...],
  "recommendations": {
    "safe_N_for_agreement": 6,
    "subtheories_needing_attention": ["counterfactual", "constitutive"]
  }
}
```

### CLI Interface

```bash
# Quick divergence scan
./comparison_v2.py --mode=divergence-scan --timeout=30

# Full scaling curves
./comparison_v2.py --mode=full-curves --min-N=4 --max-N=16

# Single subtheory focus
./comparison_v2.py --subtheory=counterfactual --mode=full-curves

# Custom template
./comparison_v2.py --template=modal_necessity --N-range=4,12
```

## Implementation Recommendations

### Phase 1: Core Infrastructure (Priority: High)

1. Create `ScalingPoint` and `ScalingCurve` dataclasses
2. Implement parameterized example generation
3. Add timeout detection with `reason_unknown()` capture
4. Build binary search divergence finder

### Phase 2: Template Library (Priority: Medium)

1. Create 2-3 templates per subtheory
2. Ensure templates scale meaningfully with N
3. Include both SAT and UNSAT expected cases
4. Document expected scaling behavior

### Phase 3: Analysis Tools (Priority: Medium)

1. Generate scaling curve visualizations
2. Statistical analysis of timing variance
3. Divergence pattern classification
4. Recommendations engine

### Phase 4: Integration (Priority: Low)

1. Integrate with existing test suite
2. CI/CD hooks for regression detection
3. Historical comparison tracking

## Risk Assessment

### Technical Risks

1. **Memory exhaustion**: Large N values may OOM before timeout
   - Mitigation: Memory limits via ulimit or solver options

2. **Non-determinism**: Random seed variation could cause flaky results
   - Mitigation: Fixed seeds, multiple runs with statistical analysis

3. **Template bias**: Generated examples may not represent real usage
   - Mitigation: Include adapted versions of existing v1 examples

### Operational Risks

1. **Long runtime**: Full scaling curves could take hours
   - Mitigation: Parallel execution, early termination options

2. **Interpretation complexity**: Results need expert analysis
   - Mitigation: Automated recommendations, clear visualizations

## Conclusion

The v2 scaling benchmark should:

1. **Start with binary search** to efficiently find divergence points
2. **Focus on counterfactual/constitutive** subtheories first (already show 10-25x base timing)
3. **Scale N from 4 to 16** as primary dimension
4. **Capture both result disagreement and timeout asymmetry** as divergence types
5. **Generate actionable recommendations** about safe operating ranges

The architecture builds on v1's proven solver-switching infrastructure while adding systematic scaling, divergence detection, and per-subtheory analysis capabilities.

## References

- [cvc5: A Versatile and Industrial-Strength SMT Solver](https://www-cs.stanford.edu/~preiner/publications/2022/BarbosaBBKLMMMN-TACAS22.pdf)
- [Z3 Performance Issues](https://github.com/Z3Prover/z3/issues/7038)
- [SMT Solver Instability Research](https://ceur-ws.org/Vol-4008/SMT_paper21.pdf)
- [SMT-COMP Benchmarking Methodology](https://smt-comp.github.io/2014/benchmarks.html)
