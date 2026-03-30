# Existing Infrastructure Analysis for Scaling Benchmark

**Task**: 57 - V2 Scaling Solver Comparison
**Round**: 3
**Date**: 2026-03-30

## Executive Summary

The ModelChecker codebase has **substantial existing infrastructure** for:
1. Comparing solver behavior (z3 vs cvc5)
2. Finding maximum model sizes through iterative scaling
3. Running examples with timing and structured output

This infrastructure can be adapted with moderate effort for the v2 scaling benchmark. The key insight is that the existing `ModelComparison` class already implements a `_find_max_N_static` algorithm that scales N values until timeout -- exactly the pattern needed for scaling benchmarks.

---

## Infrastructure Components

### 1. Theory Comparison Framework

**Location**: `code/src/model_checker/theory_lib/logos/comparison.py`

This is the v1 comparison script that compares z3 vs cvc5 on all logos examples.

**Key Components**:
- `switch_solver(backend)` - Switches between z3/cvc5 with full cache invalidation
- `run_example_with_timing()` - Runs a single example and returns (result, passed, time, error)
- `run_benchmarks()` - Main orchestrator that runs all examples against both solvers
- `flatten_examples()` - Converts `all_subtheory_examples` dict into list of tuples

**Output Structure** (JSON):
```python
{
    "metadata": {timestamp, z3_version, cvc5_version, platform, python_version},
    "summary": {solver -> {total, passed, failed, errors, avg_time}},
    "by_subtheory": {subtheory -> {z3: stats, cvc5: stats}},
    "results": [per-example results],
    "disagreements": [examples where solvers disagree]
}
```

**Reuse Potential**: HIGH - The solver switching, timing infrastructure, and output format can be directly reused.

---

### 2. Maximum Model Size Discovery

**Location**: `code/src/model_checker/builder/comparison.py`

The `ModelComparison` class provides infrastructure for finding maximum model sizes.

**Key Function**: `_find_max_N_static(theory_name, theory_config, example_case)`

```python
def _find_max_N_static(theory_name: str, theory_config: Dict[str, Any], example_case: List[Any]) -> int:
    """Find maximum N for a theory (can be pickled for multiprocessing)."""
    premises, conclusions, settings = example_case
    current_N = settings.get('N', 2)
    max_N = 0

    while True:
        test_settings = settings.copy()
        test_settings['N'] = current_N
        test_case = [premises, conclusions, test_settings]

        success, runtime = try_single_N_static(theory_name, theory_config, test_case)

        if success:
            max_N = current_N
            current_N += 1
        else:
            break

    return max_N
```

**Key Pattern**: Incrementally increases N until timeout, returns max successful N.

**`compare_semantics()` Method**:
- Takes list of `(theory_name, semantic_theory, example_case)` tuples
- Uses `ProcessPoolExecutor` for parallel execution
- Returns `[(theory_name, max_N), ...]` sorted by max_N descending

**Reuse Potential**: HIGH - This is essentially the core scaling algorithm we need.

---

### 3. Model Execution Engine

**Location**: `code/src/model_checker/builder/runner.py`

**Key Functions**:
- `try_single_N_static()` - Static (picklable) function to test a single N value
- `try_single_N()` - Instance method version
- `try_single_N_serialized()` - Uses serialization for multiprocessing

**`try_single_N_static` Signature**:
```python
def try_single_N_static(
    theory_name: TheoryName,
    theory_config: Dict[str, Any],
    example_case: List[Any]
) -> Tuple[bool, float]:
    """
    Returns:
        tuple: (success, runtime)
        - success: True if model found within max_time
        - runtime: Time taken to attempt finding the model
    """
```

**Implementation Details**:
- Deserializes theory from config
- Creates Syntax, Semantics, ModelConstraints, ModelStructure
- Compares runtime against `settings['max_time']`
- Returns (success, runtime) tuple

**Reuse Potential**: HIGH - Core execution primitive for scaling tests.

---

### 4. Theory Serialization

**Location**: `code/src/model_checker/builder/serialize.py`

Enables multiprocessing by serializing semantic theories to picklable format.

**Key Functions**:
- `serialize_semantic_theory(theory_name, semantic_theory)` -> Dict
- `deserialize_semantic_theory(theory_config)` -> semantic_theory dict
- `serialize_operators()` / `deserialize_operators()`

**Serialized Format**:
```python
{
    "theory_name": "logos",
    "semantics": {"class_name": "LogosSemantics", "module_name": "..."},
    "proposition": {"class_name": "LogosProposition", "module_name": "..."},
    "model": {"class_name": "LogosModelStructure", "module_name": "..."},
    "operators": {op_name: {"class_name": "...", "module_name": "..."}, ...},
    "dictionary": {}
}
```

**Reuse Potential**: HIGH - Required for multiprocessing in scaling benchmark.

---

### 5. Example Organization

**Location**: `code/src/model_checker/theory_lib/logos/examples.py`

**Structure**:
- `all_subtheory_examples` - Dict mapping subtheory -> examples dict
- `unit_tests` / `test_example_range` - Aggregated examples
- `countermodel_examples` / `theorem_examples` - Categorized examples

**Example Format**:
```python
example = [
    premises,      # List of formula strings
    conclusions,   # List of formula strings
    settings       # Dict with N, max_time, expectation, etc.
]
```

**Settings Include**:
- `N`: Number of worlds/model size
- `max_time`: Timeout in seconds
- `expectation`: True=SAT (countermodel), False=UNSAT (theorem)
- `contingent`, `non_null`, `non_empty`, `disjoint`: Semantic flags

**Reuse Potential**: MEDIUM - Example format is good, but scaling benchmark needs curated subset with specific characteristics.

---

### 6. Solver Registry

**Location**: `code/src/model_checker/solver/registry.py`

**Key Functions**:
- `set_cli_backend(backend)` - Set active solver
- `clear_cli_backend()` - Clear backend selection
- `reset_registry()` - Reset cached state
- `get_active_backend()` - Query current solver

**z3_shim Reset**:
```python
from model_checker import z3_shim
z3_shim._reset_backend()  # Clear cached z3 module
```

**Full Switching Pattern**:
```python
def switch_solver(backend: str) -> None:
    clear_cli_backend()
    reset_registry()
    z3_shim._reset_backend()
    set_cli_backend(backend)
```

**Reuse Potential**: HIGH - Required for comparing solvers.

---

## Adaptation Strategy for V2 Scaling Benchmark

### Phase 1: Leverage Existing Infrastructure

**Use directly without modification**:
1. `switch_solver()` - solver switching
2. `serialize_semantic_theory()` / `deserialize_semantic_theory()` - multiprocessing support
3. `try_single_N_static()` - single execution primitive
4. Example format `[premises, conclusions, settings]`

### Phase 2: Adapt Core Algorithm

**Modify `_find_max_N_static` for scaling benchmark**:

```python
def find_scaling_limit_static(
    solver: str,
    theory_config: Dict[str, Any],
    example_case: List[Any],
    start_n: int = 2,
    max_n: int = 50,
    timeout_per_n: float = 10.0
) -> ScalingResult:
    """Find maximum N and collect timing data at each scale point."""
    results = []
    premises, conclusions, base_settings = example_case

    for n in range(start_n, max_n + 1):
        settings = base_settings.copy()
        settings['N'] = n
        settings['max_time'] = timeout_per_n

        test_case = [premises, conclusions, settings]
        success, runtime = try_single_N_static(theory_name, theory_config, test_case)

        results.append(ScalingPoint(n=n, time=runtime, success=success))

        if not success:
            break

    return ScalingResult(
        example=example_name,
        solver=solver,
        max_n=max(r.n for r in results if r.success) if results else 0,
        points=results
    )
```

### Phase 3: New Output Format

**Extend existing JSON structure for scaling data**:
```python
{
    "metadata": {...},  # Same as v1
    "scaling_results": [
        {
            "example_name": "MOD_TH_1",
            "subtheory": "modal",
            "z3": {
                "max_n": 12,
                "points": [
                    {"n": 2, "time_ms": 50, "success": true},
                    {"n": 3, "time_ms": 120, "success": true},
                    ...
                ],
                "growth_factor": 2.1
            },
            "cvc5": {
                "max_n": 10,
                "points": [...],
                "growth_factor": 2.5
            }
        }
    ],
    "summary": {
        "z3_wins": 8,
        "cvc5_wins": 5,
        "ties": 7,
        "avg_growth_z3": 2.3,
        "avg_growth_cvc5": 2.8
    }
}
```

### Phase 4: Curated Example Selection

**Selection Criteria** (from existing examples):
1. Use `theorem_examples` (UNSAT problems) - force full search space exploration
2. Select examples from each subtheory for coverage
3. Prioritize examples with moderate base N (3-5) that show scaling potential
4. Include variety of operator complexity (simple extensional to complex relevance)

**Candidate Selection Approach**:
```python
# From existing infrastructure
from model_checker.theory_lib.logos.examples import (
    all_subtheory_examples,
    theorem_examples
)

# Filter for scaling suitability
scaling_candidates = []
for name, example in theorem_examples.items():
    settings = example[2]
    if settings.get('expectation') == False:  # UNSAT/theorem
        scaling_candidates.append((name, example))
```

---

## Code Snippets to Reuse

### Solver Switching (copy directly)
```python
# From comparison.py
def switch_solver(backend: str) -> None:
    clear_cli_backend()
    reset_registry()
    z3_shim._reset_backend()
    set_cli_backend(backend)
```

### Example Execution with Timing (copy and extend)
```python
# From test_solver_comparison.py
def run_example_with_timing(example_case, theory):
    start_time = time.perf_counter()
    error = None
    result = None

    try:
        mock_module = create_test_module(theory)
        example = BuildExample(mock_module, theory, example_case)
        result = bool(example.model_structure.z3_model_status)
    except Exception as e:
        error = str(e)

    elapsed = time.perf_counter() - start_time
    return result, elapsed, error
```

### Theory Loading with Dependencies
```python
# From comparison.py
def get_required_subtheories(subtheory: str) -> List[str]:
    subtheory_deps = {
        "extensional": ["extensional"],
        "modal": ["extensional", "modal", "first_order"],
        "constitutive": ["extensional", "modal", "constitutive"],
        "counterfactual": ["extensional", "modal", "counterfactual"],
        "relevance": ["extensional", "modal", "constitutive", "relevance"],
        "first_order": ["extensional", "constitutive", "first_order"],
    }
    return subtheory_deps.get(subtheory, ["extensional", subtheory])
```

---

## Implementation Estimate

| Component | Effort | Notes |
|-----------|--------|-------|
| Solver switching | None | Direct reuse |
| Serialization | None | Direct reuse |
| Core execution | Low | Wrap existing `try_single_N_static` |
| Scaling loop | Medium | Adapt `_find_max_N_static` |
| Example curation | Medium | Select ~20 from existing examples |
| Output format | Medium | Extend existing JSON schema |
| CLI integration | Low | Follow existing comparison.py pattern |
| Analysis/visualization | Medium | New code for growth factor analysis |

**Total Estimate**: 1-2 days of focused implementation

---

## Recommendations

1. **Start with existing comparison.py as template** - The v1 script has proven infrastructure

2. **Use existing example structure** - Don't reinvent the example format

3. **Leverage multiprocessing infrastructure** - The serialization and ProcessPoolExecutor patterns work well

4. **Keep output format consistent** - Extend rather than replace the JSON schema

5. **Curate examples carefully** - Quality over quantity; ~20 well-chosen examples will be more valuable than running all 100+ examples

---

## Key Files Reference

| Purpose | File Path |
|---------|-----------|
| V1 comparison script | `code/src/model_checker/theory_lib/logos/comparison.py` |
| Max N discovery | `code/src/model_checker/builder/comparison.py` |
| Execution engine | `code/src/model_checker/builder/runner.py` |
| Serialization | `code/src/model_checker/builder/serialize.py` |
| Examples | `code/src/model_checker/theory_lib/logos/examples.py` |
| Solver registry | `code/src/model_checker/solver/registry.py` |
| Test infrastructure | `code/src/model_checker/theory_lib/logos/tests/integration/test_solver_comparison.py` |
