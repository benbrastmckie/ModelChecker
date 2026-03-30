# Revised Implementation Plan: V2 Scaling Solver Comparison Benchmark

- **Task**: 57 - v2_scaling_solver_comparison
- **Status**: [NOT STARTED]
- **Effort**: 3-4 hours (reduced from 6 hours by leveraging existing infrastructure)
- **Dependencies**: None (substantial infrastructure already exists)
- **Research Inputs**:
  - reports/02_max-model-discovery.md (approach design)
  - reports/03_existing-infrastructure.md (infrastructure analysis)
- **Artifacts**: plans/03_revised-implementation-plan.md (this file)
- **Revision Reason**: New research revealed substantial existing infrastructure that can be directly reused

## Overview

**Key Change from v02**: Instead of creating new `benchmark/` package from scratch, we adapt existing infrastructure:

| Component | Original Plan | Revised Plan |
|-----------|---------------|--------------|
| Core algorithm | New `find_max_N()` | Extend `_find_max_N_static()` |
| Execution | New `run_example()` | Reuse `try_single_N_static()` |
| Serialization | Implement pickling | Reuse `serialize_semantic_theory()` |
| Solver switching | Copy from v1 | Import from existing modules |
| Package structure | New `benchmark/` | Single script extending comparison.py |

## Goals & Non-Goals

**Goals** (unchanged):
- Find maximum solvable N for each example/solver combination
- Capture timing curves for scaling analysis
- Identify subtheory-specific divergence patterns
- Generate JSON output with aggregate statistics

**Non-Goals** (unchanged):
- Visualization/plotting, CI integration, memory profiling

## Existing Infrastructure to Reuse

| Component | Location | Reuse Type |
|-----------|----------|------------|
| `_find_max_N_static()` | `builder/comparison.py` | EXTEND |
| `try_single_N_static()` | `builder/runner.py` | DIRECT |
| `serialize_semantic_theory()` | `builder/serialize.py` | DIRECT |
| `switch_solver()` | `theory_lib/logos/comparison.py` | DIRECT |
| `theorem_examples` | `theory_lib/logos/examples.py` | DIRECT |

## Implementation Phases

### Phase 1: Create Scaling Script [NOT STARTED]

**Goal**: Create `code/scaling_benchmark.py` extending v1 comparison.py patterns

**Tasks**:
- [ ] Create `code/scaling_benchmark.py` as main entry point
- [ ] Import existing infrastructure:
  ```python
  from model_checker.builder.runner import try_single_N_static
  from model_checker.builder.serialize import serialize_semantic_theory
  from model_checker.theory_lib.logos.comparison import switch_solver, flatten_examples
  from model_checker.theory_lib.logos.examples import all_subtheory_examples, theorem_examples
  ```
- [ ] Define `ScalingPoint` and `ScalingResult` dataclasses (lightweight, no separate module)
- [ ] Define curated `BENCHMARK_EXAMPLES` dict (20 examples: 10 CM + 10 TH)

**Timing**: 0.5 hours

**Verification**:
- Imports work without errors
- `BENCHMARK_EXAMPLES` contains 20 entries across all subtheories

---

### Phase 2: Implement Scaling Algorithm [NOT STARTED]

**Goal**: Adapt `_find_max_N_static` pattern to collect timing curves

**Tasks**:
- [ ] Implement `find_scaling_limit()` function:
  ```python
  def find_scaling_limit(
      example_name: str,
      solver: str,
      theory_config: dict,
      example_case: list,
      start_n: int = 3,
      max_n: int = 16,
      timeout: float = 60.0
  ) -> ScalingResult:
      """Progressively scale N, collect timing at each point."""
      points = []
      for n in range(start_n, max_n + 1):
          settings = example_case[2].copy()
          settings['N'] = n
          settings['max_time'] = timeout

          success, runtime = try_single_N_static(
              theory_name, theory_config,
              [example_case[0], example_case[1], settings]
          )

          points.append(ScalingPoint(n=n, time=runtime, success=success))
          if not success:
              break

      return ScalingResult(example=example_name, solver=solver, points=points)
  ```
- [ ] Add helper `get_max_n(result: ScalingResult) -> int`
- [ ] Add helper `calculate_growth_factor(points: List[ScalingPoint]) -> float`

**Timing**: 1 hour

**Verification**:
- Test single example: `find_scaling_limit('MOD_TH_1', 'z3', ...)` returns ScalingResult
- Timing curve shows expected exponential growth pattern

---

### Phase 3: CLI and Main Loop [NOT STARTED]

**Goal**: Implement argparse CLI and orchestration

**Tasks**:
- [ ] Add argparse with options (follow comparison.py pattern):
  - `--output` (default: scaling_results.json)
  - `--timeout` (default: 60.0)
  - `--max-n` (default: 16)
  - `--min-n` (default: 3)
  - `--examples` (filter specific examples)
  - `--subtheory` (filter subtheory)
  - `--solver` (z3, cvc5, or both)
- [ ] Implement main loop:
  ```python
  for example_name, example_case in selected_examples:
      for solver in solvers:
          switch_solver(solver)
          theory_config = serialize_semantic_theory(...)
          result = find_scaling_limit(example_name, solver, theory_config, example_case)
          results.append(result)
  ```
- [ ] Add progress output with timing

**Timing**: 1 hour

**Verification**:
- `python scaling_benchmark.py --help` shows all options
- `python scaling_benchmark.py --examples MOD_TH_1 --max-n 6 --timeout 10` runs quickly

---

### Phase 4: Output and Validation [NOT STARTED]

**Goal**: JSON output generation and end-to-end validation

**Tasks**:
- [ ] Implement JSON output generation:
  ```python
  output = {
      "metadata": {
          "timestamp": ...,
          "z3_version": z3.get_version_string(),
          "cvc5_version": "cvc5 " + cvc5_version,
          "parameters": {"min_n": args.min_n, "max_n": args.max_n, "timeout": args.timeout}
      },
      "summary": {
          "total_examples": len(results),
          "z3_wins": ..., "cvc5_wins": ..., "ties": ...,
          "avg_max_n_z3": ..., "avg_max_n_cvc5": ...
      },
      "by_subtheory": {...},
      "results": [r.to_dict() for r in results]
  }
  ```
- [ ] Add `to_dict()` method to ScalingResult
- [ ] Run smoke test: `--examples MOD_TH_1 MOD_CM_1 --timeout 10 --max-n 6`
- [ ] Verify JSON is valid and parseable
- [ ] Run focused test on counterfactual (expected hardest)

**Timing**: 1 hour

**Verification**:
- JSON output matches expected schema
- Both solvers produce results
- Counterfactual examples show lower max_N than extensional (expected)

---

## Removed Phases (Compared to v02)

| Removed | Reason |
|---------|--------|
| Phase 1: Core Data Structures (new package) | Use lightweight dataclasses in single script |
| Phase 6: Documentation | Combine with Phase 4, docstrings inline |

## Testing & Validation

- [ ] Quick smoke test: `--timeout 10 --max-n 6` completes in <1 min
- [ ] Single example test: `--examples MOD_TH_1` produces valid JSON
- [ ] Both solvers: Output contains z3 and cvc5 results
- [ ] Subtheory scaling pattern: CF_TH_1 max_N < EXT_TH_1 max_N

## Artifacts & Outputs

- `code/scaling_benchmark.py` (main script, ~200-300 lines)
- `code/scaling_results.json` (sample output)
- `specs/057_v2_scaling_solver_comparison/summaries/03_implementation-summary.md`

## Rollback/Contingency

1. Single script is isolated - removal is trivial
2. v1 comparison.py unchanged
3. If examples fail, filter with `--examples` and document

## Comparison to Original Plan

| Metric | Original (v02) | Revised (v03) |
|--------|----------------|---------------|
| Effort | 6 hours | 3-4 hours |
| New files | 4 | 1 |
| New packages | 1 (benchmark/) | 0 |
| Infrastructure reuse | Low | High |
| Complexity | Higher | Lower |
