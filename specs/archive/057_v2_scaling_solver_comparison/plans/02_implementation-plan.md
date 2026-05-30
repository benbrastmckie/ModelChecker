# Implementation Plan: V2 Scaling Solver Comparison Benchmark

- **Task**: 57 - v2_scaling_solver_comparison
- **Status**: [NOT STARTED]
- **Effort**: 6 hours
- **Dependencies**: None (v1 comparison.py infrastructure exists)
- **Research Inputs**: reports/02_max-model-discovery.md
- **Artifacts**: plans/02_implementation-plan.md (this file)
- **Standards**:
  - .claude/rules/artifact-formats.md
  - .claude/rules/state-management.md
- **Type**: python
- **Lean Intent**: false

## Overview

Implement a max-N discovery benchmark that progressively scales model sizes (N) to find the maximum N each solver (z3, cvc5) can handle before timeout. The benchmark uses 10 countermodel examples and 10 theorem examples across all subtheories, capturing timing curves and identifying divergence points. This builds on the existing v1 comparison infrastructure but adds progressive scaling rather than fixed-N testing.

### Research Integration

Key findings from `reports/02_max-model-discovery.md`:
- Selected 20 curated examples (10 CM + 10 TH) across 6 subtheories
- Progressive scaling algorithm with optional adaptive step size
- JSON output format with timing curves and comparison metrics
- Counterfactual and constitutive subtheories expected to diverge earliest (max N~5-8)
- 60-second timeout and N range 3-16 recommended

## Goals & Non-Goals

**Goals**:
- Find maximum solvable N for each example/solver combination
- Capture timing curves for scaling analysis
- Identify subtheory-specific divergence patterns
- Generate JSON output with aggregate statistics
- Provide CLI options for focused testing

**Non-Goals**:
- Visualization/plotting (post-hoc analysis)
- CI integration (future work)
- Memory profiling (out of scope)
- Parallel solver execution (sequential for reproducibility)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Long runtime (~40 min for full suite) | M | H | Early termination options, --examples filter |
| Memory exhaustion at high N | H | M | Try-except wrapper, ulimit protection |
| Solver cache affecting results | H | M | Reuse v1's switch_solver() with full cache invalidation |
| Example selection bias | M | L | Curated list covers all subtheories |
| Non-determinism in results | M | L | Fixed timeout, single-threaded execution |

## Implementation Phases

### Phase 1: Core Data Structures [NOT STARTED]

**Goal**: Define dataclasses and constants for the benchmark

**Tasks**:
- [ ] Create `code/src/model_checker/benchmark/__init__.py` (new package)
- [ ] Create `code/src/model_checker/benchmark/max_n_discovery.py` with:
  - [ ] `TimingPoint` dataclass (N, time_seconds, result)
  - [ ] `MaxNResult` dataclass (max_N, timing_curve, reason, timeout_N, error_N)
  - [ ] `BENCHMARK_EXAMPLES` dict mapping example_id to (subtheory, expects_cm, description)
  - [ ] Default constants: TIMEOUT=60.0, MIN_N=3, MAX_N=16

**Timing**: 1 hour

**Files to modify**:
- `code/src/model_checker/benchmark/__init__.py` (new)
- `code/src/model_checker/benchmark/max_n_discovery.py` (new)

**Verification**:
- Import works: `from model_checker.benchmark.max_n_discovery import TimingPoint, MaxNResult`
- BENCHMARK_EXAMPLES contains 20 entries

---

### Phase 2: Core Algorithm Implementation [NOT STARTED]

**Goal**: Implement the find_max_N function and solver execution

**Tasks**:
- [ ] Implement `run_example(example_name, N, solver, timeout) -> TimingPoint`
  - [ ] Use switch_solver() from v1 comparison.py
  - [ ] Load example from all_subtheory_examples
  - [ ] Modify settings with new N and timeout
  - [ ] Run via BuildExample
  - [ ] Capture timing and result (sat/unsat/timeout/error)
- [ ] Implement `find_max_N(example_name, solver, start_N, max_N, timeout) -> MaxNResult`
  - [ ] Linear progression from start_N to max_N
  - [ ] Early termination on timeout/error
  - [ ] Build timing curve
- [ ] Add helper `get_required_subtheories(subtheory) -> list` for theory loading

**Timing**: 1.5 hours

**Files to modify**:
- `code/src/model_checker/benchmark/max_n_discovery.py`

**Verification**:
- Test single example: `find_max_N('EXT_CM_1', 'z3', start_N=3, max_N=8, timeout=30)`
- Returns MaxNResult with timing curve

---

### Phase 3: CLI Entry Point [NOT STARTED]

**Goal**: Create the command-line interface for running benchmarks

**Tasks**:
- [ ] Create `code/max_model_benchmark.py` as CLI entry point
- [ ] Add argparse with options:
  - [ ] `--output` (default: max_model_results.json)
  - [ ] `--timeout` (default: 60.0)
  - [ ] `--max-N` (default: 16)
  - [ ] `--min-N` (default: 3)
  - [ ] `--examples` (filter to specific examples)
  - [ ] `--subtheory` (filter to specific subtheory)
  - [ ] `--solver` (run only z3 or cvc5, default both)
- [ ] Implement main loop over examples and solvers
- [ ] Add progress output (Testing {name}...)

**Timing**: 1 hour

**Files to modify**:
- `code/max_model_benchmark.py` (new)

**Verification**:
- `python max_model_benchmark.py --help` shows all options
- `python max_model_benchmark.py --examples EXT_CM_1 --timeout 10 --max-N 6` runs quickly

---

### Phase 4: Output Formatting [NOT STARTED]

**Goal**: Implement JSON output generation with aggregate statistics

**Tasks**:
- [ ] Implement per-example result dict generation
  - [ ] Include comparison metrics (max_N_winner, max_N_delta)
- [ ] Implement aggregate summary calculation
  - [ ] Total examples, z3/cvc5 wins, ties
  - [ ] Average max_N by solver
- [ ] Implement by-category breakdown (countermodel vs theorem)
- [ ] Implement by-subtheory breakdown
- [ ] Add metadata section (timestamp, versions, parameters)
- [ ] Write formatted JSON to output file

**Timing**: 1 hour

**Files to modify**:
- `code/src/model_checker/benchmark/max_n_discovery.py` (add output functions)
- `code/max_model_benchmark.py` (call output functions)

**Verification**:
- Output JSON matches schema from research report
- Contains all required sections: metadata, summary, by_category, by_subtheory, examples

---

### Phase 5: Testing and Validation [NOT STARTED]

**Goal**: Verify benchmark works correctly with quick smoke tests

**Tasks**:
- [ ] Run quick test: `python max_model_benchmark.py --timeout 10 --max-N 6`
- [ ] Verify both solvers produce results
- [ ] Check JSON output is valid and parseable
- [ ] Run focused counterfactual test (expected hardest):
  - `python max_model_benchmark.py --examples CF_CM_1 CF_TH_1 --timeout 30 --max-N 10`
- [ ] Document any discovered issues or adjustments needed
- [ ] Verify example IDs exist in all_subtheory_examples

**Timing**: 1 hour

**Files to modify**:
- `code/max_model_benchmark.py` (bug fixes if needed)
- `code/src/model_checker/benchmark/max_n_discovery.py` (bug fixes if needed)

**Verification**:
- No errors during execution
- JSON output is valid
- Results show expected patterns (faster subtheories have higher max_N)

---

### Phase 6: Documentation and Final Review [NOT STARTED]

**Goal**: Add usage documentation and ensure code quality

**Tasks**:
- [ ] Add docstrings to all public functions
- [ ] Add module-level docstring with usage examples
- [ ] Update README or add benchmark-specific docs
- [ ] Run full benchmark with default settings (if time permits)
- [ ] Save sample output as `code/sample_max_model_results.json`

**Timing**: 0.5 hours

**Files to modify**:
- `code/max_model_benchmark.py` (docstrings)
- `code/src/model_checker/benchmark/max_n_discovery.py` (docstrings)

**Verification**:
- `python max_model_benchmark.py --help` is self-documenting
- Code passes linting

## Testing & Validation

- [ ] Import test: `from model_checker.benchmark.max_n_discovery import *`
- [ ] Quick smoke test: `--timeout 10 --max-N 6` completes
- [ ] Single example test: `--examples EXT_CM_1` produces valid JSON
- [ ] Both solvers tested: Output contains z3 and cvc5 results
- [ ] Counterfactual scaling: CF_CM_1 max_N < EXT_CM_1 max_N (harder problems scale less)

## Artifacts & Outputs

- `code/src/model_checker/benchmark/__init__.py`
- `code/src/model_checker/benchmark/max_n_discovery.py`
- `code/max_model_benchmark.py`
- `code/sample_max_model_results.json` (sample output)
- `specs/057_v2_scaling_solver_comparison/summaries/02_implementation-summary.md`

## Rollback/Contingency

If implementation encounters blocking issues:
1. The new `benchmark/` package is isolated - removal is clean
2. v1 comparison.py remains unchanged and functional
3. If specific examples fail, filter them out with `--examples` and document

If benchmark runtime is prohibitive:
1. Reduce default MAX_N to 12
2. Reduce default TIMEOUT to 30
3. Add `--quick` mode that tests only 5 representative examples
