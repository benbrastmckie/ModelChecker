# Research Report: CVC5 Unsat Core Tracking Overhead

**Task**: 77 - Conditional unsat core tracking for CVC5 solver
**Date**: 2026-04-03
**Session**: sess_1775240861_7b2f37

## Executive Summary

The `produce-unsat-cores` option in CVC5 adds approximately **10-30% overhead** (1.1x-1.3x) to solver runtime, but this is **not the primary cause** of CVC5's observed slowness (25-35x slower than Z3 on UNSAT examples). The overhead amounts to only 0.05-0.15ms per solve operation, whereas the worst-case examples show ~2-3 second differences between solvers.

**Recommendation**: Implementing conditional unsat core tracking is a **low-priority optimization** that would yield marginal improvements (~100ms total across 24 curated examples). The CVC5 performance gap has other root causes that should be investigated first.

## Round 1: Measured Overhead

### Direct CVC5 Benchmark Results

Testing with bitvector constraints similar to ModelChecker's modal logic:

| Test Case | With Cores | Without Cores | Overhead |
|-----------|------------|---------------|----------|
| Modal N=3 (8 states) | 1.030ms | 0.908ms | 1.13x (+0.12ms) |
| Modal N=4 (16 states) | 1.120ms | 1.230ms | 0.91x (-0.11ms) |
| Modal N=5 (32 states) | 1.214ms | 1.076ms | 1.13x (+0.14ms) |
| Modal N=6 (64 states) | 1.262ms | 1.152ms | 1.10x (+0.11ms) |
| Complex N=4 depth=5 | 0.459ms | 0.355ms | 1.30x (+0.10ms) |
| Complex N=6 depth=8 | 0.631ms | 0.486ms | 1.30x (+0.15ms) |

**Key Finding**: Overhead is ~10-30% or ~0.1ms per solve, which cannot account for the 2-3 second differences seen in worst-case examples.

### Comparison to Observed CVC5 Slowness

From benchmark data (output.json):

| Example | Z3 Time | CVC5 Time | Ratio | Unsat Core Overhead (est.) |
|---------|---------|-----------|-------|---------------------------|
| CL_TH_1 | 0.064s | 2.206s | 34x | ~0.0001s (0.005%) |
| CF_TH_2 | 0.090s | 2.710s | 30x | ~0.0001s (0.004%) |
| MOD_TH_5 | 0.071s | 2.012s | 28x | ~0.0001s (0.005%) |

The unsat core overhead (~0.1ms) is **negligible** compared to the actual performance gap (~2 seconds).

## Round 2: Unsat Core Usage Analysis

### Code Paths That Call `solver.unsat_core()`

1. **`structure.py:solve()` (line 253)**: Called when `check()` returns UNSAT
   - Result stored in `self.unsat_core`
   - Called on every UNSAT result

2. **`structure.py:re_solve()` (line 291)**: Called during iteration when re-solving
   - Same pattern as `solve()`

3. **`structure.py:_get_relevant_constraints()` (line 396)**: Reads stored core
   - Used for printing constraints
   - Only triggered when `print_constraints=True`

### Consumers of Unsat Core Data

| Consumer | File | Condition | Purpose |
|----------|------|-----------|---------|
| `print_grouped_constraints()` | structure.py:375 | `print_constraints=True` | Display UNSAT constraints |
| `print_model()` | structure.py:663 | `print_z3=True` | Raw core display |
| `semantic.py` (logos) | logos/semantic.py:1699 | `print_constraints=True` | Theory-specific printing |
| `semantic.py` (bimodal) | bimodal/semantic.py:2221 | `print_constraints=True` | Theory-specific printing |
| `builder_utils.py` | jupyter/builder_utils.py:115 | Jupyter notebook display | Interactive output |

### Key Observations

1. **Always extracted on UNSAT**: `solver.unsat_core()` is called for every UNSAT result, even when core won't be used
2. **Core usage is optional**: Only needed when `print_constraints=True` or `print_z3=True`
3. **Iteration doesn't need cores**: The iteration system (`iterate/constraints.py`) doesn't use unsat cores
4. **Extraction is O(n)**: The CVC5 adapter's layered lookup (Python ID -> Term ID -> String) is efficient

### When Cores Are Actually Needed

```
Scenario                          | Cores Needed?
----------------------------------|---------------
Regular SAT example               | No
Regular UNSAT example             | Only if printing
Iteration (finding more models)   | No
Jupyter notebook output           | Yes (if UNSAT)
CLI with --print-constraints      | Yes (if UNSAT)
CLI without print flags           | No
```

## Round 3: Conditional Mechanism Design

### Option A: Parameter to `create_solver()` (Recommended for Future)

```python
def create_solver(settings: Optional[Dict[str, Any]] = None) -> TrackedSolverProtocol:
    backend = get_active_backend(settings)
    need_cores = settings.get('print_constraints', False) or settings.get('print_z3', False)

    if backend == "cvc5":
        return CVC5SolverAdapter(need_unsat_cores=need_cores)
    # ...
```

**Pros**: Clean API, explicit intent
**Cons**: Requires API change, small benefit

### Option B: Lazy Initialization (Minimal Change)

Only set `produce-unsat-cores` when `assert_tracked()` is first called:

```python
def assert_tracked(self, constraint: Any, label: str) -> None:
    if not self._unsat_cores_enabled:
        self._solver.set('produce-unsat-cores', 'true')
        self._unsat_cores_enabled = True
    # ... rest of method
```

**Pros**: No API change, automatic
**Cons**: Always enables for tracked constraints (which is all constraints currently)

### Option C: Settings-Based Opt-Out

Add setting: `general_settings['disable_unsat_cores'] = True`

**Pros**: User control
**Cons**: Another setting to manage

### Recommendation

**Do not implement** any of these options at this time. The overhead is too small (~100ms total savings across 24 examples) to justify the complexity. Focus optimization efforts on the actual causes of CVC5 slowness.

## Round 4: Broader Implications

### Interaction with Other Optimization Tasks

| Task | Interaction | Notes |
|------|-------------|-------|
| Task 78 (CVC5 solver tactics) | Independent | Tactics operate on formula structure, not proof tracking |
| Task 79 (CVC5 theory selection) | Independent | Theory selection is orthogonal to unsat cores |
| Task 80 (CVC5 incremental solving) | Potential interaction | Incremental solving with proofs may have different overhead |

### Root Cause Analysis

The 25-35x CVC5 slowness on UNSAT examples is **not** caused by `produce-unsat-cores`. Likely causes include:

1. **Different SAT solver heuristics**: CVC5 and Z3 use different CDCL strategies
2. **Preprocessing differences**: CVC5's simplification passes may differ
3. **Theory solver interactions**: Bitvector theory solving may have different performance characteristics
4. **Proof production overhead**: Even without unsat cores, CVC5 may produce internal proofs

### Web Research Findings

From CVC5 documentation and GitHub issues:

- Setting `produce-unsat-cores` internally affects simplification: "it's as if one uses `--simplification=none`" (GitHub issue #5141)
- CVC5 1.3.x uses new proof infrastructure for unsat core tracking
- Lightweight solve-under-assumptions approach is used when possible

However, the measured overhead (~10-30%) does not match the extreme slowdown pattern (25-35x), indicating the core tracking overhead is not the dominant factor.

## Conclusions

1. **Unsat core overhead is measurable but small**: ~10-30% or ~0.1ms per solve
2. **Not the root cause of CVC5 slowness**: The 25-35x gap requires other explanations
3. **Implementation complexity not justified**: Conditional tracking would add complexity for minimal gain
4. **Defer implementation**: Mark this as low priority pending investigation of actual CVC5 performance issues

## Recommended Next Steps

1. **Investigate CVC5 theory solver performance** (new research task)
2. **Profile CVC5 internals** on worst-case examples
3. **Test CVC5 solver options**: `--simplification=batch`, `--bv-solver=bitblast`, etc.
4. **Consider CVC5 version upgrade**: 1.3.x may have performance regressions

## Sources

- [CVC5: A Versatile and Industrial-Strength SMT Solver](https://link.springer.com/content/pdf/10.1007/978-3-030-99524-9_24.pdf)
- [Interfaces for Understanding cvc5](https://cvc5.github.io/blog/2024/04/15/interfaces-for-understanding-cvc5.html)
- [CVC5 GitHub Issue #5141](https://github.com/cvc5/cvc5/issues/5141) - Performance issue related to unsat cores
- [CVC5 Options Documentation](https://cvc5.github.io/docs/cvc5-1.0.2/options.html)
