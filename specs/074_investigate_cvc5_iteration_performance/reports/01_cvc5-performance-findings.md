# Research Report: CVC5 Model Evaluation and Iteration Performance

- **Task**: 74 - Investigate CVC5 model evaluation and iteration performance bottleneck
- **Date**: 2026-03-31
- **Status**: Initial findings from debugging session

## Problem Statement

When running counterfactual examples (e.g., CF_CM_1) with `solver: cvc5` and `iterate: 2`, the model checker appears to hang. The same examples complete in <1s with Z3.

## Key Measurements

| Metric | Z3 | CVC5 | Ratio |
|--------|-----|------|-------|
| Solver check (model 1) | 0.0209s | 0.4755s | ~23x |
| Total model 1 build | ~0.6s | **18.22s** | ~30x |
| Model 2 found | 0.5s | **timeout (10s)** | -- |
| Total CF_CM_1 time | 0.78s | 24.1s | ~31x |

The solver check itself (SMT satisfiability) is only ~23x slower. But the **total model build** is ~30x slower, indicating that `model.eval()` calls during `BuildExample` construction are the primary bottleneck.

## Root Cause Analysis

### Where Time Is Spent

1. **`BuildExample` construction** (~18s with CVC5 vs ~0.6s with Z3): This evaluates every expression in the model structure -- `is_world(state)`, `verify(prop, state)`, `falsify(prop, state)` for all N=4 atoms (16 states). Each `model.eval()` call through the CVC5 pythonic API is significantly slower than Z3's.

2. **Iteration model 2 search** (times out at 10s): The `solver.check()` with exclusion constraints is called but CVC5 cannot find a second non-isomorphic model within the timeout. Z3 finds it in 0.5s.

### CVC5-Specific Issues Discovered

1. **`CVC5SolverAdapter` missing `assertions()` method**: The iteration code's `ConstraintGenerator` calls `original_solver.assertions()` to copy constraints to a persistent solver. The `CVC5SolverAdapter` did not implement this method. **Fixed**: Added `assertions()` delegation to `cvc5_adapter.py`.

2. **Solver option timing**: CVC5 requires options (like `tlimit`, `tlimit-per`) to be set **before** any assertions are added. Setting after initialization raises `RuntimeError: solver is already fully initialized`. This means per-call timeouts cannot be added to an existing solver.

3. **No `timeout` option in CVC5**: CVC5 uses `tlimit` (total wall-clock limit) and `tlimit-per` (per-check limit) instead of Z3's `timeout`. The z3_shim transparent switching doesn't cover solver option names.

4. **Cross-solver assertion copying**: Creating a new `cvc5.pythonic.Solver()` and copying assertions from another CVC5 solver works for simple cases but the iteration with exclusion constraints still times out. Reusing the original solver directly is more reliable.

## Changes Made During Investigation

### `code/src/model_checker/iterate/constraints.py`

**`_create_persistent_solver()`**: Modified to detect `CVC5SolverAdapter` and reuse its internal `_solver` directly instead of copying assertions to a new solver. For Z3, the existing copy-assertions approach is preserved. Solver-level timeouts are set appropriately for each backend.

### `code/src/model_checker/solver/cvc5_adapter.py`

**`assertions()`**: Added method that delegates to `self._solver.assertions()`. Required by the iteration system's `ConstraintGenerator`.

### `code/src/model_checker/builder/runner.py` (from task 73)

**`clear_cli_backend()` and `invalidate_all_caches()`**: Added to the per-example `finally` block to prevent solver backend settings from leaking between examples. This fix is correct but was not the primary cause of the observed hang.

## Investigation Leads for Further Research

### A. Profile CVC5 `model.eval()` Performance

The hypothesis is that each `model.eval()` call through `cvc5.pythonic` has high per-call overhead. Test:
```python
import time, cvc5.pythonic as cvc5p
# Create solver with counterfactual constraints, get model
# Time 1000 model.eval() calls vs Z3 equivalent
```

Possible causes:
- CVC5 pythonic wrapper creates new Term objects per eval
- CVC5's internal model representation requires serialization/deserialization
- The `model_completion=True` parameter triggers expensive computation in CVC5

### B. Alternative CVC5 Model Access Patterns

CVC5 may have more efficient ways to extract model values:
- Direct `model[variable]` indexing instead of `model.eval(expr)`
- Batch evaluation APIs
- Using the base CVC5 API instead of the pythonic wrapper

### C. Hybrid Z3/CVC5 Strategy for Iteration

Since the initial satisfiability check is the key value of CVC5 (different search heuristics), consider:
1. Use CVC5 for the initial `solver.check()` to find model 1
2. Extract the model values
3. Rebuild constraints in Z3 for iteration (model 2+)

This requires converting between CVC5 and Z3 expression types, or rebuilding constraints from the semantic theory.

### D. CVC5 Solver Configuration

Options that might improve performance:
- `produce-models`: Already enabled; verify it doesn't add overhead
- `simplification`: CVC5 simplification level might affect eval speed
- `bv-solver`: Different bitvector solver strategies
- `--no-debug-check`: Disable internal debug checks

### E. Z3 Shim Overhead

The `z3_shim.__getattr__` lazy loading adds one dict lookup per attribute access. For tight loops calling `z3.And()`, `z3.Not()`, `z3.Or()`, this could accumulate. Profile the shim overhead specifically.

### F. Expression Caching

If the same expressions are evaluated multiple times against the same model, caching `model.eval()` results could help. Check if `BuildExample` construction has redundant evaluations.

## Recommendations

1. **Short-term**: The timeout fixes prevent hangs. CVC5 examples with `iterate: 2` will find model 1 (slowly) and timeout gracefully on model 2.

2. **Medium-term**: Profile `BuildExample` construction to identify the exact `model.eval()` hotspot. Consider caching or batch evaluation.

3. **Long-term**: Evaluate hybrid Z3/CVC5 strategy -- use CVC5 for initial model finding where its heuristics are valuable, switch to Z3 for iteration where Z3's model evaluation is 30x faster.

## Test Commands

```bash
# Full counterfactual suite with CVC5
python code/dev_cli.py code/src/model_checker/theory_lib/logos/subtheories/counterfactual/examples.py

# Compare with Z3 (edit examples.py: change 'solver': 'cvc5' to 'solver': 'z3')
# Z3 finds 2 models for CF_CM_1 in 0.78s total

# Run solver unit tests
cd code && python -m pytest src/model_checker/solver/tests/ -v
```
