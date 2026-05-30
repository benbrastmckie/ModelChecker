# Iterator and Example Processing Context Analysis

## Executive Summary

This research extends the initial backend leak analysis by examining the broader context of how examples, iterations, and semantic theories are processed. The analysis confirms that the proposed fix (adding `clear_cli_backend()` after each example) is correct and identifies the exact placement within the dual-loop structure.

## Processing Architecture

### Dual-Loop Structure

The example processing follows a nested loop pattern in `runner.py`:

```
run_examples() loop:
    for example_name, example_case in example_range.items():    # OUTER: Examples
        gc.collect()
        reset _main_ctx to None
        gc.collect()

        for theory_name, semantic_theory in semantic_theories.items():  # INNER: Theories
            example_copy = copy settings
            try:
                process_example(example_name, example_copy, theory_name, semantic_theory)
            finally:
                gc.collect()
```

**Key Insight**: The `_cli_override` is set inside `process_example()` via `BuildExample.__init__()`, but the cleanup (`gc.collect()`) only addresses Z3 objects, not the registry state.

### Where Backend Gets Set

The call chain that sets `_cli_override`:

```
process_example()
    -> BuildExample.__init__()
        -> _configure_solver_backend()
            -> set_backend_with_invalidation()
                -> invalidate_all_caches()  # Clears z3_shim, atoms, etc.
                -> set_cli_backend()        # Sets _cli_override
```

This happens at lines 91-111 in `example.py`:

```python
def _configure_solver_backend(self, example_case: List[Any]) -> None:
    from model_checker.solver.lifecycle import set_backend_with_invalidation
    from model_checker.solver.registry import get_active_backend

    if len(example_case) >= 3 and isinstance(example_case[2], dict):
        settings = example_case[2]
        requested_solver = settings.get("solver")
        if requested_solver and requested_solver in ("z3", "cvc5"):
            current = get_active_backend()
            if current != requested_solver:
                set_backend_with_invalidation(requested_solver)
```

### Backend Priority Chain

From `registry.py`:

```python
def get_active_backend(settings: Optional[Dict[str, Any]] = None) -> str:
    # 1. CLI flag has highest priority
    if _cli_override:
        return _cli_override

    # 2. Environment variable MODEL_CHECKER_SOLVER
    env_solver = os.environ.get("MODEL_CHECKER_SOLVER")
    if env_solver and env_solver in ("z3", "cvc5"):
        return env_solver

    # 3. Settings configuration
    if settings and "solver" in settings:
        return settings["solver"]

    # 4. Default to z3
    return "z3"
```

**The Bug**: Once `_cli_override` is set (priority 1), it returns immediately without checking per-example settings (priority 3). Examples without a solver setting that expect the default (z3) instead get the leaked override.

## Iterator Mechanism

### IteratorCore Architecture

Located in `iterate/iterator.py`, the iterator manages finding multiple distinct models:

```
IteratorCore(build_example)
    |
    +-> Settings validation (iterate count, timeout, etc.)
    +-> Initial model stored in found_models, model_structures
    +-> iterate() loop:
        |
        +-> Create ConstraintGenerator
        +-> Generate exclusion constraints for previous models
        +-> Check satisfiability
        +-> If sat: build new model structure
        +-> Check isomorphism against previous models
        +-> If distinct: add to found_models
```

### Constraint Generation

The `ConstraintGenerator` in `iterate/constraints.py`:

1. Creates a persistent solver from the original model's solver
2. Copies all assertions from the original solver
3. Adds exclusion constraints for previous models
4. Uses state difference constraints (e.g., is_world predicates)

**Important**: The constraint generator calls `original_solver.assertions()` which requires the solver adapter to support this method. The CVC5 adapter may not fully implement this (separate issue noted in prior research).

### Iteration Settings

Settings that affect iteration behavior:

| Setting | Default | Description |
|---------|---------|-------------|
| `iterate` | 1 | Number of models to find |
| `timeout` | 300 | Iteration timeout in seconds |
| `max_consecutive_invalid` | 20 | Stop after N invalid models |
| `enable_progress` | True | Show progress bars |

## Settings Flow

### Settings Layers

1. **DEFAULT_GENERAL_SETTINGS**: Hardcoded defaults
2. **Module general_settings**: From the examples.py file
3. **Example settings**: Per-example dict in example_case[2]
4. **CLI flags**: Module flags that override

### Solver Setting Sources

| Source | Priority | Example |
|--------|----------|---------|
| `--z3` / `--cvc5` CLI flags | Highest (sets _cli_override at startup) | `python -m model_checker examples.py --cvc5` |
| Per-example `solver` setting | Medium (calls set_backend_with_invalidation) | `{'solver': 'cvc5', ...}` |
| `MODEL_CHECKER_SOLVER` env var | Low | `export MODEL_CHECKER_SOLVER=cvc5` |
| Default | Lowest | `"z3"` |

### CLI Backend vs Example Backend

There are two distinct use cases:

1. **CLI Override**: User passes `--cvc5` flag to run ALL examples with CVC5
   - Set once at startup via `__main__.py` lines 291-302
   - Should persist for entire run (intentional)

2. **Per-Example Override**: Example specifies `'solver': 'cvc5'` in settings
   - Set via `set_backend_with_invalidation()` in `BuildExample.__init__()`
   - Should NOT persist to subsequent examples (bug)

The bug conflates these: per-example settings call the same `set_cli_backend()` used for CLI flags, causing the sticky behavior.

## Fix Location Analysis

### Current Location (line 765-767)

```python
# In run_examples() method
try:
    self.process_example(example_name, example_copy, theory_name, semantic_theory)
finally:
    # Force cleanup after each example to prevent state leaks
    gc.collect()
```

### Recommended Change

```python
try:
    self.process_example(example_name, example_copy, theory_name, semantic_theory)
finally:
    # Clear per-example solver override to prevent backend leak
    from model_checker.solver.registry import clear_cli_backend
    clear_cli_backend()
    # Force cleanup after each example to prevent state leaks
    gc.collect()
```

### Alternative: Clear at Theory Loop Level

The current plan places the clear in the **inner** (theory) loop. This is correct because:

1. Each theory processing for an example could set a different solver
2. Cleaning after each theory ensures no cross-theory leakage
3. The outer loop's `gc.collect()` happens before the inner loop

### Alternative: Clear at Example Loop Level

Placing the clear in the **outer** (example) loop would also work but is slightly less precise:

```python
for example_name, example_case in self.build_module.example_range.items():
    gc.collect()
    # ... reset context ...
    for theory_name, semantic_theory in self.build_module.semantic_theories.items():
        try:
            self.process_example(...)
        finally:
            gc.collect()
    # Clear at example level instead
    from model_checker.solver.registry import clear_cli_backend
    clear_cli_backend()
```

**Recommendation**: Keep the plan's inner-loop placement for finer-grained cleanup.

## Plan Assessment

### Current Plan Review

The plan at `plans/01_clear-cli-backend.md` proposes:

1. Phase 1: Add `clear_cli_backend()` call in finally block (lines 765-767)
2. Phase 2: Verify with counterfactual examples

### Assessment: Plan is Correct

The plan correctly identifies:
- The root cause (_cli_override persistence)
- The fix location (finally block in runner.py)
- The existing API to use (clear_cli_backend)
- The verification test case (counterfactual examples)

### Suggested Improvements

1. **Import optimization**: Move the import outside the finally block to the top of the method or module level. The current plan imports inside the finally block, which works but adds minor overhead per example.

2. **Diagnostic logging**: Consider adding a debug log when clearing:
   ```python
   logger.debug(f"Clearing per-example solver override after {example_name}/{theory_name}")
   ```

3. **Documentation**: Add a comment explaining WHY the clear is needed, not just what it does:
   ```python
   # Clear per-example solver override.
   # Examples may set solver via settings['solver'], which calls set_backend_with_invalidation().
   # Without clearing, this "leaks" to subsequent examples that expect the default.
   clear_cli_backend()
   ```

## Related Observations

### CVC5 Adapter Compatibility Issue

The prior research noted that `CVC5SolverAdapter` lacks an `.assertions()` method. This is used by:

1. `iterate/constraints.py` line 57: `original_solver.assertions()`
2. Progress tracking code that counts constraints

This is a **separate issue** but affects CVC5 usability with iteration. Recommend tracking as a follow-up task.

### Other Backend Reset Locations

The codebase has other places that manipulate backend state:

1. `__main__.py` lines 291-302: CLI flag handling (intentional, sets at startup)
2. `theory_lib/logos/comparison.py` line 155: Comparison testing utilities
3. Various test files: Test setup/teardown

None of these are affected by the fix since they either:
- Set the backend intentionally for the entire run
- Are test utilities with their own cleanup

## Conclusion

The proposed plan is sound. The only suggested improvements are:

1. Move import to module level for minor performance gain
2. Add explanatory comment for maintainability

The fix correctly addresses the root cause (sticky `_cli_override`) at the appropriate location (after each theory-example pair processing) using the existing API (`clear_cli_backend()`).

## Files Referenced

| File | Purpose |
|------|---------|
| `builder/runner.py` | Main example processing loop, fix location |
| `builder/example.py` | BuildExample initialization, where backend gets set |
| `solver/registry.py` | Backend registry with `_cli_override` and clear function |
| `solver/lifecycle.py` | Cache invalidation hooks |
| `iterate/iterator.py` | Iteration loop for finding multiple models |
| `iterate/constraints.py` | Constraint generation for model exclusion |
| `z3_shim.py` | Backend abstraction layer |

## Test Verification

The verification command from the plan is correct:

```bash
python code/dev_cli.py code/src/model_checker/theory_lib/logos/subtheories/counterfactual/examples.py
```

Expected behavior after fix:
- CF_CM_1: Uses CVC5 (has `'solver': 'cvc5'` in settings)
- CF_CM_2: Uses Z3 (no solver setting, should default to z3)
- No `AttributeError: module 'cvc5.pythonic' has no attribute 'reset_params'`
