# Implementation Plan: Fix Per-Example Solver Backend Leak (Revised)

- **Task**: 73 - Fix per-example solver backend leaking across examples via _cli_override
- **Status**: [NOT STARTED]
- **Effort**: 0.5 hours
- **Dependencies**: None
- **Research Inputs**: reports/01_backend-leak-analysis.md, reports/02_iterator-context-analysis.md
- **Artifacts**: plans/02_clear-cli-backend-revised.md (this file)
- **Supersedes**: plans/01_clear-cli-backend.md
- **Standards**: plan-format.md, status-markers.md, artifact-formats.md, tasks.md
- **Type**: z3

## Overview

The `_cli_override` variable in `solver/registry.py` persists across examples, causing solver settings from one example to leak to subsequent examples. When CF_CM_1 sets `solver: cvc5`, CF_CM_2 (which has no solver setting) incorrectly inherits CVC5 instead of defaulting to Z3. The fix is a single-line addition in `runner.py` to call `clear_cli_backend()` after each example processes.

### Research Integration

**From 01_backend-leak-analysis.md**:
- Root cause: `set_backend_with_invalidation()` sets `_cli_override` which never gets cleared
- Recommended fix: Add `clear_cli_backend()` call in finally block of `runner.py`
- Existing API: `clear_cli_backend()` already exists in `solver/registry.py`

**From 02_iterator-context-analysis.md**:
- Dual-loop structure confirmed: outer=examples, inner=theories
- Fix placement in inner loop's finally block is correct
- Backend priority: `_cli_override` > env var > settings > default
- **Improvements identified**:
  1. Move import to module level for minor performance gain
  2. Add explanatory comment for maintainability

## Goals & Non-Goals

**Goals**:
- Ensure each example starts with a clean solver backend state
- Prevent solver settings from leaking between examples
- Use existing API (`clear_cli_backend()`) for minimal code change
- Import at module level for cleaner code

**Non-Goals**:
- Fixing the CVC5SolverAdapter missing `.assertions()` method (separate issue)
- Refactoring the backend selection architecture
- Adding new configuration options

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Clearing backend breaks CLI override behavior | High | Low | CLI override from `--cvc5` flag only set at startup; per-example overrides are what we're clearing |
| Other code relies on sticky override | Medium | Low | Research confirmed no other consumers of sticky behavior |

## Implementation Phases

### Phase 1: Add clear_cli_backend() Call [NOT STARTED]

**Goal**: Clear the CLI backend override after each example processes to prevent leak

**Tasks**:
- [ ] Add import at module level in `code/src/model_checker/builder/runner.py`
- [ ] Add `clear_cli_backend()` call in the existing finally block (line ~767)
- [ ] Add explanatory comment

**Timing**: 15 minutes

**Files to modify**:
- `code/src/model_checker/builder/runner.py`

**Changes**:

1. **Add import at module level** (near other solver imports, ~line 30):
```python
from model_checker.solver.registry import clear_cli_backend
```

2. **Modify finally block** (line ~765-767):
```python
# Current:
finally:
    # Force cleanup after each example to prevent state leaks
    gc.collect()

# After:
finally:
    # Clear per-example solver override.
    # Examples may set solver via settings['solver'], which calls set_backend_with_invalidation().
    # Without clearing, this "leaks" to subsequent examples that expect the default (z3).
    clear_cli_backend()
    # Force cleanup after each example to prevent state leaks
    gc.collect()
```

**Verification**:
- Import statement works (no circular dependency)
- Code compiles without syntax errors

---

### Phase 2: Verification [NOT STARTED]

**Goal**: Verify the fix works with the counterfactual examples

**Tasks**:
- [ ] Run the counterfactual examples that reproduce the bug
- [ ] Verify CF_CM_1 runs with CVC5 (has `solver: cvc5`)
- [ ] Verify CF_CM_2 runs with Z3 (no solver setting, should default)
- [ ] Confirm no `reset_params` AttributeError

**Timing**: 15 minutes

**Command**:
```bash
python code/dev_cli.py code/src/model_checker/theory_lib/logos/subtheories/counterfactual/examples.py
```

**Expected Results**:
- CF_CM_1: Uses CVC5 backend (from `solver: cvc5` setting)
- CF_CM_2: Uses Z3 backend (default, no solver setting)
- No `AttributeError: module 'cvc5.pythonic' has no attribute 'reset_params'`

**Verification**:
- Both examples complete without backend-related errors
- Each example uses the correct solver backend

## Testing & Validation

- [ ] Run counterfactual examples: `python code/dev_cli.py code/src/model_checker/theory_lib/logos/subtheories/counterfactual/examples.py`
- [ ] Verify CF_CM_1 uses CVC5, CF_CM_2 uses Z3
- [ ] No `reset_params` AttributeError
- [ ] Existing tests still pass (if any exist for runner.py)

## Artifacts & Outputs

- plans/02_clear-cli-backend-revised.md (this file)
- summaries/02_clear-cli-backend-summary.md (after implementation)

## Rollback/Contingency

If the fix causes issues:
1. Remove the import and `clear_cli_backend()` call from `runner.py`
2. The codebase returns to previous behavior
3. Consider Option C from research (separate `_settings_backend` variable) as alternative

## Changes from Previous Plan (v1)

| Aspect | v1 (01_clear-cli-backend.md) | v2 (this file) |
|--------|------------------------------|----------------|
| Import location | Inside finally block | Module level |
| Comment | Brief | Detailed explanation of WHY |
| Research inputs | 1 report | 2 reports |
