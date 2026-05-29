# Implementation Plan: Fix Z3 Solver State Leakage

- **Task**: 94 - fix_z3_solver_state_leakage
- **Status**: [NOT STARTED]
- **Effort**: 4 hours
- **Dependencies**: None
- **Research Inputs**: reports/02_team-research.md, reports/01_z3-state-leakage.md
- **Artifacts**: plans/02_z3-isolation-fix.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-formats.md, tasks.md
- **Type**: z3
- **Lean Intent**: false

## Overview

Z3's global C-level context (`z3.z3._main_ctx`) persists learned lemmas, caches, and heuristic seeds across examples, causing nondeterministic results where BM_CM_3 and BM_CM_1 find countermodels after other examples but time out when run alone. The existing five scattered reset attempts (`reset_z3_context()`, `reset_solver_context()`, `Z3ContextManager`, `_initialize_z3_context()`, inline `_main_ctx = None` in `run_examples`) are all ineffective because they target the wrong attribute or use `importlib.reload()` which does not reset the C library state. This plan implements Option B2 from team research: a `contextlib.contextmanager` that swaps `z3.z3._main_ctx` to a fresh `z3.Context()` per example, providing true C-level isolation in ~25 lines across 3 core files, followed by dead code cleanup and test validation.

### Research Integration

Key findings integrated from `reports/02_team-research.md` (4-teammate synthesis):

- **Root cause**: `z3.z3._main_ctx` (the `z3.z3` submodule attribute) holds the actual C-level context; existing resets target `z3._main_ctx` or `z3.main_ctx` at the wrong module level
- **Option B2 selected**: Global `_main_ctx` swap via context manager requires changes to only 3 files (~25 lines), verified empirically by teammates B and C
- **Option A rejected**: Z3 objects cannot be pickled (`ctypes` pointer limitation), blocking the multiprocessing approach
- **AtomSort cache**: `syntactic/atoms.py` caches `DeclareSort('AtomSort')` which is context-bound; `reset_atom_sort()` must be called inside the context manager
- **Timeout sensitivity**: BM_CM_3 (`max_time: 2`) and BM_CM_1 may need timeout increases even after the fix due to Z3 MBQI nondeterminism (Z3 issue #7525)
- **Z3 maintainer guidance**: Fresh `z3.Context()` objects provide complete isolation (Z3 discussion #4992)

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md found.

## Goals & Non-Goals

**Goals**:
- Achieve true C-level Z3 context isolation between examples via `isolated_z3_context()` context manager
- Wrap `process_example()` in `runner.py` so each example runs in a fresh context
- Reset the `AtomSort` cache inside the context manager to avoid stale sort references
- Remove dead/ineffective reset infrastructure (`reset_z3_context()`, `reset_solver_context()`, `Z3ContextManager`, `_initialize_z3_context()`, inline resets in `run_examples()`)
- Validate that BM_CM_3 and BM_CM_1 produce consistent results in isolation and in sequence
- Add `conftest.py` Z3 isolation fixtures for test infrastructure

**Non-Goals**:
- Implementing multiprocessing-based isolation (Option A) -- blocked by Z3 pickling limitation
- Threading explicit `ctx=` parameters through all 23+ Z3 constructor calls (Option B1) -- unnecessary with B2
- Modifying semantic theory files (`logos/semantic.py`, `bimodal/semantic.py`) -- B2 is transparent to these
- Addressing unrelated Z3 performance tuning beyond timeout sensitivity for BM_CM_3/BM_CM_1

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| `z3.z3._main_ctx` swap breaks z3_shim lazy loading | H | L | z3_shim delegates to `z3` module which reads `_main_ctx` via `get_ctx(None)`; verified transparent by teammate B |
| AtomSort cache not fully cleared, causing Context mismatch errors | H | L | Call `reset_atom_sort()` both before yielding (clear old-context sort) and after restoring (clear new-context sort) |
| `z3.reset_params()` in `_initialize_z3_context` resets timeout set by example settings | M | M | Move `z3.reset_params()` call inside context manager before context swap, or verify it only affects global params not per-solver timeout |
| BM_CM_3/BM_CM_1 still timeout after fix due to inherent MBQI complexity | M | M | Test with increased `max_time` values (5s, 10s); document findings; adjust defaults if needed |
| Removing dead reset code introduces regressions in cvc5 backend path | M | L | `reset_solver_context()` has a cvc5 branch that is a no-op; removing it has no effect; verify cvc5 path is unaffected |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3, 4 | 2 |

Phases within the same wave can execute in parallel.

---

### Phase 1: Implement isolated_z3_context() and Wrap Runner Loop [COMPLETED]

**Goal**: Create the core context manager that swaps `z3.z3._main_ctx` to a fresh `z3.Context()` per example, and integrate it into the runner loop.

**Tasks**:
- [ ] Add `isolated_z3_context()` context manager to `code/src/model_checker/utils/context.py`:
  - Import `contextlib.contextmanager` and `z3` (the real z3 module, not z3_shim)
  - Save current `z3.z3._main_ctx` reference
  - Create fresh `z3.Context()` and assign to `z3.z3._main_ctx`
  - Call `reset_atom_sort()` to clear stale AtomSort cache
  - Yield to caller
  - In `finally` block: call `reset_atom_sort()` again, restore saved `z3.z3._main_ctx`
- [ ] In `code/src/model_checker/builder/runner.py` `run_examples()` method:
  - Import `isolated_z3_context` from `model_checker.utils.context`
  - Wrap the `self.process_example()` call (line ~766) with `with isolated_z3_context():`
  - Remove inline `z3._main_ctx = None` reset (lines ~751-752)
  - Remove the two `gc.collect()` calls flanking the inline reset (lines ~747, ~755) -- these are unnecessary with proper context isolation
- [ ] In `code/src/model_checker/builder/runner.py` `_initialize_z3_context()` method:
  - Remove the `reset_z3_context()` call (line ~318) since isolation now happens at the runner level
  - Keep `z3.reset_params()` and `z3.set_param(verbose=0)` calls (still needed for param reset)
  - Keep logging configuration (still needed)
- [ ] In `code/src/model_checker/builder/example.py` `_initialize_z3_context()` method:
  - Replace the body with `pass` (the `z3.main_ctx().solver.reset()` call always fails silently)
- [ ] Run a quick smoke test: `python -m model_checker code/src/model_checker/theory_lib/bimodal/examples.py` to verify basic functionality

**Timing**: 1.5 hours

**Depends on**: none

**Files to modify**:
- `code/src/model_checker/utils/context.py` - Add `isolated_z3_context()` context manager (~20 lines)
- `code/src/model_checker/builder/runner.py` - Wrap `process_example()` call, remove inline resets
- `code/src/model_checker/builder/example.py` - Stub out `_initialize_z3_context()` body

**Verification**:
- `isolated_z3_context()` creates a fresh `z3.Context()` with a distinct `ref()` value on each entry
- `run_examples()` wraps each `process_example()` call in the context manager
- `_initialize_z3_context()` in `example.py` no longer attempts the failing `z3.main_ctx().solver.reset()` call
- Bimodal examples run to completion without errors

---

### Phase 2: Clean Up Dead Reset Infrastructure [COMPLETED]

**Goal**: Remove the five ineffective reset mechanisms that are now superseded by `isolated_z3_context()`.

**Tasks**:
- [ ] In `code/src/model_checker/utils/context.py`:
  - Remove `Z3ContextManager` class entirely (lines ~14-48)
  - Remove `reset_z3_context()` function (lines ~50-62)
  - Remove `reset_solver_context()` function (lines ~65-104)
  - Keep `isolated_z3_context()` (added in Phase 1)
  - Update module docstring to reflect new purpose
  - Update `__init__.py` imports if `Z3ContextManager`, `reset_z3_context`, or `reset_solver_context` are exported
- [ ] In `code/src/model_checker/builder/runner.py`:
  - Remove unused `import gc` and `import importlib` at top of file (if no other usage remains)
  - Remove `gc.collect()` call in the `finally` block of `run_examples()` (line ~775)
  - Verify no remaining references to removed functions
- [ ] Search codebase for any remaining references to removed functions:
  - `grep -rn "reset_z3_context\|reset_solver_context\|Z3ContextManager" code/src/`
  - Update or remove any remaining callers
- [ ] Run bimodal examples again to verify nothing broke

**Timing**: 1 hour

**Depends on**: 1

**Files to modify**:
- `code/src/model_checker/utils/context.py` - Remove dead classes and functions
- `code/src/model_checker/utils/__init__.py` - Update exports (if needed)
- `code/src/model_checker/builder/runner.py` - Remove unused imports and gc.collect() calls
- Any other files referencing removed functions (discovered via grep)

**Verification**:
- `grep -rn "reset_z3_context\|reset_solver_context\|Z3ContextManager" code/src/` returns no results (except the new `isolated_z3_context`)
- Bimodal examples still run correctly
- No unused imports remain in modified files

---

### Phase 3: Test Validation and Timeout Tuning [COMPLETED]

**Goal**: Validate that BM_CM_3 and BM_CM_1 produce consistent results in isolation and in sequence, and tune timeouts if needed.

**Tasks**:
- [ ] Run BM_CM_3 in isolation (single example file or filtered run) and record result/timing
- [ ] Run BM_CM_1 in isolation and record result/timing
- [ ] Run the full bimodal example suite and verify BM_CM_3 and BM_CM_1 produce the same results as in isolation
- [ ] If BM_CM_3 or BM_CM_1 timeout in isolation but succeed in sequence (or vice versa), investigate:
  - Try increasing `max_time` from 2 to 5 or 10 seconds
  - Document whether the fix resolves the inconsistency or if timeout tuning is also needed
- [ ] Run the full test suite: `pytest code/tests/ -x -v` to catch any regressions
- [ ] Run logos theory examples: `python -m model_checker code/src/model_checker/theory_lib/logos/examples.py` to verify cross-theory compatibility

**Timing**: 1 hour

**Depends on**: 2

**Files to modify**:
- Bimodal example files (only if `max_time` adjustments are needed for BM_CM_3/BM_CM_1)

**Verification**:
- BM_CM_3 and BM_CM_1 produce identical results whether run alone or after other examples
- Full test suite passes with no new failures
- Logos examples run correctly (cross-theory validation)
- Any timeout changes are documented with before/after timings

---

### Phase 4: Add conftest.py Z3 Isolation Fixtures [NOT STARTED]

**Goal**: Add autouse pytest fixtures that ensure Z3 context isolation between test functions, preventing test-order-dependent failures.

**Tasks**:
- [ ] In `code/tests/conftest.py`, add an `autouse` fixture `z3_context_isolation`:
  - Import `isolated_z3_context` from `model_checker.utils.context`
  - Use the context manager to wrap each test function
  - This ensures every test gets a fresh Z3 context regardless of test ordering
- [ ] In `code/src/model_checker/builder/tests/conftest.py`, add or verify the same fixture exists (builder tests are closest to the affected code)
- [ ] In `code/src/model_checker/utils/tests/conftest.py`, add or verify the same fixture exists
- [ ] Run `pytest code/tests/ -x -v` to verify fixtures do not break existing tests
- [ ] Run `pytest code/src/model_checker/builder/tests/ -x -v` to verify builder tests pass
- [ ] Run `pytest code/src/model_checker/utils/tests/ -x -v` to verify utils tests pass

**Timing**: 0.5 hours

**Depends on**: 2

**Files to modify**:
- `code/tests/conftest.py` - Add `z3_context_isolation` autouse fixture
- `code/src/model_checker/builder/tests/conftest.py` - Add or verify isolation fixture
- `code/src/model_checker/utils/tests/conftest.py` - Add or verify isolation fixture

**Verification**:
- `z3_context_isolation` fixture appears in `pytest --fixtures` output
- All test suites pass with the new fixtures
- Running tests in random order (`pytest --randomly-seed=...` if plugin available) produces consistent results

## Testing & Validation

- [ ] BM_CM_3 produces identical results when run alone vs. after other bimodal examples
- [ ] BM_CM_1 produces identical results when run alone vs. after other bimodal examples
- [ ] Full bimodal example suite completes without errors
- [ ] Full logos example suite completes without errors
- [ ] `pytest code/tests/ -x -v` passes with no new failures
- [ ] `grep -rn "reset_z3_context\|reset_solver_context\|Z3ContextManager" code/src/` returns no hits
- [ ] No `gc.collect()` calls remain in `runner.py` that were only present for Z3 reset workarounds
- [ ] `isolated_z3_context()` creates distinct `z3.Context` objects on each invocation (verifiable via `ref()` values in debug)

## Artifacts & Outputs

- `specs/094_fix_z3_solver_state_leakage/plans/02_z3-isolation-fix.md` (this plan)
- `specs/094_fix_z3_solver_state_leakage/summaries/02_z3-isolation-fix-summary.md` (after implementation)
- Modified files:
  - `code/src/model_checker/utils/context.py` - New `isolated_z3_context()`, removed dead code
  - `code/src/model_checker/builder/runner.py` - Context manager wrapping, cleanup
  - `code/src/model_checker/builder/example.py` - Stubbed `_initialize_z3_context()`
  - `code/tests/conftest.py` - Z3 isolation fixture
  - `code/src/model_checker/builder/tests/conftest.py` - Z3 isolation fixture
  - `code/src/model_checker/utils/tests/conftest.py` - Z3 isolation fixture

## Rollback/Contingency

If the `_main_ctx` swap causes unexpected issues (Context mismatch errors, segfaults, or z3_shim incompatibilities):

1. Revert `utils/context.py` to restore `reset_z3_context()` and `reset_solver_context()`
2. Revert `runner.py` to restore inline reset logic and `gc.collect()` calls
3. Revert `example.py` `_initialize_z3_context()` body
4. The dead code cleanup (Phase 2) can be independently reverted since it only removes code
5. As a fallback, Option A (multiprocessing) could be investigated further, accepting the architectural complexity of moving all result extraction into subprocesses
