# Implementation Summary: Bootstrap — Branch, Baseline Capture, and Oracle Relocation

- **Task**: 118 - bootstrap_branch_baseline_capture_and_oracle_reloc
- **Plan**: `specs/118_bootstrap_branch_baseline_capture_and_oracle_reloc/plans/01_branch-baseline-oracle-relocation.md`
- **Status**: COMPLETED (all 6 phases)
- **Branch**: `task-117-restore-model-checker` (not pushed)

## Overview

Executed all 6 phases of the plan across two sessions (this session resumed from a
session-limit interruption after Phase 3). Established the task branch, captured a full
before-state baseline of the live bimodal test suite plus canonical collect/help snapshots,
confirmed the restore-point SHA inventory, relocated the `bimodal_logic` oracle package from
`code/src/bimodal_logic/` to the top-level `oracle/bimodal_logic/`, reconciled all 8 in-package
test files that referenced it, and added a standalone dev-setup doc plus final collection gates.

## Phase-by-Phase Results

### Phase 1: Create Task Branch (completed prior session)
Branch `task-117-restore-model-checker` created off `master`, not pushed. Commit `618c8f5e`.

### Phase 2: Capture Pre-Change Baseline (completed this session)
Reconciled checklist state using outputs already captured by the interrupted prior session:
- `baselines/bimodal-suite-segment1.txt`: 5 failed, 534 passed in 2875.30s.
- `baselines/bimodal-suite-remainder.txt`: 279 passed in 1325.56s.
- Combined: **818 tests, 813 passed, 5 failed** (~70 min wall-clock). All 5 failures are
  pre-existing cross-oracle differential assertion mismatches in
  `test_cross_oracle_differential.py` — not introduced by this task.
- `baselines/collect-only-before.txt`: 269 tests collected, 2 pre-existing `ModuleNotFoundError`
  collection errors (missing `builder`/`output.manager` — later tasks' responsibility).
- `baselines/help-before.txt`: fails with the same missing-module error.
- Deleted two superseded, aborted partial-run files (`bimodal-suite.txt`, `bimodal-suite-full.txt`).
- Wrote `baselines/README.md` documenting the exact commands, results, and before/after
  comparison guidance for later tasks. Commit `a09f5b80`.

### Phase 3: Inventory and Confirm Restore-Point SHAs (completed prior session)
All 4 restore-point SHA/path pairs confirmed via `git ls-tree`. `baselines/restore-inventory.md`.
Commit `2cf0597e`.

### Phase 4: Relocate the Oracle Package (this session)
`git mv code/src/bimodal_logic oracle/bimodal_logic` (untracked `__pycache__` dirs removed
first); deleted the untracked, stale `code/src/bimodal_logic.egg-info/`. Commit `c8cb92ed`.

**Deviation from plan assumption**: the plan expected the oracle to be fully self-contained
("it should not import `model_checker`"). Verified this is false: `provider.py` imports
`model_checker.utils.context.isolated_z3_context`, `ModelConstraints`, `Syntax`, and
`theory_lib.bimodal` symbols; `serialization.py` imports `model_checker.solver.is_true`. This is
architecturally correct — the package is a cross-oracle differential harness that must construct
in-package semantics objects to compare against. Documented in the plan and the new
`oracle/bimodal_logic/README.md`.

### Phase 5: Reconcile In-Package Oracle-Dependent Tests (this session)
Enumerated the 8 files (`grep -rl bimodal_logic code/src/model_checker/`), matching the plan's
plan-time finding exactly. All 8 had genuine (non-docstring-only) imports.

- **Moved** (7 files, `git mv`) to `oracle/bimodal_logic/tests/`: `test_cross_oracle_differential.py`,
  `test_soundness_regression.py`, `test_boundary_regression.py`, `test_oracle_provider.py`,
  `test_oracle_interface.py`, `test_json_translation.py`, `test_fold_unfold.py`.
- **Split decision** for `test_frame_class_mapping.py`: its `TestFrameClassDeclarationConsistency`
  class had one oracle-dependent method (`test_base_means_taskframe_axioms_not_frameclassbase`,
  checks a `Z3OracleProvider` class attribute) and three in-package-only methods (test the
  `BimodalSemantics.frame_constraints` directly via `z3.Solver`, no oracle needed). Extracted only
  the oracle-dependent method to a new file, `oracle/bimodal_logic/tests/test_frame_class_declaration.py`;
  left the other three methods in place. Also reworded two docstring/comment prose mentions of the
  literal string `bimodal_logic` in the in-package file, since the plan's gate is a literal
  full-text grep, not an import-only check.
- Checked for shared helper modules/fixtures (`conftest.py`, relative imports) — none exist; each
  moved file is self-contained.
- Final gate: `grep -rl bimodal_logic code/src/model_checker/` returns nothing. Commit `31b69077`.

### Phase 6: Oracle Standalone Dev Setup and Final Gate (this session)
Added `oracle/bimodal_logic/README.md` (not `pyproject.toml` — see deviation below) documenting
layout, the `model_checker` dependency, `PYTHONPATH`-based dev setup, and the relationship to the
in-package suite. Commit `dca6e469`.

**Deviation**: chose README over a new `oracle/bimodal_logic/pyproject.toml` because
`code/pyproject.toml` still declares the `bimodal-logic` project identity (name, `bimodal-logic`
console script, `bimodal_harness.oracle_providers` entry point) pointing at the old import path.
Editing `pyproject.toml`/`MANIFEST.in` include/exclude rules is an explicit Non-Goal of this task
(New Task 4's scope per the plan) — adding a second, competing `pyproject.toml` under `oracle/`
risked packaging ambiguity, so the README documents the existing entry-point declaration's
current location instead.

**Deviation**: `PYTHONPATH=oracle` alone is insufficient for the oracle's own tests to collect
(`ModuleNotFoundError: No module named 'model_checker'`, 9 collection errors) because
`bimodal_logic/__init__.py` eagerly imports `provider` -> `serialization` -> `model_checker.solver`.
The correct, verified command is `PYTHONPATH=oracle:code/src pytest oracle/bimodal_logic/tests
--collect-only -q`, which collects **550 tests**, 0 errors. This is documented in the plan and the
README; the plan's Testing & Validation checklist item is checked off with this deviation noted
inline rather than silently passing a subtly different command.

Final verification:
- `PYTHONPATH=oracle:code/src pytest oracle/bimodal_logic/tests --collect-only -q` -> 550 tests
  collected, 0 errors.
- `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests --collect-only -q`
  -> 286 tests collected, 0 errors.
- `grep -rl bimodal_logic code/src/model_checker/` -> empty.
- `code/src/bimodal_logic/` and `code/src/bimodal_logic.egg-info/` confirmed absent.

## Plan Deviations

1. **Phase 2**: baseline suite run split into two segment files rather than one
   `bimodal-suite.txt`, and two earlier aborted single-run attempts were deleted as superseded
   (documented in `baselines/README.md`).
2. **Phase 4**: the oracle is not fully self-contained — `provider.py`/`serialization.py`
   legitimately import `model_checker` (architecturally necessary for cross-oracle diffing, not a
   defect).
3. **Phase 5**: `test_frame_class_mapping.py` required a finer-grained split (one test method
   extracted) rather than a whole-file move-or-fix-forward decision, plus a reword of two
   docstring/comment prose mentions of the literal string `bimodal_logic` to satisfy the plan's
   literal full-text grep gate.
4. **Phase 6**: chose `README.md` over `pyproject.toml` for the oracle's dev-setup file to avoid
   conflicting with `code/pyproject.toml`'s existing (out-of-scope-to-fix) `bimodal-logic` project
   declaration; documented that `PYTHONPATH=oracle:code/src` (not `oracle` alone) is required for
   the oracle's own tests to collect.

## Files Touched

**Created**:
- `specs/118_bootstrap_branch_baseline_capture_and_oracle_reloc/baselines/README.md`
- `oracle/bimodal_logic/README.md`
- `oracle/bimodal_logic/tests/test_frame_class_declaration.py`

**Moved** (`git mv`):
- `code/src/bimodal_logic/` -> `oracle/bimodal_logic/` (7 source files + `tests/__init__.py` +
  `tests/test_cli.py`)
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_cross_oracle_differential.py` ->
  `oracle/bimodal_logic/tests/test_cross_oracle_differential.py`
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_soundness_regression.py` ->
  `oracle/bimodal_logic/tests/test_soundness_regression.py`
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_boundary_regression.py` ->
  `oracle/bimodal_logic/tests/test_boundary_regression.py`
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_oracle_provider.py` ->
  `oracle/bimodal_logic/tests/test_oracle_provider.py`
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_oracle_interface.py` ->
  `oracle/bimodal_logic/tests/test_oracle_interface.py`
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_json_translation.py` ->
  `oracle/bimodal_logic/tests/test_json_translation.py`
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_fold_unfold.py` ->
  `oracle/bimodal_logic/tests/test_fold_unfold.py`

**Modified**:
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_frame_class_mapping.py` (removed one
  oracle-dependent test method + import; reworded 2 docstring/comment prose mentions)
- `specs/118_bootstrap_branch_baseline_capture_and_oracle_reloc/plans/01_branch-baseline-oracle-relocation.md`
  (checklist items, phase headings, status -> COMPLETED)

**Deleted**:
- `code/src/bimodal_logic.egg-info/` (untracked, stale build artifact)
- `specs/118_bootstrap_branch_baseline_capture_and_oracle_reloc/baselines/bimodal-suite.txt`,
  `bimodal-suite-full.txt` (superseded partial-run baseline attempts)

## Commits

| Phase | SHA | Message |
|-------|-----|---------|
| 1 | `618c8f5e` | task 118 phase 1: create task branch |
| 3 | `2cf0597e` | task 118 phase 3: inventory and confirm restore-point SHAs |
| 2 | `a09f5b80` | task 118 phase 2: capture pre-change baseline |
| 4 | `c8cb92ed` | task 118 phase 4: relocate the oracle package |
| 5 | `31b69077` | task 118 phase 5: reconcile in-package oracle-dependent tests |
| 6 | `dca6e469` | task 118 phase 6: oracle standalone dev setup and final gate |

## Definition of Done — Verified

- [x] Branch exists (`task-117-restore-model-checker`), not pushed.
- [x] Baseline artifacts saved under the task directory.
- [x] `oracle/bimodal_logic/` exists with its own tests collecting from the new location.
- [x] `grep -rl bimodal_logic code/src/model_checker/` returns nothing.

## Handoff to Downstream Tasks

- New Task 5 (root-causing the differential test failures) has its before-state baseline in
  `baselines/README.md` and can now find the 5 relevant tests at
  `oracle/bimodal_logic/tests/test_cross_oracle_differential.py`.
- New Task 2/New Task 3 (restore-point consumers) have `baselines/restore-inventory.md`.
- New Task 4 (package-identity work) should be aware that `code/pyproject.toml` still declares a
  `bimodal-logic` project pointing at the pre-move import path (`bimodal_logic.cli:run`,
  `bimodal_logic.provider:Z3OracleProvider`) — this needs correction (either repoint to
  `oracle/bimodal_logic/` via a path dependency, or migrate the metadata into a proper
  `oracle/bimodal_logic/pyproject.toml`) as part of reconciling the wheel's package-data
  include/exclude rules.
