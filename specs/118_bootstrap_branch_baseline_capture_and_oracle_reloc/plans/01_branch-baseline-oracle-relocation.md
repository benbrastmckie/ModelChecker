# Implementation Plan: Bootstrap — Branch, Baseline Capture, and Oracle Relocation

- **Task**: 118 - bootstrap_branch_baseline_capture_and_oracle_reloc
- **Status**: [COMPLETED]
- **Effort**: 3 hours (plus background test wall-clock)
- **Dependencies**: None
- **Research Inputs**: specs/117_review_cli_pypi_parity_nix_flake_release/reports/02_spawn-analysis.md
- **Artifacts**: plans/01_branch-baseline-oracle-relocation.md (this file)
- **Standards**: plan-format.md; status-markers.md; artifact-management.md; tasks.md
- **Type**: python

## Overview

This task lays the foundation every downstream restore/port/release task depends on. It covers
phases 1-2 of the parent restore plan
(`specs/117_review_cli_pypi_parity_nix_flake_release/plans/01_restore-model-checker-release.md`):
create a task branch off `master` (no push), capture a documented before-state baseline (live
bimodal suite pass/fail + timing, current failing `--collect-only` and `--help` snapshots), confirm
the restore-point SHAs the later tasks will `git checkout`, and relocate the bimodal
oracle/harness layer out of the shipped `model_checker` package into a standalone top-level
`oracle/bimodal_logic/` directory. Definition of done: the branch exists, baseline artifacts are
saved under the task directory, `oracle/bimodal_logic/` exists with its own tests collecting from
their new location, and `grep -rl bimodal_logic code/src/model_checker/` returns nothing.

### Research Integration

The spawn analysis (`reports/02_spawn-analysis.md`) decomposes the 13-phase parent plan into 8
tasks along the plan's own 9-wave dependency boundaries. This task is New Task 1 ("Bootstrap"),
covers parent phases 1-2, depends on nothing, and unblocks the package-identity work (the wheel
must exclude the oracle) and the oracle-side differential testing. The oracle relocation is
called out as a pure move with no cross-API risk.

### Prior Plan Reference

The parent plan's phases 1-2 are the authoritative reference for this task. Its Phase 1 timing
is 1 hour (plus background test time) and Phase 2 is 2 hours. The restore-point SHA table
(`013a486c^` builder/, `c21b3709^` iterate/jupyter, `71ef79a1^` output/manager.py+progress/,
`abb3bf7d^` exclusion/imposition) is inventoried here but consumed by later tasks, not this one.

### Roadmap Alignment

No ROADMAP.md consulted for this dispatch (roadmap_flag not set). This task advances the
model-checker release-restoration effort tracked under parent task 117.

### Filesystem Grounding (verified at plan time)

- `code/src/bimodal_logic/` exists: `cli.py`, `__init__.py`, `provider.py`, `serialization.py`,
  `translation.py`, `tests/`.
- `code/src/bimodal_logic.egg-info/` exists (stale, to be deleted).
- `oracle/` does not yet exist at repo root.
- Current branch is `master`.
- **Key finding**: 8 in-package test files under
  `code/src/model_checker/theory_lib/bimodal/tests/unit/` reference `bimodal_logic`, not just the
  differential test named in the task description. Real (non-docstring) imports appear in:
  `test_cross_oracle_differential.py`, `test_soundness_regression.py`, `test_boundary_regression.py`,
  `test_oracle_provider.py`, `test_oracle_interface.py`, `test_json_translation.py`,
  `test_fold_unfold.py`, and `test_frame_class_mapping.py` (`from bimodal_logic.provider import
  Z3OracleProvider`). All 8 must be handled to satisfy the "zero references" gate.

## Goals & Non-Goals

**Goals**:
- Create a task branch off `master` without pushing.
- Save a durable before-state baseline (bimodal suite result/timing, `--collect-only` snapshot,
  `--help` snapshot) under the task directory.
- Confirm each restore-point SHA's source path exists via `git ls-tree <sha>^ -- <path>`.
- Move `code/src/bimodal_logic/` to `oracle/bimodal_logic/` and delete the stale egg-info.
- Relocate or fix-forward all in-package references so `code/src/model_checker/` imports zero
  `bimodal_logic`.
- Give the oracle a minimal standalone dev setup and confirm its tests collect from the new path.

**Non-Goals**:
- Executing any git-history restore (`git checkout <sha>^ -- <path>`) — that is later tasks.
- Porting exclusion/imposition or reconciling logos — later tasks.
- Editing `pyproject.toml`/`MANIFEST.in` package-data include/exclude — that is New Task 4.
- Root-causing the differential test's actual failures — that is New Task 5.
- Any `git push`, PR creation, or PyPI action (prohibited for agents).

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Baseline captured after tree mutation, so "before" state is polluted | H | M | Capture baseline (Phase 2) strictly before any relocation (Phase 4); enforce via dependency edge. |
| "Zero references" gate fails because only the differential test was moved | H | H | Phase 5 enumerates all 8 referencing files and classifies each (move vs. fix-forward) before the gate. |
| Moving a test that also legitimately exercises the in-package bimodal theory removes in-package coverage | M | M | For each file, distinguish oracle-only cross-checks (move) from docstring-only mentions (reword in place); document the classification in the summary. |
| `git mv` misses `__pycache__` or leaves import paths broken | M | M | Move with `git mv`, exclude `__pycache__`, then run `pytest --collect-only` on both trees to prove collection. |
| A restore-point SHA's parent path does not exist as expected | M | L | Phase 3 is read-only verification; a miss is recorded as a blocker for the consuming task, not fixed here. |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2, 3 | 1 |
| 3 | 4 | 2 |
| 4 | 5 | 4 |
| 5 | 6 | 5 |

Phases within the same wave can execute in parallel.

### Phase 1: Create Task Branch [COMPLETED]

- **Goal:** Establish an isolated working branch off `master` for all restoration work.
- **Tasks:**
  - [x] Confirm the working tree is in a known state (`git status --short`) and that HEAD is on
        `master`.
  - [x] Create and switch to a task branch, e.g. `git checkout -b task-117-restore-model-checker`.
  - [x] Do NOT push the branch (agent push is prohibited).
- **Timing:** 10 minutes
- **Depends on:** none
- **Files to modify:** none (branch metadata only)
- **Verification:**
  - `git branch --show-current` reports the new task branch name.
  - No remote push occurred.

### Phase 2: Capture Pre-Change Baseline [COMPLETED]

- **Goal:** Record the before-state so regressions introduced by later tasks are detectable.
- **Tasks:**
  - [x] Run the live bimodal suite once for a pass/fail + timing baseline:
        `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests -q`
        (long-running; may run in background). Save stdout/stderr and the timing to a file under
        the task directory (e.g. `baselines/bimodal-suite.txt`). **Deviation**: run split into two
        segments for operational convenience (`baselines/bimodal-suite-segment1.txt`: 5 failed,
        534 passed in 2875.30s; `baselines/bimodal-suite-remainder.txt`: 279 passed in 1325.56s).
        Combined: 818 tests, 813 passed, 5 failed (all in `test_cross_oracle_differential.py`,
        pre-existing). Two earlier aborted single-file attempts (`bimodal-suite.txt`,
        `bimodal-suite-full.txt`) were deleted as superseded.
  - [x] Snapshot the current (failing) canonical collect state:
        `PYTHONPATH=code/src pytest code/tests/ --collect-only -q` -> save to
        `baselines/collect-only-before.txt`.
  - [x] Snapshot `PYTHONPATH=code/src python -m model_checker --help` -> save to
        `baselines/help-before.txt`.
  - [x] Record the exact commands and the resulting pass/fail counts in a short
        `baselines/README.md` for before/after comparison by New Task 5.
- **Timing:** 30 minutes (plus background suite wall-clock)
- **Depends on:** 1
- **Files to modify:**
  - `specs/118_bootstrap_branch_baseline_capture_and_oracle_reloc/baselines/*` - new baseline
    artifacts (create the `baselines/` dir lazily when writing).
- **Verification:**
  - All three baseline files exist and are non-empty under the task directory.
  - The bimodal-suite file records a pass/fail count and elapsed time.

### Phase 3: Inventory and Confirm Restore-Point SHAs [COMPLETED]

- **Goal:** Confirm each restore source path exists at its recorded SHA so later tasks can
  `git checkout <sha>^ -- <path>` without re-deriving SHAs.
- **Tasks:**
  - [x] For each restore target, confirm the source path exists at the parent commit via
        `git ls-tree <sha>^ -- <path>`:
    - `013a486c^` -- `code/src/model_checker/builder/`
    - `c21b3709^` -- `code/src/model_checker/iterate/` and the `jupyter/` path
    - `71ef79a1^` -- `code/src/model_checker/output/manager.py` and `output/progress/`
    - `abb3bf7d^` -- `exclusion/` and `imposition/` theory paths
  - [x] Record each confirmed SHA -> path mapping (and any miss) in
        `baselines/restore-inventory.md` for the consuming tasks (New Task 2, New Task 3).
- **Timing:** 20 minutes
- **Depends on:** 1
- **Files to modify:**
  - `specs/118_bootstrap_branch_baseline_capture_and_oracle_reloc/baselines/restore-inventory.md`
    - new inventory artifact.
- **Verification:**
  - `restore-inventory.md` lists every SHA/path pair with a confirmed/missing status.
  - Read-only: no files under `code/` are modified by this phase.

### Phase 4: Relocate the Oracle Package [COMPLETED]

- **Goal:** Move the bimodal oracle/harness code out of the shipped package into a standalone
  top-level directory and remove the stale build artifact.
- **Tasks:**
  - [x] `git mv code/src/bimodal_logic oracle/bimodal_logic` (creates `oracle/` at repo root),
        moving `cli.py`, `__init__.py`, `provider.py`, `serialization.py`, `translation.py`, and
        the package's own `tests/`. Exclude `__pycache__` from the move. `__pycache__` dirs were
        untracked (not moved by git); removed before the move.
  - [x] Delete the stale `code/src/bimodal_logic.egg-info/`.
  - [x] Confirm the moved package's internal imports remain intact. **Deviation from plan
        assumption**: the oracle is NOT fully self-contained — `provider.py` imports
        `model_checker.utils.context.isolated_z3_context`, `model_checker.ModelConstraints`,
        `model_checker.Syntax`, and `model_checker.theory_lib.bimodal` symbols; `serialization.py`
        imports `model_checker.solver.is_true`. This is architecturally necessary: the oracle is a
        *cross-oracle differential harness* that must construct the in-package bimodal semantics
        objects to compare against. `cli.py` imports `provider` lazily (inside `main()`, not at
        module level), but `oracle/bimodal_logic/__init__.py` eagerly does
        `from .provider import Z3OracleProvider` -> `from .serialization import
        serialize_countermodel` -> `from model_checker.solver import is_true`, so merely
        importing the `bimodal_logic` package (as `tests/test_cli.py` does via `from bimodal_logic
        import cli`) requires `model_checker` to be importable. Verified: `PYTHONPATH=oracle`
        alone fails collection (`ModuleNotFoundError: No module named 'model_checker'`);
        `PYTHONPATH=oracle:code/src` collects all 18 tests successfully. Phase 6's dev-setup
        file and verification command are corrected accordingly (both path entries required, not
        `oracle` alone).
- **Timing:** 30 minutes
- **Depends on:** 2
- **Files to modify:**
  - `code/src/bimodal_logic/**` -> `oracle/bimodal_logic/**` (moved).
  - `code/src/bimodal_logic.egg-info/` (deleted).
- **Verification:**
  - [x] `oracle/bimodal_logic/` exists with the five modules plus `tests/`.
  - [x] `code/src/bimodal_logic/` and `code/src/bimodal_logic.egg-info/` no longer exist.

### Phase 5: Reconcile In-Package Oracle-Dependent Tests [COMPLETED]

- **Goal:** Ensure no file under `code/src/model_checker/` references `bimodal_logic`, by moving
  oracle-dependent tests alongside the oracle and fixing forward the rest.
- **Tasks:**
  - [x] Enumerate all in-package references:
        `grep -rl bimodal_logic code/src/model_checker/`. Confirmed 8 files under
        `theory_lib/bimodal/tests/unit/` (matches plan-time finding exactly).
  - [x] Classify each of the 8 files. Verified each of the 7 non-`test_frame_class_mapping.py`
        files has a genuine module-level import (not docstring-only) of `bimodal_logic` or
        `bimodal_logic.translation`, confirming the plan's pre-classification:
    - **Moved** (via `git mv`) to `oracle/bimodal_logic/tests/`: `test_cross_oracle_differential.py`,
      `test_soundness_regression.py`, `test_boundary_regression.py`, `test_oracle_provider.py`,
      `test_oracle_interface.py`, `test_json_translation.py`, `test_fold_unfold.py`. Several of
      these (`test_boundary_regression.py`, `test_oracle_interface.py`, `test_oracle_provider.py`,
      `test_soundness_regression.py`) also import `model_checker` directly (genuine cross-oracle
      differential tests), so they require `PYTHONPATH=oracle:code/src` (both entries) to run from
      the new location — consistent with the Phase 4 finding about `provider.py`/`serialization.py`.
    - **No files were docstring-only** — all 8 grep hits had at least one real import.
    - `test_frame_class_mapping.py`: **split decision**, finer-grained than a whole-file
      move/fix-forward. The file's `TestFrameClassDeclarationConsistency` class had two methods:
      `test_base_means_taskframe_axioms_not_frameclassbase` (imports
      `bimodal_logic.provider.Z3OracleProvider` locally, checks only a class attribute — no
      dependency on the `semantics` fixture body) and
      `test_three_taskframe_axioms_present_in_frame_constraints` (pure in-package, uses
      `BimodalSemantics.frame_constraints` + `z3.Solver`, no oracle import). Extracted only the
      first method to a new file, `oracle/bimodal_logic/tests/test_frame_class_declaration.py`;
      left the class's other three methods (`test_three_taskframe_axioms_present_in_frame_constraints`,
      `test_nullity_axiom_enforced_in_frame`, `test_converse_axiom_enforced_in_frame`) in place.
      Two docstring/comment prose mentions of the literal string `bimodal_logic` in the same file
      (module docstring line 15, class docstring) were reworded to remove the literal substring
      entirely (the plan's literal `grep -rl bimodal_logic` gate matches text, not just imports)
      while preserving the cross-reference to the oracle's test suite.
  - [x] Move any oracle-only helper modules/fixtures the relocated tests depend on alongside them.
        Checked: no `conftest.py` or relative-import helper modules exist under
        `theory_lib/bimodal/tests/unit/`; each of the 7 moved files is self-contained, so nothing
        additional needed to move.
  - [x] After moving, re-run `grep -rl bimodal_logic code/src/model_checker/` and confirm empty.
        Confirmed empty after the `test_frame_class_mapping.py` reword.
- **Timing:** 40 minutes
- **Depends on:** 4
- **Files to modify:**
  - `code/src/model_checker/theory_lib/bimodal/tests/unit/test_cross_oracle_differential.py` and
    the other oracle-dependent tests -> moved to `oracle/bimodal_logic/tests/` (or reworded).
  - Any oracle-only helper/fixture files -> moved alongside.
- **Verification:**
  - [x] `grep -rl bimodal_logic code/src/model_checker/` returns no results.
  - [x] The summary documents the move-vs-fix-forward decision for each of the 8 files.

### Phase 6: Oracle Standalone Dev Setup and Final Gate [COMPLETED]

- **Goal:** Give the relocated oracle an independent dev setup and prove both trees collect
  cleanly.
- **Tasks:**
  - [x] Add a minimal dev setup for the oracle: either `oracle/bimodal_logic/pyproject.toml` or a
        `oracle/bimodal_logic/README.md` documenting `PYTHONPATH`-based standalone development and
        the `bimodal_harness.oracle_providers` entry point, so the oracle builds/tests independently
        of the model-checker package. **Deviation**: chose `README.md` over `pyproject.toml`
        because `code/pyproject.toml` still declares the `bimodal-logic` project (name, console
        script, `bimodal_harness.oracle_providers` entry point) pointing at the old import path —
        editing `pyproject.toml`/`MANIFEST.in` is an explicit Non-Goal of this task (New Task 4's
        scope), so a second, competing `pyproject.toml` under `oracle/` was avoided to prevent
        packaging ambiguity. The README documents the existing entry-point declaration's location
        and the `PYTHONPATH=oracle:code/src` requirement (not `oracle` alone — see Phase 4/5
        findings on `__init__.py`'s eager import chain).
  - [x] Verify the oracle's own tests collect from the new location, e.g.
        `PYTHONPATH=oracle pytest oracle/bimodal_logic/tests --collect-only -q`. **Deviation**:
        `PYTHONPATH=oracle` alone fails (`ModuleNotFoundError: No module named 'model_checker'`,
        9 collection errors) because `bimodal_logic/__init__.py` eagerly imports `provider.py` ->
        `serialization.py` -> `model_checker.solver`. Verified instead with
        `PYTHONPATH=oracle:code/src pytest oracle/bimodal_logic/tests --collect-only -q`:
        **550 tests collected**, 0 errors (only pre-existing `PytestUnknownMarkWarning` for
        `slow`/`differential` marks, unrelated to the move — those markers are registered in
        `code/pyproject.toml`'s `[tool.pytest.ini_options]`, not visible when pytest's rootdir is
        the repo root).
  - [x] Verify the in-package bimodal suite still collects without the external harness:
        `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests --collect-only -q`.
        Result: **286 tests collected**, 0 errors.
  - [x] Confirm `grep -rl bimodal_logic code/src/model_checker/` remains empty (final gate).
        Confirmed empty.
- **Timing:** 30 minutes
- **Depends on:** 5
- **Files to modify:**
  - `oracle/bimodal_logic/pyproject.toml` or `oracle/bimodal_logic/README.md` - new dev-setup file.
- **Verification:**
  - [x] Oracle tests collect from `oracle/bimodal_logic/tests` (550 tests, `PYTHONPATH=oracle:code/src`).
  - [x] In-package bimodal tests collect with no `bimodal_logic` import errors (286 tests).
  - [x] `grep -rl bimodal_logic code/src/model_checker/` is empty.

## Testing & Validation

- [x] `git branch --show-current` shows the task branch; nothing was pushed.
- [x] Baseline artifacts (bimodal suite result/timing, `collect-only-before.txt`,
      `help-before.txt`, `restore-inventory.md`) exist and are non-empty under the task directory.
- [x] `oracle/bimodal_logic/` exists with its five modules, `tests/`, and a dev-setup file.
- [x] `code/src/bimodal_logic/` and `code/src/bimodal_logic.egg-info/` no longer exist.
- [x] `PYTHONPATH=oracle pytest oracle/bimodal_logic/tests --collect-only -q` collects successfully.
      **Deviation**: requires `PYTHONPATH=oracle:code/src` in practice (see Phase 6 notes above);
      `PYTHONPATH=oracle` alone fails collection.
- [x] `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests --collect-only -q`
      collects with no `bimodal_logic` import errors.
- [x] `grep -rl bimodal_logic code/src/model_checker/` returns nothing.

## Artifacts & Outputs

- `specs/118_bootstrap_branch_baseline_capture_and_oracle_reloc/plans/01_branch-baseline-oracle-relocation.md` (this plan)
- `specs/118_bootstrap_branch_baseline_capture_and_oracle_reloc/baselines/` (bimodal suite output,
  `collect-only-before.txt`, `help-before.txt`, `restore-inventory.md`, `README.md`)
- `oracle/bimodal_logic/` (relocated oracle package + tests + dev-setup file)
- `specs/118_bootstrap_branch_baseline_capture_and_oracle_reloc/summaries/01_branch-baseline-oracle-relocation-summary.md` (produced by /implement)

## Rollback/Contingency

- All work is confined to the task branch; abandoning the branch (`git checkout master`) reverts
  every change. Do not delete the branch until New Task 2 has consumed the baseline and inventory.
- The relocation is a set of `git mv` operations plus one directory deletion; if collection fails
  after the move, `git mv` back to `code/src/bimodal_logic/` restores the prior layout. Take a
  snapshot (`bash .claude/scripts/git-snapshot.sh`) before any destructive retry.
- Baseline and inventory artifacts are additive under `specs/`; they carry no rollback risk.
