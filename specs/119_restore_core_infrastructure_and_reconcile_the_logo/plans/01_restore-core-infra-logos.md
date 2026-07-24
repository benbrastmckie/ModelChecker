# Implementation Plan: Restore Core Infrastructure and Reconcile the logos Theory

- **Task**: 119 - restore_core_infrastructure_and_reconcile_the_logos
- **Status**: [IMPLEMENTING]
- **Effort**: 4.5 hours
- **Dependencies**: 118 (COMPLETED) — task branch `task-117-restore-model-checker` exists and is checked out; restore-point SHAs confirmed in `specs/118_bootstrap_branch_baseline_capture_and_oracle_reloc/baselines/restore-inventory.md`; the `bimodal_logic` oracle has been relocated to top-level `oracle/bimodal_logic/`.
- **Research Inputs**: specs/117_review_cli_pypi_parity_nix_flake_release/reports/02_spawn-analysis.md
- **Artifacts**: plans/01_restore-core-infra-logos.md (this file)
- **Standards**:
  - .claude/context/formats/plan-format.md
  - .claude/rules/artifact-formats.md
  - .claude/rules/state-management.md
  - .claude/rules/git-workflow.md
  - .claude/rules/pr-prohibition.md
- **Type**: python

## Overview

This task executes phases 3-4 of the parent restore plan (`specs/117_review_cli_pypi_parity_nix_flake_release/plans/01_restore-model-checker-release.md`): restore the deleted general-purpose `model_checker` infrastructure (`builder/`, `iterate/`, `jupyter/`, `output/manager.py`, `output/progress/`) from concrete git-history restore points, reconcile any imports broken since those (post-solver-migration) restore points, and make the in-tree `logos` theory functional and registered in `AVAILABLE_THEORIES`. All restore sources are post-solver-migration commits, so the restored modules target an API matching current HEAD and breakage should be minimal (fix-forward, not port). Definition of done: `model_checker.builder`, `model_checker.iterate`, `model_checker.output.manager` import cleanly; `PYTHONPATH=code/src python -m model_checker --help` and `python code/dev_cli.py --help` run without `ModuleNotFoundError`; `logos` (and its retained subtheories) are registered in `AVAILABLE_THEORIES` with the first-order subtheory removal (`e9734a27`) intact; and `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/logos -q` collects and passes.

### Research Integration

The spawn analysis (`reports/02_spawn-analysis.md`, from parent task 117) established the scope and dependency rationale for this task: `builder/`, `iterate/`, `jupyter/`, and `output/manager.py`/`output/progress/` must exist before `logos` (which imports `model_checker.iterate`) can be reconciled and registered, and before any theory-registration work in later tasks can proceed. The restore-point SHAs and the exact source-path contents at each `<sha>^` were independently verified read-only by task 118 (`baselines/restore-inventory.md`): all six SHA/path pairs resolved successfully, so each `git checkout <sha>^ -- <path>` in this plan has a confirmed source. The parent plan's restore-points table classifies every module in this task's scope as "Post-migration — clean restore" (for `builder`/`iterate`/`jupyter`/`output`) or "Post-migration — fix imports + register" (for `logos`) — none require the pre-migration porting work that is isolated in the separate exclusion/imposition task.

### Prior Plan Reference

No prior plan for this task. The parent plan (phases 3-4) is the authoritative reference for phase-level detail; this plan decomposes those two parent phases into four smaller, independently verifiable phases and is not a copy of the parent.

### Roadmap Alignment

`specs/ROADMAP.md` is an empty template (no items) and no roadmap flag was passed; this plan adds no roadmap phases.

### Concrete Git Restore Points (this task's scope)

Restore each deleted module from the commit immediately preceding its deletion, using the non-destructive path-checkout form `git checkout <sha>^ -- <path>` (never the pathspec-discard form `git checkout -- <path>`). All confirmed present at `<sha>^` by task 118's inventory:

| Module | Restore command | Solver-abstraction status |
|--------|-----------------|---------------------------|
| `model_checker/builder/` (20 entries) | `git checkout 013a486c^ -- code/src/model_checker/builder` | Post-migration — clean restore |
| `model_checker/iterate/` (13 entries) | `git checkout c21b3709^ -- code/src/model_checker/iterate` | Post-migration — clean restore |
| `model_checker/jupyter/` (full package) | `git checkout c21b3709^ -- code/src/model_checker/jupyter` | Post-migration — clean restore |
| `model_checker/output/manager.py`, `output/progress/` | `git checkout 71ef79a1^ -- code/src/model_checker/output/manager.py code/src/model_checker/output/progress` | Post-migration — clean restore |
| `theory_lib/logos/` | keep in-tree | Post-migration — fix imports + register |

## Goals & Non-Goals

**Goals**:
- Restore `builder/`, `iterate/`, `jupyter/`, `output/manager.py`, and `output/progress/` into `code/src/model_checker/` from their confirmed git-history restore points.
- Reconcile imports so `model_checker.builder`, `model_checker.iterate`, and `model_checker.output.manager` import cleanly and both CLI entry points (`python -m model_checker --help`, `python code/dev_cli.py --help`) run without `ModuleNotFoundError`.
- Reconcile `theory_lib/logos/` imports (now that `model_checker.iterate` is restored), confirm the first-order removal is intact, and register `logos` and its retained subtheories in `AVAILABLE_THEORIES`.
- Get the `logos` test suite to collect and pass.
- Commit per green sub-step throughout.

**Non-Goals**:
- Restoring or porting `exclusion`/`imposition` (pre-migration; separate downstream task).
- Restoring the first-order subtheory (its removal in `e9734a27` is intentional and preserved).
- Package-identity work (`pyproject.toml`/`MANIFEST.in`) or pytest `testpaths` widening (separate downstream task).
- Any `git push`, PR creation, or PyPI action (user-only, per `pr-prohibition.md`).
- Rewriting `builder`/`iterate`/`logos` semantics beyond what is required to make the restored/registered code import and pass on the current API.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Restored `builder`/`iterate` reference modules that changed since the (post-migration) restore point, causing import breakage. | M | M | Run import smoke tests immediately after restore; fix-forward each broken reference against current module paths rather than reverting unrelated improvements. Because sources are post-migration, breakage is expected to be minimal. |
| Restored infrastructure references the `bimodal_logic` oracle that task 118 relocated to top-level `oracle/`. | M | L | Grep restored modules for `bimodal_logic` imports; repoint or remove any residual reference. The oracle move is a task-118 fact this task must respect, not re-do. |
| `logos` has dangling references to the removed first-order subtheory. | M | L | Explicitly grep `theory_lib/logos/` for first-order references before registration; confirm `e9734a27` removal is intact and no import resolves to a deleted first-order module. |
| `git checkout <sha>^ -- <path>` accidentally run in the pathspec-discard form, discarding working-tree changes. | H | L | Always include the `<sha>^` revision argument; never use `git checkout -- <path>`. Restores stage the paths; review with `git status --short` before committing. |
| Registering `logos` in `AVAILABLE_THEORIES` surfaces cross-theory import coupling. | M | L | Register incrementally and re-run the `logos` import + test smoke check immediately after editing `theory_lib/__init__.py`; keep shared imports pointing at current module paths. |
| `logos` test suite has a long or Z3-heavy runtime that stalls iteration. | L | M | Run targeted `logos` subsets during reconciliation; reserve the full `pytest code/src/model_checker/theory_lib/logos -q` run for the phase-4 green gate. |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4 | 3 |

Phases within the same wave can execute in parallel. This plan is fully sequential (one phase per wave): each phase's verification is a hard precondition for the next (the CLI cannot be reconciled before the modules exist; `logos` imports cannot resolve before `iterate` is restored and reconciled; `logos` cannot be registered/tested before its imports resolve).

### Phase 1: Restore Core Infrastructure Modules from Git History [COMPLETED]

- **Goal:** Bring the deleted `builder/`, `iterate/`, `jupyter/`, `output/manager.py`, and `output/progress/` back into the working tree from their confirmed restore points, as a clean staged restore committed before any reconciliation.
- **Tasks:**
  - [x] Confirm the working tree is on branch `task-117-restore-model-checker` and clean enough to stage the restores (`git status --short`).
  - [x] `git checkout 013a486c^ -- code/src/model_checker/builder`
  - [x] `git checkout c21b3709^ -- code/src/model_checker/iterate code/src/model_checker/jupyter`
  - [x] `git checkout 71ef79a1^ -- code/src/model_checker/output/manager.py code/src/model_checker/output/progress`
  - [x] Verify the restored trees match task 118's inventory (`builder/` 20 entries, `iterate/` 13 entries, `jupyter/` full package, `output/manager.py` present, `output/progress/` 6 entries) via `git status --short` / `ls`. **Deviation**: actual git-history entry counts are 22 for `builder/` and 14 for `iterate/` (confirmed via `git ls-tree <sha>^`), not the 20/13 the inventory doc reported — the inventory's prose enumeration undercounted `validation.py`/`z3_utils.py` (builder) and one file (iterate); the restore itself is a byte-for-byte match to git history, so this is a documentation discrepancy in the upstream inventory, not a restore defect.
  - [x] Commit the raw restore (scoped to the restored paths only): `task 119 phase 1: restore builder, iterate, jupyter, output infrastructure`.
- **Timing:** 1 hour
- **Depends on:** none
- **Files to modify:**
  - `code/src/model_checker/builder/` — restored (20 files)
  - `code/src/model_checker/iterate/` — restored (13 files)
  - `code/src/model_checker/jupyter/` — restored (full package)
  - `code/src/model_checker/output/manager.py`, `code/src/model_checker/output/progress/` — restored
- **Verification:**
  - All five restore targets present on disk and staged; `git status --short` shows only the intended restored paths.
  - Entry counts match `restore-inventory.md`.

### Phase 2: Reconcile Core Infrastructure Imports and Verify CLI [COMPLETED]

- **Goal:** Make the restored infrastructure import cleanly against the current post-solver-migration API and get both `model-checker` CLI entry points running without `ModuleNotFoundError`.
- **Tasks:**
  - [x] Run import smoke tests: `PYTHONPATH=code/src python -c "import model_checker.builder"`, `... import model_checker.iterate`, `... import model_checker.output.manager` (and `model_checker.output.progress`). **Result**: `builder`/`iterate`/`output.progress` imported cleanly immediately; `output.manager` initially raised `ModuleNotFoundError: No module named 'model_checker.output.config'`.
  - [x] For each `ModuleNotFoundError`/`ImportError`, fix-forward the reference against the current module layout (e.g. `z3_shim`, `model_checker.solver`, modular `models.*` package) — do not revert unrelated post-restore improvements. **Deviation**: the root cause was not an API-name drift but four additional dependency files (`config.py`, `constants.py`, `helpers.py`, `errors.py`) deleted in the exact same commit (`71ef79a1`) as `manager.py`, which the plan's restore-points table did not list. Restored all four from the same restore point `71ef79a1^` (not a rewrite — a same-source restore extension), after which `manager.py` imports cleanly with no further code changes needed.
  - [x] Grep the restored modules for any `bimodal_logic` (relocated oracle) references; repoint or remove them so no restored module imports the moved oracle. Grep was clean (no matches) across `builder/`, `iterate/`, `jupyter/`, `output/`.
  - [x] Verify `PYTHONPATH=code/src python -m model_checker --help` runs cleanly. Confirmed, exit 0.
  - [x] Verify `python code/dev_cli.py --help` runs cleanly. Confirmed, exit 0.
  - [x] Commit per green sub-step (each module importing cleanly / each CLI entry point running is a green milestone): `task 119 phase 2: reconcile infrastructure imports, CLI --help green`.
- **Timing:** 1.5 hours
- **Depends on:** 1
- **Files to modify:**
  - `code/src/model_checker/builder/` — import fixes as needed
  - `code/src/model_checker/iterate/` — import fixes as needed
  - `code/src/model_checker/output/manager.py`, `code/src/model_checker/output/progress/` — import fixes as needed
  - `code/src/model_checker/jupyter/` — import fixes only if it blocks CLI import (jupyter is an optional extra; deep reconciliation is out of scope)
- **Verification:**
  - All four target modules import without error.
  - Both `python -m model_checker --help` and `python code/dev_cli.py --help` exit 0 with no `ModuleNotFoundError`.
  - No restored module imports `bimodal_logic`.

### Phase 3: Reconcile the logos Theory Imports [COMPLETED]

- **Goal:** Make `theory_lib/logos/` import cleanly now that `model_checker.iterate` is restored, and confirm the first-order removal is intact with no dangling references.
- **Tasks:**
  - [x] Confirm `theory_lib/logos/__init__.py`'s `from .iterate import ...` / `model_checker.iterate` imports now resolve; run `PYTHONPATH=code/src python -c "import model_checker.theory_lib.logos"`. **Result**: succeeded immediately, zero code changes needed — phase 2's `iterate` restore was sufficient.
  - [x] Fix any residual `logos` import paths that break against the current API (fix-forward). **Deviation**: no fix-forward was needed; `logos` had no residual import breakage against current HEAD's API.
  - [x] Grep `theory_lib/logos/` for references to the removed first-order subtheory; confirm the `e9734a27` removal is intact and no import resolves to a deleted first-order module. Remove any dangling reference found. Grep for `first_order`/`first-order`/`firstorder` (case-insensitive) across `theory_lib/logos/` returned zero matches; `subtheories/` contains only `constitutive`, `counterfactual`, `extensional`, `modal`, `relevance`, `spatial` (no `first_order` directory). `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/logos --collect-only -q` collects 446 tests with zero errors, confirming no dangling reference at test-collection time either.
  - [x] Commit per green sub-step: `task 119 phase 3: reconcile logos imports, first-order removal verified`.
- **Timing:** 1 hour
- **Depends on:** 2
- **Files to modify:**
  - `code/src/model_checker/theory_lib/logos/` — import path fixes; removal of any dangling first-order reference
- **Verification:**
  - `import model_checker.theory_lib.logos` succeeds with no error.
  - No reference to the removed first-order subtheory remains (grep is clean); the `e9734a27` removal is confirmed intact.

### Phase 4: Register logos and Green Its Test Suite [NOT STARTED]

- **Goal:** Register `logos` and its retained subtheories in `AVAILABLE_THEORIES` and get the `logos` test suite to collect and pass.
- **Tasks:**
  - [ ] Register `logos` (and its retained subtheories) in `theory_lib` `AVAILABLE_THEORIES` (`code/src/model_checker/theory_lib/__init__.py`), following the existing `bimodal` registration as the pattern.
  - [ ] Re-run the `logos` import smoke test after editing `theory_lib/__init__.py` to catch any coupling surfaced by registration.
  - [ ] Get `theory_lib/logos/tests/` to collect: `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/logos --collect-only -q` reports zero collection errors.
  - [ ] Run the suite to green: `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/logos -q`; fix-forward any residual failures within `logos`'s scope.
  - [ ] Commit per green sub-step: `task 119 phase 4: register logos, logos test suite green`.
- **Timing:** 1 hour
- **Depends on:** 3
- **Files to modify:**
  - `code/src/model_checker/theory_lib/__init__.py` — add `logos` to `AVAILABLE_THEORIES`
  - `code/src/model_checker/theory_lib/logos/` — residual test/import fixes as needed
- **Verification:**
  - `logos` appears in `AVAILABLE_THEORIES`.
  - `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/logos -q` collects and passes (or with only documented, justified skips/xfails).

## Testing & Validation

- [ ] `PYTHONPATH=code/src python -c "import model_checker.builder"` succeeds.
- [ ] `PYTHONPATH=code/src python -c "import model_checker.iterate"` succeeds.
- [ ] `PYTHONPATH=code/src python -c "import model_checker.output.manager"` succeeds.
- [ ] `PYTHONPATH=code/src python -m model_checker --help` runs without `ModuleNotFoundError`.
- [ ] `python code/dev_cli.py --help` runs without `ModuleNotFoundError`.
- [ ] `PYTHONPATH=code/src python -c "import model_checker.theory_lib.logos"` succeeds.
- [ ] `logos` is registered in `AVAILABLE_THEORIES`.
- [ ] `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/logos -q` collects and passes.
- [ ] No restored module imports the relocated `bimodal_logic` oracle; no `logos` reference to the removed first-order subtheory remains.

## Artifacts & Outputs

- plans/01_restore-core-infra-logos.md (this file)
- summaries/01_restore-core-infra-logos-summary.md (on completion)
- Restored source under `code/src/model_checker/`: `builder/`, `iterate/`, `jupyter/`, `output/manager.py`, `output/progress/`.
- Reconciled `code/src/model_checker/theory_lib/logos/`.
- Updated `code/src/model_checker/theory_lib/__init__.py` (`logos` registered in `AVAILABLE_THEORIES`).

## Rollback/Contingency

- All work occurs on the `task-117-restore-model-checker` branch off `master`; if the restore proves unworkable, the branch can be abandoned without touching `master`.
- Each phase commits per green sub-step, so a failed phase can be reverted independently via `git revert` of its commits without losing earlier restored modules.
- If `logos` reconciliation (phases 3-4) exceeds budget, the restored infrastructure (phases 1-2) is still a self-contained green milestone that unblocks downstream tasks; `logos` registration can be deferred to a follow-up rather than blocking the infrastructure restore — but this is a fallback, not the plan.
- No PyPI upload or `git push` occurs during implementation.
