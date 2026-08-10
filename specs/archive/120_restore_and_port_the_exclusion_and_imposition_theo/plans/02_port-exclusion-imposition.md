# Implementation Plan: Restore and Port the exclusion and imposition Theories

- **Task**: 120 - restore_and_port_the_exclusion_and_imposition_theo
- **Status**: [COMPLETED]
- **Effort**: 6 hours
- **Dependencies**: 119 (COMPLETED — core infra + logos restored and green), 118 (COMPLETED — restore-point SHA inventory)
- **Research Inputs**: specs/117_review_cli_pypi_parity_nix_flake_release/reports/02_spawn-analysis.md
- **Artifacts**: plans/02_port-exclusion-imposition.md (this file)
- **Standards**: plan-format.md; status-markers.md; artifact-management.md; tasks.md
- **Type**: python
- **Lean Intent**: false

## Overview

Restore the `exclusion` and `imposition` theories from the pre-solver-migration commit `abb3bf7d^`
and port them to the current API, then register both in `AVAILABLE_THEORIES` and drive their test
suites green. Grounding the recipe against actual source: at `abb3bf7d^` both theories **already
use** the modular `models.*` package structure (`model_checker.models.semantic.SemanticDefaults`,
`models.proposition.PropositionDefaults`, `models.structure.ModelDefaults`,
`models.constraints.ModelConstraints`), and `syntactic`/`utils` re-exports
(`Operator`, `OperatorCollection`, `ForAll`, `Exists`) are unchanged in the current API. The single
real API gap is the **solver abstraction**: pre-migration code does `import z3` and calls
`z3.is_true(...)`/`z3.is_false(...)` directly, whereas the current reference theories (`bimodal`,
`logos`) do `from model_checker import z3_shim as z3` plus
`from model_checker.solver import is_true, is_false` and call the bare `is_true(...)`/`is_false(...)`.
Definition of done: `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/exclusion -q` and
`.../imposition -q` both green, both theories registered in `AVAILABLE_THEORIES`, and no import
errors against the current `z3_shim`/`solver`/`models.*` API.

### Research Integration

The spawn-analysis report (`02_spawn-analysis.md`) isolates this as the highest-risk work in the
parent plan (pre-solver-migration porting, flagged High-Impact/High-Likelihood) and confirms the
prerequisite chain: task 119 restored `builder`/`iterate`/`jupyter`/`output` and reconciled/
registered `logos` (446-test suite green), and task 118 verified the restore-point SHAs. The
restore-inventory confirms `abb3bf7d^` contains complete `exclusion/` and `imposition/` theory
packages (paths enumerated below). Direct source inspection (this plan) narrowed the port to the
solver abstraction rather than a broad models-package migration, materially de-risking the estimate.

### Prior Plan Reference

No prior plan for this task. The parent plan's Phase 5 (exclusion) and Phase 6 (imposition) —
`specs/117_review_cli_pypi_parity_nix_flake_release/plans/01_restore-model-checker-release.md` — are
the authoritative phase-level reference; this plan refines those two phases into an executable,
source-grounded recipe rather than copying them.

### Roadmap Alignment

No ROADMAP.md consulted for this task (roadmap_flag not set). This task advances the parent
restore-model-checker-release effort by completing its two highest-risk theory-restoration phases.

## Goals & Non-Goals

**Goals**:
- Restore `exclusion` and `imposition` from `abb3bf7d^` onto the current branch.
- Port both from the pre-solver-migration API to `z3_shim` + `model_checker.solver` is_true/is_false.
- Register both in `theory_lib/__init__.py` `AVAILABLE_THEORIES`.
- Make `pytest code/src/model_checker/theory_lib/exclusion -q` and `.../imposition -q` both green.
- Commit per green sub-step.

**Non-Goals**:
- Re-deriving restore-point SHAs (use `abb3bf7d^` from the confirmed inventory).
- Package-identity work (`pyproject.toml`/`MANIFEST.in`) — that is task 121's scope (parent Phase 7).
- Widening pytest `testpaths` or the full-suite green gate — parent Phases 8-10 (downstream tasks).
- Modifying `bimodal`/`logos` — they are the reference pattern, treated as read-only ground truth.
- The documented fallback (ship logos+bimodal only) — last resort only; the goal is full restoration.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Hidden API drift beyond the solver abstraction (e.g. `ModelConstraints`/`BaseModelIterator` signature changes) | H | M | Phase 1 does a resolve-imports smoke test before any test run; diff pre-migration call sites against current `bimodal`/`logos` usage; fix per site. |
| Dead backup modules (`exclusion/semantic_backup.py`, `semantic_original.py`) carry stale imports and break collection | M | M | Phase 1 checks whether any test imports them; port if imported, otherwise remove as dead code (record removal in commit). |
| `imposition` depends on `logos` subtheory operators/semantic that may have shifted since restore | M | M | Phase 3 verifies each `logos.subtheories.*` and `logos.semantic` import against the restored logos package before porting. |
| `z3.is_true`/`z3.is_false` call-site sweep misses an occurrence, causing runtime AttributeError | M | M | Use exhaustive `grep -rn "z3.is_true\|z3.is_false"` per theory; verify zero remaining after edit; the resolve-imports + pytest run catches stragglers. |
| Test suite encodes pre-migration behavior that changed (e.g. iterator API) | M | L | Treat test failures as porting signals, not test rewrites; only adjust tests where they import moved symbols, not to mask behavior changes. |
| Porting exceeds the 6-hour budget | M | L | Exclusion recipe (Phases 1-2) is the reusable template; if imposition (Phases 3-4) overruns, the parent-documented fallback (register exclusion only, defer imposition) applies — last resort, flagged in summary. |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4 | 3 |
| 5 | 5 | 2, 4 |

Phases within the same wave can execute in parallel. This plan is sequential: the exclusion port
(Phases 1-2) establishes the reusable recipe and first touches `AVAILABLE_THEORIES`/`__init__.py`,
which the imposition port (Phases 3-4) reuses and appends to.

### Phase 1: Restore exclusion and port the solver abstraction [COMPLETED]

- **Goal:** Restore `exclusion` from history and convert all direct-z3 solver usage to the current
  `z3_shim` + `model_checker.solver` API so every module imports cleanly.
- **Tasks:**
  - [x] `git checkout abb3bf7d^ -- code/src/model_checker/theory_lib/exclusion`
  - [x] In every `.py` under `exclusion/` that does `import z3`, replace with
        `from model_checker import z3_shim as z3` (matches `bimodal`/`logos` reference).
  - [x] Sweep `grep -rn "z3\.is_true\|z3\.is_false" code/src/model_checker/theory_lib/exclusion`;
        replace each `z3.is_true(` -> `is_true(` and `z3.is_false(` -> `is_false(`, and add
        `from model_checker.solver import is_true, is_false` to each affected module. Confirm the
        sweep returns zero `z3.is_true`/`z3.is_false` occurrences afterward.
  - [x] Confirm the already-current imports resolve unchanged (no edit expected):
        `models.semantic.SemanticDefaults`, `models.proposition.PropositionDefaults`,
        `models.structure.ModelDefaults`, `models.constraints.ModelConstraints`,
        `syntactic.{Operator,OperatorCollection}`, `utils.{ForAll,Exists}`,
        `syntactic.atoms.get_atom_sort`. Fix any that fail against the current API.
        **Deviation**: `semantic/core.py` imported `WitnessSemanticError` from
        `theory_lib.errors`, which no longer exists there (the shared `errors.py`
        reparented `WitnessRegistryError`/`WitnessConstraintError`/`WitnessPredicateError`
        under `WitnessError` instead of a removed `WitnessSemanticError` — drift outside
        the anticipated solver-abstraction gap, matching the plan's "hidden API drift"
        risk row). Fixed by importing/raising `WitnessError` (the current base class) in
        place of `WitnessSemanticError`, in the theory code only; `theory_lib/errors.py`
        itself was left untouched (out of this task's `file_scope`).
  - [x] Decide `semantic_backup.py` / `semantic_original.py`: if no test or `__init__` imports them,
        remove as dead code; otherwise port them under the same recipe.
        **Result**: neither was imported anywhere in the tree; both removed as dead code
        (`semantic_backup.py` was a docstring-only stub; `semantic_original.py` was the
        1565-line pre-refactor monolith already superseded by `semantic/`).
  - [x] Resolve-imports smoke test:
        `PYTHONPATH=code/src python -c "import model_checker.theory_lib.exclusion"` succeeds.
- **Timing:** 1.5 hours
- **Depends on:** none

**Files to modify:**
- `code/src/model_checker/theory_lib/exclusion/**` (restored from history, then ported) —
  primary edits in `semantic/__init__.py`, `semantic/core.py`, `semantic/constraints.py`,
  `semantic/model.py`, `semantic/registry.py`, `operators.py`, `iterate.py`.

**Verification:**
- `git status` shows the restored `exclusion/` tree.
- `grep -rn "^import z3$" code/src/model_checker/theory_lib/exclusion` returns nothing.
- `grep -rn "z3\.is_true\|z3\.is_false" code/src/model_checker/theory_lib/exclusion` returns nothing.
- The resolve-imports `python -c` smoke test exits 0.

---

### Phase 2: Register exclusion and green its test suite [COMPLETED]

- **Goal:** Register `exclusion` in `AVAILABLE_THEORIES` and make its full test suite collect and pass.
- **Tasks:**
  - [x] Add `'exclusion',` to `AVAILABLE_THEORIES` in `code/src/model_checker/theory_lib/__init__.py`
        (with a short inline comment, matching the existing entries' style).
  - [x] Run `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/exclusion -q`; triage
        collection errors first (import/symbol moves), then runtime failures.
        **Result**: all 143 tests passed on first run (13.93s) — no failures to triage, the
        Phase 1 port left no runtime API drift beyond the one already fixed.
  - [x] For each failure, diff the failing call site against the equivalent `bimodal`/`logos`
        current-API usage; fix the theory code (not the test) unless a test imports a moved symbol.
        N/A — zero failures.
  - [x] Confirm `discover_theories()`/registration consistency: `exclusion` loads via the
        `theory_lib` public API without warnings.
  - [x] Commit: `task 120: restore and port exclusion theory (green)` (commit message adapted to
        the phase-commit convention: `task 120 phase 2: register exclusion and green its test suite`).
- **Timing:** 1.5 hours
- **Depends on:** 1

**Files to modify:**
- `code/src/model_checker/theory_lib/__init__.py` — append `exclusion` to `AVAILABLE_THEORIES`.
- `code/src/model_checker/theory_lib/exclusion/**` — targeted fixes surfaced by the test run.

**Verification:**
- `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/exclusion -q` exits 0 (all green).
- `exclusion` present in `AVAILABLE_THEORIES`; no import errors on `from model_checker.theory_lib import get_theory` for exclusion.

---

### Phase 3: Restore imposition and apply the porting recipe [COMPLETED]

- **Goal:** Restore `imposition` from history and apply the Phase 1 recipe, plus verify its
  `logos`-dependent imports against the restored logos package.
- **Tasks:**
  - [x] `git checkout abb3bf7d^ -- code/src/model_checker/theory_lib/imposition`
  - [x] Apply the Phase 1 recipe: `import z3` -> `from model_checker import z3_shim as z3`;
        `z3.is_true`/`z3.is_false` -> `is_true`/`is_false` with the `model_checker.solver` import.
        Applied to all production files plus `tests/unit/test_model.py`, whose local
        `evaluate_z3_boolean` test closures and `unittest.mock.patch('z3.is_true'/'z3.is_false')`
        targets also referenced the moved symbols; patch targets were repointed at the test
        module's own imported names (moved-symbol test adjustment, not a behavior-masking rewrite).
  - [x] Verify `imposition`'s `logos` dependencies resolve against the restored logos:
        `logos.subtheories.extensional.operators`, `...modal.operators`,
        `...counterfactual.operators`, and `logos.semantic.LogosProposition`
        (used as `Proposition` in `imposition/__init__.py` and `operators.py`).
        Verified via direct `python -c` import of every exact import statement — all resolve
        unchanged against the current logos API.
  - [x] Verify iterate imports resolve: `from model_checker.iterate.core import BaseModelIterator`
        and `from model_checker.utils import bitvec_to_substates, pretty_set_print`. Verified.
  - [x] Handle `examples_refactored/` the same as production modules (port or confirm clean).
        Confirmed clean: no `import z3` or theory_lib.errors usage in `examples_refactored/`.
  - [x] Resolve-imports smoke test:
        `PYTHONPATH=code/src python -c "import model_checker.theory_lib.imposition"` succeeds.
        **Deviations found and fixed (hidden API drift, same risk category as Phase 1's
        `WitnessSemanticError`, both beyond the anticipated solver-abstraction gap)**:
        1. `semantic/core.py` and `semantic/helpers.py` imported `ImpositionSemanticError`,
           `ImpositionOperationError`, and `ImpositionHelperError` from `theory_lib.errors`;
           unlike the `Witness*` hierarchy, these were removed entirely (not reparented) in
           the current shared `errors.py`. Fixed by importing/raising the existing `SemanticError`
           base class at each site instead, passing `theory="imposition"` explicitly (matching
           the removed subclasses' behavior) and inlining the previously auto-generated messages
           for the two `ImpositionHelperError` call sites (which took a bare function-name
           argument). `theory_lib/errors.py` itself was left untouched (out of `file_scope`).
        2. `semantic/core.py` imported the `ImpositionSemantics` protocol from `theory_lib.types`
           (aliased `ImpositionSemanticsProtocol`), which was also removed from the current
           `types.py`. The alias was unused anywhere in the file (dead import), so it was simply
           dropped from the import line rather than substituted.
- **Timing:** 1 hour
- **Depends on:** 2

**Files to modify:**
- `code/src/model_checker/theory_lib/imposition/**` (restored, then ported) — primary edits in
  `semantic/core.py`, `semantic/model.py`, `semantic/helpers.py`, `operators.py`, `iterate.py`.

**Verification:**
- `grep -rn "^import z3$" code/src/model_checker/theory_lib/imposition` returns nothing.
- `grep -rn "z3\.is_true\|z3\.is_false" code/src/model_checker/theory_lib/imposition` returns nothing.
- The resolve-imports `python -c` smoke test exits 0 (proves logos + iterate deps resolve).

---

### Phase 4: Register imposition and green its test suite [COMPLETED]

- **Goal:** Register `imposition` in `AVAILABLE_THEORIES` and make its full test suite collect and pass.
- **Tasks:**
  - [x] Add `'imposition',` to `AVAILABLE_THEORIES` in `theory_lib/__init__.py`.
  - [x] Run `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/imposition -q`; triage
        collection then runtime failures against the `logos`/`bimodal` reference usage.
        **Result**: all 110 tests passed on first run (9.90s) — no failures to triage.
  - [x] Fix theory code (not tests) except where tests import moved symbols. N/A — zero failures.
  - [x] Commit: `task 120: restore and port imposition theory (green)` (commit message adapted to
        the phase-commit convention: `task 120 phase 4: register imposition and green its test suite`).
- **Timing:** 1.5 hours
- **Depends on:** 3

**Files to modify:**
- `code/src/model_checker/theory_lib/__init__.py` — append `imposition` to `AVAILABLE_THEORIES`.
- `code/src/model_checker/theory_lib/imposition/**` — targeted fixes surfaced by the test run.

**Verification:**
- `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/imposition -q` exits 0 (all green).
- `imposition` present in `AVAILABLE_THEORIES`.

---

### Phase 5: Consolidated verification and regression check [COMPLETED]

- **Goal:** Confirm both theories are green together, both registered, and no regression to the
  existing `bimodal`/`logos` suites or the `theory_lib` public API.
- **Tasks:**
  - [x] Run both suites in one invocation:
        `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/exclusion code/src/model_checker/theory_lib/imposition -q`.
        **Result**: 253 passed in 22.09s (no cross-registration interference).
  - [x] Regression guard: `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/logos code/src/model_checker/theory_lib/bimodal -q` still green (registration edits touched shared `__init__.py`).
        **Result**: 732 passed in 154.16s (0:02:34) — no regression from the `AVAILABLE_THEORIES`
        edits.
  - [x] Confirm `AVAILABLE_THEORIES == ['bimodal', 'logos', 'exclusion', 'imposition']` (or the
        existing order with the two new entries appended) and `discover_theories()` reports no
        unregistered/orphaned theories.
        **Result**: `AVAILABLE_THEORIES == ['bimodal', 'logos', 'exclusion', 'imposition']`;
        `discover_theories() == ['bimodal', 'exclusion', 'imposition', 'logos']` (alphabetical);
        zero unregistered/orphaned theories.
  - [x] Confirm no direct-z3 residue across both theories (final grep sweep, both dirs).
        **Result**: `grep -rn "^import z3$"` and `grep -rn "z3\.is_true\|z3\.is_false"` across
        both `exclusion/` and `imposition/` return zero matches.
  - [x] Final commit if any consolidation fixes were needed:
        `task 120: verify exclusion + imposition restoration green`.
        N/A — no consolidation fixes were needed; all Phase 5 checks passed on the first run.
        Phase 5 verification itself is committed under the standard
        `task 120 phase 5: consolidated verification and regression check` convention.
- **Timing:** 0.5 hours
- **Depends on:** 2, 4

**Files to modify:**
- None expected (verification only); any fix lands in the relevant theory dir or `__init__.py`.

**Verification:**
- Combined exclusion+imposition pytest run exits 0.
- logos+bimodal regression run exits 0.
- No `import z3` / `z3.is_true` / `z3.is_false` residue in either theory dir.

## Testing & Validation

- [x] `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/exclusion -q` — green (143 passed).
- [x] `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/imposition -q` — green (110 passed).
- [x] Combined exclusion+imposition run — green (253 passed, no cross-registration interference).
- [x] logos+bimodal regression run — still green after `__init__.py` edits (732 passed).
- [x] Resolve-imports smoke tests for both theories exit 0.
- [x] Zero `import z3` / `z3.is_true` / `z3.is_false` occurrences in either theory dir.
- [x] Both theories present in `AVAILABLE_THEORIES`; `discover_theories()` consistent.

## Artifacts & Outputs

- Restored + ported `code/src/model_checker/theory_lib/exclusion/` (current-API).
- Restored + ported `code/src/model_checker/theory_lib/imposition/` (current-API).
- Updated `code/src/model_checker/theory_lib/__init__.py` with `exclusion` and `imposition`
  registered in `AVAILABLE_THEORIES`.
- Green test suites for both theories.
- Per-green-step commits on branch `task-117-restore-model-checker`.

## Rollback/Contingency

- Each theory is committed only at a green sub-step, so a failed port reverts cleanly with
  `git checkout -- code/src/model_checker/theory_lib/{exclusion|imposition}` before the commit.
- Registration is a single-line addition per theory; removing the line from `AVAILABLE_THEORIES`
  fully de-registers without touching restored source.
- **Last-resort fallback** (only if the imposition port cannot reach green within budget):
  register `exclusion` only, leave `imposition` unregistered, and hand off imposition as a
  follow-up — flagged explicitly in the implementation summary. The goal remains full restoration;
  this fallback is not to be taken pre-emptively.
