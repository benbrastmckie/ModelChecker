# Implementation Summary: Restore and Port the exclusion and imposition Theories

- **Task**: 120 - restore_and_port_the_exclusion_and_imposition_theo
- **Plan**: specs/120_restore_and_port_the_exclusion_and_imposition_theo/plans/02_port-exclusion-imposition.md
- **Status**: COMPLETED (all 5 phases)
- **Branch**: task-117-restore-model-checker

## Overview

Restored the `exclusion` and `imposition` theories from the pre-solver-migration commit
`abb3bf7d^`, ported both from direct-`z3` usage to the current `z3_shim` + `model_checker.solver`
abstraction, registered both in `theory_lib.AVAILABLE_THEORIES`, and drove both test suites green
with no regression to `logos`/`bimodal`.

## What Was Done

**Phase 1 — Restore exclusion and port the solver abstraction**
- Restored `code/src/model_checker/theory_lib/exclusion/` from `abb3bf7d^` (snapshot ->
  scoped `git checkout abb3bf7d^ -- <path>` -> `git stash pop`, to work around unrelated
  dirty state blocking a direct checkout — process note from task 119).
- Ported all `import z3` occurrences (14 files, production + tests) to
  `from model_checker import z3_shim as z3`.
- Ported `z3.is_true`/`z3.is_false` in the 3 production files that used them to bare
  `is_true`/`is_false` via `from model_checker.solver import is_true, is_false`.
- Removed `semantic_backup.py` (docstring-only stub) and `semantic_original.py`
  (1565-line pre-refactor monolith) as dead code — neither was imported anywhere.
- Fixed an unanticipated drift: `WitnessSemanticError` no longer exists in the shared
  `theory_lib/errors.py` (reparented under `WitnessError`); switched the one call site to
  `WitnessError`.
- Resolve-imports smoke test passed; 143 tests collected with 0 errors.

**Phase 2 — Register exclusion and green its test suite**
- Added `'exclusion',` to `AVAILABLE_THEORIES`.
- `pytest .../exclusion -q` — 143 passed on first run, no triage needed.

**Phase 3 — Restore imposition and apply the porting recipe**
- Restored `code/src/model_checker/theory_lib/imposition/` from `abb3bf7d^` (same
  snapshot/checkout/stash-pop process).
- Applied the same z3-import and is_true/is_false port, including
  `tests/unit/test_model.py`'s local test closures and `unittest.mock.patch('z3.is_true'|
  'z3.is_false')` targets (repointed at the test module's own imported names — a
  moved-symbol adjustment, not a behavior-masking rewrite).
- Verified every `logos`/`iterate` import used by imposition resolves unchanged against the
  current API (direct `python -c` check of the exact import statements).
- Confirmed `examples_refactored/` clean (no z3 or errors-module drift).
- Fixed two further unanticipated drifts (see Plan Deviations below):
  `ImpositionSemanticError`/`ImpositionOperationError`/`ImpositionHelperError` were removed
  entirely from `theory_lib/errors.py` (not reparented, unlike `Witness*`); and the
  `ImpositionSemantics` protocol was removed from `theory_lib/types.py`.
- Resolve-imports smoke test passed; 110 tests collected with 0 errors.

**Phase 4 — Register imposition and green its test suite**
- Added `'imposition',` to `AVAILABLE_THEORIES`.
- `pytest .../imposition -q` — 110 passed on first run, no triage needed.

**Phase 5 — Consolidated verification and regression check**
- Combined `pytest .../exclusion .../imposition -q` — 253 passed, no cross-registration
  interference.
- Regression guard `pytest .../logos .../bimodal -q` — 732 passed (154.16s), confirming the
  shared `theory_lib/__init__.py` edits caused no regression.
- `AVAILABLE_THEORIES == ['bimodal', 'logos', 'exclusion', 'imposition']`;
  `discover_theories() == ['bimodal', 'exclusion', 'imposition', 'logos']`; zero
  unregistered/orphaned theories.
- Final grep sweep: zero `import z3` / `z3.is_true` / `z3.is_false` occurrences across both
  theory directories.
- No consolidation fixes were needed.

## Test Results

| Suite | Result |
|-------|--------|
| `exclusion` | 143 passed |
| `imposition` | 110 passed |
| `exclusion` + `imposition` combined | 253 passed |
| `logos` + `bimodal` regression | 732 passed |

## Plan Deviations

The plan anticipated the solver-abstraction gap (`import z3` -> `z3_shim`;
`z3.is_true`/`z3.is_false` -> `is_true`/`is_false`) as the primary port surface, with a risk
row flagging "hidden API drift beyond the solver abstraction" as a Medium/Medium risk. Three
such drifts materialized and were fixed in theory code only (never in the shared
`theory_lib/errors.py` or `theory_lib/types.py`, both outside this task's `file_scope`):

1. **`exclusion/semantic/core.py`**: imported `WitnessSemanticError` from `theory_lib.errors`,
   which no longer exists there — the current `errors.py` reparents `WitnessRegistryError`/
   `WitnessConstraintError`/`WitnessPredicateError` under `WitnessError` instead. Fixed by
   importing/raising `WitnessError` (the current base class) at the one call site.
2. **`imposition/semantic/core.py` and `imposition/semantic/helpers.py`**: imported
   `ImpositionSemanticError`, `ImpositionOperationError`, and `ImpositionHelperError` from
   `theory_lib.errors`; these were removed entirely (not reparented) in the current shared
   `errors.py`. Fixed by using the existing `SemanticError` base class at all 4 raise sites,
   passing `theory="imposition"` explicitly and inlining the two `ImpositionHelperError` call
   sites' previously auto-generated messages (that class took a bare function-name argument
   `SemanticError` does not accept).
3. **`imposition/semantic/core.py`**: imported the `ImpositionSemantics` protocol from
   `theory_lib.types` (aliased `ImpositionSemanticsProtocol`), also removed from current
   `types.py`. The alias was unused anywhere in the file, so it was simply dropped from the
   import line.

Additionally, per the plan's explicit dead-code-decision task, `exclusion/semantic_backup.py`
and `exclusion/semantic_original.py` were removed (neither was imported anywhere in the tree)
rather than ported, consistent with the plan's stated fallback for that checklist item.

No other deviations: all 5 phases completed in full, both theories registered, both suites
green, no regression, and the last-resort fallback (register exclusion only, defer
imposition) was never needed.

## Files Modified

- `code/src/model_checker/theory_lib/exclusion/**` (restored + ported; 2 files removed as
  dead code)
- `code/src/model_checker/theory_lib/imposition/**` (restored + ported)
- `code/src/model_checker/theory_lib/__init__.py` — `exclusion` and `imposition` appended to
  `AVAILABLE_THEORIES`

## Artifacts

- Plan: `specs/120_restore_and_port_the_exclusion_and_imposition_theo/plans/02_port-exclusion-imposition.md`
- Handoffs: `specs/120_restore_and_port_the_exclusion_and_imposition_theo/handoffs/phase-{1..5}-handoff-*.md`
- This summary: `specs/120_restore_and_port_the_exclusion_and_imposition_theo/summaries/01_port-exclusion-imposition-summary.md`
