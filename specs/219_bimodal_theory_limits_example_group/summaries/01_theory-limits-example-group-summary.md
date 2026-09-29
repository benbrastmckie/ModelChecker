# Implementation Summary: Bimodal Theory-Limits Example Group

- **Task**: 219 - Add a documented THEORY-LIMITS example group to bimodal's examples.py
- **Status**: [COMPLETED]
- **Started**: 2026-09-29T04:23:00Z
- **Completed**: 2026-09-29T08:05:00Z
- **Effort**: ~3 hours
- **Dependencies**: None (tasks 216 and 217 were concurrent siblings this cycle; neither touched
  `code/src/model_checker/theory_lib/bimodal/examples.py`)
- **Artifacts**: plans/01_theory-limits-example-group.md, reports/01_theory-limits-example-group.md
- **Standards**: summary-format.md, status-markers.md, artifact-management.md, tasks.md

## Overview

Added a new `THEORY-LIMITS` section to
`code/src/model_checker/theory_lib/bimodal/examples.py` that records permanent limits of this
theory or of its verified BimodalLogic (Lean) counterpart, seeded with the stability-of-since
certificate-incompleteness result. The section carries a header comment block covering the
required six points and two real, active countermodel entries (`TL_CM_1`, `TL_CM_2`); the
`[stab]`-form schema itself is recorded in prose only, since no stability-modal operator exists
in this theory and adding one is out of scope (the blocked stability-modal-extension task's
scope).

## What Changed

- Added a `THEORY-LIMITS` banner and header comment block to `examples.py`, immediately after
  the final `BX7P_LINEAR_S_TH_example` block and before the `### DEFINE EXAMPLES AND THEORIES TO
  COMPUTE ###` banner. The header states: the group's inclusion criterion; Fact 1 (the schema is
  a genuine ZZ-time non-validity, correct and desirable) and Fact 2 (the verified side's
  certificate class for it is provably empty, a completeness gap) kept under separate labelled
  sub-headings; why this is not an axiom problem (`stab` is outside the base `Formula` language
  the `Axiom` inductive ranges over); that the limit belongs to the verified side's certificate
  design, not to this checker; the shape mechanism (a reflexivity-derived invariance axiom across
  the whole accessibility class), with the earlier temporal-asymmetry diagnosis named and marked
  superseded/refuted rather than restated; the standing semi-decision-procedure consequence,
  cross-referencing `docs/ADEQUACY.md` section 7.4; the `[stab]`-schema recorded as pending, not
  encoded; and the Box-versus-stability question answered explicitly ("same verdict, UNRELATED
  mechanism").
- Added `TL_CM_1` (`(A \Since B) -> \Box (A \Since B)`) and `TL_CM_2` (`\Past A -> \Box \Past A`)
  as real countermodel entries, each with a per-example comment following the file's existing
  convention, wired into `countermodel_examples` (new "Theory-Limits Countermodels" subsection)
  and the active `example_range`, both at `back=2, mid=1, fwd=2, max_time=10, expectation=True`.
- Extended the module docstring's naming-convention list (`TL_CM_*`) and the "Example
  Categories" list (new Theory-Limits line) in the Module Structure section.
- Created no Python object of any kind for the `(g S e) -> [stab](g S e)` schema itself; it
  remains prose-only in the header, explicitly marked pending the blocked extension task.

## Decisions

- Both `TL_CM_1`/`TL_CM_2` were added as active, currently-passing regression tests rather than
  recorded-but-inactive entries: their expected outcome ("countermodel found") is a currently
  true, independently re-verified fact about this checker, unlike the `[stab]`-form schema, whose
  certificate class is provably empty on the verified side. This distinction is stated explicitly
  in both the header and the `example_range` wiring comment.
- All five upstream citations use fully-qualified Lean declaration names only
  (`FormalSystem.Metalogic.Decidability.PlusSharingWitnessFamily.{stabSnceTarget,
  snce_share_congr, not_plusCertifies_stabSnce, not_plusCertifies_stabSnce_premise,
  not_plusValidZTime_stabSnce}`), with no `file:line` anchor, matching the task's citation
  instruction and this theory's own drift-avoidance rationale for its Compression citations.
- The plan's phases 2 and 3 (header-only, then entries-and-wiring) were kept as genuinely
  separate edits and separate commits, matching the plan's own phase separation and per-phase
  verification tiers, even though both target the same file.

## Plan Deviations

- None (implementation followed plan).

## Impacts

- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_bimodal.py` now collects 55 cases
  (53 baseline + `TL_CM_1` + `TL_CM_2`); no change was made to that file, `operators.py`,
  `KNOWN_TIMEOUT_EXAMPLES`, or `UNSTABLE_EXAMPLES`.
- The active `example_range` CLI run now reports a countermodel for both new entries alongside
  the existing examples.
- No existing example's premises, conclusions, or settings changed: the task's own committed
  diff (`545ecab9`..`cef95562`) is purely additive, with zero deletion lines in `examples.py`.

## Follow-ups

- A future BimodalLogic-side task could add the five cited declaration names to that
  repository's `lean-citation-manifest.json` seed list, giving a future ModelChecker citation
  table the same manifest-backed drift protection `docs/ADEQUACY.md`'s existing Lean-citation
  table has. Non-blocking; flagged by the research report.
- **Concurrency note for the orchestrator**: at Phase 4 gate time, a foreign, uncommitted
  modification to `example_range` (several pre-existing, unrelated entries commented out) was
  found in the shared working tree, attributable to a concurrently-running sibling process on
  this same tree (multiple independent `claude` sessions were observed running against this
  repository). It was NOT created by this task, NOT staged, and NOT committed by this task's
  work; `git diff cef95562 HEAD -- examples.py` confirms this task's own committed content is
  byte-for-byte unaffected. The uncommitted foreign edit remains in the working tree for its
  owning process (or the user) to resolve.

## References

- `code/src/model_checker/theory_lib/bimodal/examples.py` (the changed file)
- `specs/219_bimodal_theory_limits_example_group/plans/01_theory-limits-example-group.md`
- `specs/219_bimodal_theory_limits_example_group/reports/01_theory-limits-example-group.md`
- `/home/benjamin/Projects/BimodalLogic/FormalSystem/Metalogic/Decidability/PlusWitnessFamily/Incompleteness.lean`
  (read-only ground truth; not modified)
