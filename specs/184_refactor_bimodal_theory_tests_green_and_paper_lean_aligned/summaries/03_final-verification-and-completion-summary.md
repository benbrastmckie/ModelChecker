# Implementation Summary: Witness-family certificate redesign - final verification and completion

- **Task**: 184 - Redesign the bimodal theory around witness-family certificates (discrete Z-time)
- **Status**: [COMPLETED]
- **This dispatch covers**: Phases 22-24 (documentation rewrite, `development`-marker removal and
  gating re-enablement, final verification). Phases 1-21 are covered by three prior summaries
  (`01_certificate-foundation-layer-summary.md`, `01_constraint-generation-groundwork-summary.md`,
  `02_semantic-core-structure-operators-iterate-summary.md`) and their own phase handoffs; this
  document does not re-derive that work, only closes the task out.
- **Artifacts**: `plans/01_witness-family-certificate-redesign.md` (Phases 1-24 all closed)
- **Standards**: summary-format.md, status-markers.md, artifact-management.md, tasks.md

## Overview

The bimodal theory's semantic core is redesigned around witness-family certificate search over
discrete (Z) time, replacing the retired window-and-abundance Z3 encoding outright. This dispatch
closes the task: documentation rewritten for the certificate design (Phase 22), the `development`
pytest marker retired and bimodal restored to gating status (Phase 23), and the whole repository
verified green under the real gating selections with the redesign's claims measured, not asserted
(Phase 24).

**The task is complete with two carried-forward exclusions**, both from earlier phases, neither
silently absorbed into this "complete" verdict:

1. **Phase 15 `[COMPLETED WITH EXCLUSIONS]`**: isomorphism rejection during iteration is
   exact-difference, not rotation/permutation-invariant, and — discovered more sharply during
   Phase 22's documentation work — **`iterate: N > 1` currently crashes outright** via the
   standard CLI/`iterate_example` path (`AttributeError: 'BimodalSemantics' object has no
   attribute 'is_world'`, from shared framework code in `model_checker/iterate/models.py` that
   unconditionally assumes every theory has an `is_world` predicate). Not fixed here — it is
   cross-theory shared code needing its own regression plan. **Use `iterate: 1` (the default)
   until fixed.**
2. **Phase 21 `[COMPLETED WITH EXCLUSIONS]`**: `oracle/run-oracle-suite.sh`'s pass-2 "0 selected"
   condition, confirmed pre-existing across five task-generations of history. This condition has
   since resolved itself as a side effect of the `development` marker's Phase 23 removal (the one
   test its dead node-id fragment could match was also `development`-marked, so removing the
   marker unblocked it) — pass 2 now selects and passes 5 tests. This is an emergent consequence,
   not a deliberate fix, and the underlying dead fragment is still dead.

## What Changed (Phases 22-24)

### Phase 22: Documentation rewrite

Rewrote, grounding every claim in the actual current code and in live `dev_cli.py` output samples:

- `code/src/model_checker/theory_lib/bimodal/README.md` — full rewrite.
- `docs/ARCHITECTURE.md` — full rewrite: retired the frame-axiom ledger table and the
  duration-domain-guard note; added the two-phase constraint emission, the independent re-check
  (obligation S3), and "The (SOUND) Theorem" (carrying in the theorem statement, all four lemmas
  with Lean citations, and the determinism/cost tradeoff from `docs/ADEQUACY.md`, per the plan's
  own Amendment task); removed the dead "Rendering and Output-Encoding Policy" section (confirmed
  its subject code no longer exists anywhere in the tree).
- `docs/SETTINGS.md`, `docs/API_REFERENCE.md`, `docs/USER_GUIDE.md`, `docs/ITERATE.md`, and the
  `docs/README.md` hub — full rewrites for the certificate design's real settings, classes, and
  workflow.
- `oracle/bimodal_logic/README.md` — added a "Certificate JSON Export" section pointing to
  BimodalLogic's own protocol document as the fixed external contract.

**Discovered beyond the phase's own task list**: direct `dev_cli.py` testing with `"iterate": 3`
reproduced the `iterate: N > 1` crash described above — sharper than Phase 15's original "no
active exclusion constraint" record. Documented in `docs/ITERATE.md`'s "A Live Limitation"
section with pointers from `README.md`/`ARCHITECTURE.md`/`USER_GUIDE.md`.

### Phase 23: Remove the `development` marker and re-enable gating

Retired the marker entirely: unregistered in `code/pyproject.toml`; both
`pytest_collection_modifyitems` hooks that applied it deleted (`bimodal/tests/conftest.py`'s
whole-tree blanket, `oracle/conftest.py`'s tree-minus-soundness-core blanket, including its
now-dead `_SOUNDNESS_CORE_CLASSES`/`_is_soundness_core` exemption machinery); `and not
development` removed from all 10 gating `-m` invocations (`flake.nix` x2, `.github/workflows/
tests.yml` x2, `packaging.yml`, `release.yml` x2, `pypi-smoke.yml`, `oracle/run-oracle-suite.sh`
x2) plus prose in `code/run_tests.py` and `.github/workflows/README.md`. Three CI contract tests
whose entire subject evaporated with the mechanism they tested were deleted outright
(`test_development_marker_application.py`, `test_oracle_development_marker_application.py`,
`test_gating_selection_bimodal_decoupling.py`); two others covering broader properties were
narrowed (`test_run_tests_markers.py`, `test_unstable_deselection_wiring.py`).
`TESTING_GUIDE.md` section 8.14 rewritten as a compact retirement record.
`bimodal/tests/README.md`'s "Non-Gating" section rewritten to "Gating".
`test_example_budget_floor.py`'s stale bimodal-exclusion paragraph corrected (confirmed directly:
`KNOWN_TIMEOUT_EXAMPLES`/`UNSTABLE_EXAMPLES` are both empty, and the four examples it named as
uncollected are all now collected).

**Discovered beyond the phase's own task list**: two real marker consumers not named in the
plan's Phase 23 file list would have been left broken or semantically wrong —
`test_example.py`'s `test_build_example_bimodal_theory_countermodel` (marker removed; its
settings dict modernized off the retired `N`/padded `max_time: 30` onto the certificate
encoding's own fast default, verified green at 0.18-0.19s both before and after) and
`test_generate_then_execute.py`'s `_DEVELOPMENT_THEORIES` (emptied from `{"bimodal"}`, kept as an
empty set for future reuse). A `code/CHANGELOG.md` `[Unreleased]` entry records the redesign and
retirement (the 1.3.8 entry that introduced the marker was left untouched, per Keep a Changelog
convention against editing a published entry).

### Phase 24: Final verification

All verification run live in this dispatch, not assumed from earlier phases:

- **Main gating selection**: parallel pass (`-m "not packaging and not performance and not
  unstable and not xdist_serial" -n 4`) → 2855 passed, 1 skipped (environment-mode-conditional,
  unrelated to bimodal), 236.66s. Serial pass (`-m "xdist_serial and not packaging and not
  unstable"`) → 9 passed, 4.24s. **2864 tests passed total, 0 failed.**
- **Oracle suite**: `bash oracle/run-oracle-suite.sh` → both passes PASSED, ~9s combined
  (down from the pre-redesign ~40-minute figure). Pass 2 now genuinely selects and passes 5 tests
  (see the carried-forward Phase 21 exclusion note above).
- **Oracle exhaustive scan**: independently re-measured (`oracle/scan_runner.py
  --max-complexity 5`) at 274/274 conclusive (100%), 0 disagreements, ~9-10s wall-clock —
  reproducing Phase 21's own measurement.
- **`dev_cli.py` output shapes**: confirmed for `BM_CM_1` (countermodel — full `Certificate:`/
  boxed-subformula-table/`Evaluation Point:` block) and `MF_MODAL_FUTURE_TH` (no certificate —
  bare "there is no countermodel." with no spurious certificate block, per D8).
- **Certificate round-trip**: `test_certificate_lean_agreement.py` → 10/10 passed, not skipped
  (BimodalLogic/`lake` was available in this environment).

See the plan's own Phase 24 section for the full before/after comparison table and the
deliverable-by-deliverable checklist against the task description's DELIVERABLES list — every
named deliverable has a corresponding landed change.

## Measured Final Suite Numbers

| Suite | Result |
|---|---|
| `theory_lib/bimodal/tests/` | **366 passed**, 0 failed |
| `oracle/bimodal_logic/tests/` (via `run-oracle-suite.sh`) | **567 passed, 4 xfailed** (pass 1) + **5 passed** (pass 2) |
| Oracle exhaustive complexity<=5 scan | **274/274 conclusive (100%)**, 0 disagreements, ~9-10s |
| Main gating selection (`code/tests src/model_checker`) | **2855 passed** (parallel) + **9 passed** (serial), 1 unrelated skip, 0 failed |
| `code/tests/ci` | **136 passed** |
| Certificate/Lean round-trip | **10 passed** (live, not skipped) |

No test suite reported a failure anywhere in this dispatch's verification. The task's own
"red period" the plan predicted during the rewrite is closed: every measured number above is
green.

## Plan Deviations

- Touched `.github/workflows/README.md`, `code/tests/ci/test_example_budget_floor.py`,
  `code/src/model_checker/builder/tests/unit/test_example.py`,
  `code/tests/packaging/test_generate_then_execute.py`, `code/CHANGELOG.md`, and
  `code/src/model_checker/theory_lib/bimodal/docs/README.md` — none in the plan's original file
  lists for Phases 22-23; each individually justified in those phases' own plan sections (see
  "Discovered beyond this phase's own task list" notes there).
- The final summary is numbered `03_` rather than `01_`, since two earlier progress summaries
  (covering Phases 1-8 and 9-15) already used `01`/`02`.
- No other deviations from the plan's own Phases 22-24 task lists; every task item in both phases
  is checked off with its own verification evidence recorded inline in the plan.

## What NOT to Try

- Do not re-register `development` or resurrect either deleted CI contract test.
- Do not attempt to fix the `iterate: N > 1` crash or the shared `ConstraintGenerator` gap as a
  follow-up to this task — both are confirmed, reproduced, and require their own cross-theory
  regression plan; see `docs/ITERATE.md`.
- Do not edit `docs/ADEQUACY.md` as part of any bimodal follow-up to this task — it is owned by
  the separate adequacy-layer task; its one stale sentence (describing `semantic/core.py` as the
  retired encoding) is recorded for that task to pick up, not this one.
- Do not treat the `oracle/run-oracle-suite.sh` pass-2 fix as evidence the underlying dead
  `_XDIST_SERIAL_NODEID_FRAGMENTS` fragment issue was resolved — it was not; the fragment is
  still dead, pass 2 simply no longer depends on it mattering.

## References

- Plan: `specs/184_refactor_bimodal_theory_tests_green_and_paper_lean_aligned/plans/01_witness-family-certificate-redesign.md` — all 24 phases `[COMPLETED]` or `[COMPLETED WITH EXCLUSIONS]`.
- Phase handoffs: `specs/184_.../handoffs/phase-22-handoff-20260925T220000Z.md`,
  `phase-23-handoff-20260925T230000Z.md`.
- Research report (authority): `specs/184_.../reports/01_finite-certificate-redesign.md`.
- `code/src/model_checker/theory_lib/bimodal/docs/ADEQUACY.md` — the full (SOUND) soundness proof.
- `code/src/model_checker/theory_lib/bimodal/docs/ITERATE.md` — the `iterate: N > 1` crash's full
  reproduction and citation.
