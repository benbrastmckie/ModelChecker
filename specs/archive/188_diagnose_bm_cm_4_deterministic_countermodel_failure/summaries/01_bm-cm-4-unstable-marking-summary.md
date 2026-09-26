# Implementation Summary: Diagnose BM_CM_4 Deterministic Countermodel Failure

- **Task**: 188 - Diagnose BM_CM_4 deterministic countermodel failure
- **Status**: [COMPLETED]
- **Started**: 2026-09-25T17:15:00Z
- **Completed**: 2026-09-25T19:05:00Z
- **Effort**: ~7 hours (solver-bound measurement phases dominate)
- **Dependencies**: None
- **Artifacts**: plans/01_bm-cm-4-symbol-rename-fix.md, baselines/01_symbol-rename-harness.py,
  baselines/01_pre-change-verdicts.json, baselines/02_seed-sweep.json, baselines/02_seed-sweep.md
- **Standards**: summary-format.md, status-markers.md, artifact-management.md, tasks.md

## Overview

The plan's Phase 2 decision gate (a required >= 20-seed sweep, run before touching any source
file) rejected the candidate alpha-rename fix that research had identified: under a genuine
25-seed pinned-seed sweep, the renamed construction produced MORE undecided draws (5/25) than
the unmodified, committed construction (2/25) at the identical seeds and 40s probe budget. Per
the plan's own explicit gate, Phases 3-5 (land the rename, diff, full-suite verify) were
correctly not executed, and the task routed to Phase 7: BM_CM_4 is now tracked in
`UNSTABLE_EXAMPLES` (TESTING_GUIDE.md section 8.9), with `core.py` carrying zero diff.

## What Changed

- Built a rerunnable, seed-pinnable, counter-poisonable measurement harness
  (`baselines/01_symbol-rename-harness.py`, adapted from the archived frame-axiom regression
  harness) and used it to capture a full 52-example pre-change baseline
  (`baselines/01_pre-change-verdicts.json`) and a 25-seed sweep of both the candidate rename and
  a same-host, same-budget baseline control (`baselines/02_seed-sweep.json`/`.md`).
- Added `"BM_CM_4"` to `UNSTABLE_EXAMPLES` in
  `code/src/model_checker/theory_lib/bimodal/tests/unit/test_bimodal.py`, with a four-criteria
  comment block (what fails and why; demonstrably non-semantic; genuine fix attempted and its
  failure recorded; verbatim exit criterion), following the existing `BM_CM_1` entry's structure.
- Extended `.github/scripts/unstable_watch_classify.py`'s `MAX_TIME_BY_NODEID_FRAGMENT` with a
  `BM_CM_4-example_case9: 120` entry and added `TestClassifyBMCM4Signature` (4 new tests) to
  `code/tests/ci/test_unstable_watch_classifier.py` (47/47 pass).
- Corrected every stale "now reliably finds countermodels" claim: `examples.py`'s
  `BM_CM_4_settings` comment and header comment, `test_bimodal.py:69`'s `KNOWN_TIMEOUT_EXAMPLES`
  NOTE, the oracle inline comment copy, and `test_bound_var_counter_isolation.py`'s module
  docstring (a dated "second occurrence" note explaining all three parametrized states failing
  again is BM_CM_4's own instability, not a reopened order-dependence bug -- the counter-reset
  fix is confirmed still working).
- Marked both of the oracle tree's own BM_CM_4 assertions (`test_boundary_regression.py`'s
  `test_countermodel_bm_cm4_at_example_settings` and
  `test_regression_all_active_examples[BM_CM_4]`) `@pytest.mark.unstable`, after finding both
  currently fail with no exemption marker at all (confirmed by direct run: 120.95s failure).
  Neither is invoked by any gating GitHub Actions workflow today (confirmed by grep across
  `.github/workflows/`), so this was not a live CI-red risk, but it closed an undocumented,
  locally-red gap inconsistent with this task's own 8.9 bar.

## Decisions

- **Diagnosis confirmed as case (a)**: a genuine solve-cost regression from commit `f9cc081e`
  (Skolemized Seriality + Interpolation frame axioms), not (b) unreachability or (c) a semantic
  failure. Every decided draw in the 25-seed sweep returns the expected `match`; ADEQUACY.md's
  known-unsound-encoding caveat is not implicated because no verdict ever flips.
- **The alpha-rename candidate was rejected, not landed.** The research report's 3-5-probe
  sample (renamed: 3/3 fast `match`; baseline: 3/3 timeout, both at Z3's *default*, unpinned
  parameters) reflected each construction's specific default-parameter draw, not its general
  reliability. Under a real seed sweep the unmodified construction is actually MORE reliable
  (2/25 undecided) than the renamed one (5/25 undecided) -- the rename relocates the tail, it
  does not close it. Per the plan's decision gate, this stops Phase 3 before it starts.
  `max_time` was NOT raised on any branch, per the task's explicit prohibition.
- **BM_CM_4 satisfies TESTING_GUIDE 8.9's entry criterion 2** ("demonstrably not semantic") for
  the first time: prior to this task it was untracked and had zero decided-draw evidence on
  record; the 25-seed sweep now exhibits 23/25 decided `match` draws.
- **The oracle tree's own BM_CM_4 assertions were also marked `unstable`** (an addition beyond
  the plan's literal Phase 7 task list, made once the evidence showed both assertions failing
  with no marker at all) for consistency with 8.9 and with the code/-tree marking, even though
  neither is currently gating in practice.
- **No certificate-redesign handover is warranted.** The failure is a genuine, bounded solve-cost
  regression with no semantic-verdict ambiguity, so there is nothing here for that separate track
  to inherit.

## Plan Deviations

- **Phases 3, 4, 5 not executed** (by design): the plan's own decision gate at Phase 2
  ("if any seed produces an undecided draw ... STOP and route to Phase 7") fired, and Phases 3-5
  are each explicitly conditioned on the prior phase (`3 depends on 2`, `4 depends on 3`,
  `5 depends on 4`). This is the plan's designed negative-result path, not a skipped obligation --
  see the "NOT EXECUTED" notes added to each of those three phase headings.
- **Phase 6's tasks were written assuming the rename had landed** (e.g. "this task's rename
  recovered decided `match` draws"). The actual edits record the REJECTION of the rename
  candidate and BM_CM_4's `unstable` status instead, since that is what was actually measured.
  All five Phase 6 file-edit tasks and the four-node-ID re-run were still completed, executed as
  part of Phase 7 (whose own task list requires Phase 6's corrections "on every branch") rather
  than as an independent Phase-5-gated run.
- **Oracle `@pytest.mark.unstable` additions** (both BM_CM_4 sites in
  `test_boundary_regression.py`) go beyond Phase 7's literal task list, which named only the
  comment resync. Added because the evidence-gathering step found both assertions failing with
  zero exemption marker -- see Phase 7's outcome note for the full justification and the
  confirmation that neither is gating today regardless.

## Impacts

- `code/src/model_checker/theory_lib/bimodal/semantic/core.py` carries zero diff from this task
  -- no solver-visible behavior changed.
- BM_CM_4 is now deselected from every release-gating pytest invocation via `-m "not unstable"`
  (code/ tree) in addition to the pre-existing theory-wide `development` blanket, and via the
  same marker in the oracle tree (where no blanket previously existed).
- BM_CM_4 is now observed by `unstable-watch.yml`'s nightly `watch_code` and `watch_oracle`
  steps (both filter `-m unstable`), with a working `TIMING` vs. `NEW` classification via the
  extended `unstable_watch_classify.py`.
- The rerunnable harness (`baselines/01_symbol-rename-harness.py`) remains available as the
  standing regression probe for any future encoding change in this area.

## Follow-ups

- BM_CM_4's `unstable` marker comes off per its own exit criterion: 20 consecutive
  unstable-watch runs with zero failures, OR a genuine encoding fix collapsing the tail across a
  >= 20-seed sweep with no undecided draw at `max_time = 120`. No owner/due date; tracked via the
  nightly `unstable-watch.yml` workflow and TESTING_GUIDE.md section 8.9's review cadence.
- If a future change touches `build_seriality_constraint`/`build_interpolation_constraint`, rerun
  `baselines/01_symbol-rename-harness.py`'s sweep mode rather than re-deriving a fresh probe from
  scratch.

## References

- `specs/188_diagnose_bm_cm_4_deterministic_countermodel_failure/plans/01_bm-cm-4-symbol-rename-fix.md`
- `specs/188_diagnose_bm_cm_4_deterministic_countermodel_failure/reports/01_bm-cm-4-cost-regression.md`
- `specs/188_diagnose_bm_cm_4_deterministic_countermodel_failure/baselines/01_symbol-rename-harness.py`
- `specs/188_diagnose_bm_cm_4_deterministic_countermodel_failure/baselines/01_pre-change-verdicts.json`
- `specs/188_diagnose_bm_cm_4_deterministic_countermodel_failure/baselines/02_seed-sweep.json`
- `specs/188_diagnose_bm_cm_4_deterministic_countermodel_failure/baselines/02_seed-sweep.md`
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_bimodal.py`
- `code/src/model_checker/theory_lib/bimodal/examples.py`
- `oracle/bimodal_logic/tests/test_boundary_regression.py`
- `.github/scripts/unstable_watch_classify.py`
- `code/docs/core/TESTING_GUIDE.md` section 8.9
