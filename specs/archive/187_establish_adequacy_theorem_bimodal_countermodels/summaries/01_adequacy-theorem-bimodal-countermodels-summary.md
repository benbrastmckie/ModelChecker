# Implementation Summary: Task #187

- **Task**: 187 - Establish an adequacy theorem connecting ModelChecker's bimodal countermodels to the paper's task semantics
- **Status**: [COMPLETED]
- **Started**: 2026-09-25T05:14:32Z
- **Completed**: 2026-09-25T08:50:00Z
- **Effort**: about 3.5 hours
- **Dependencies**: None blocking. Layered over the certificate-redesign task, which this task's Phase 5 amends while it is still not-yet-begun.
- **Artifacts**: plans/01_adequacy-theorem-bimodal-countermodels.md, reports/01_adequacy-theorem-bimodal-countermodels.md
- **Standards**: summary-format.md, status-markers.md, artifact-management.md, tasks.md

## Overview

Implemented the six-phase adequacy-layer plan in full. Authored
`code/src/model_checker/theory_lib/bimodal/docs/ADEQUACY.md`, a durable theory document stating
and fully proving (SOUND) for the witness-family certificate design (four lemmas, the theorem,
a Lean citation table verified name-by-name against the BimodalLogic development, and a
transcription audit), stating the proved re-check windows and the presentation/re-verification
protocol, and recording (ADEQ) as open with its A0-A3 status table and deciding tests. Built a
checker-independent certificate fixture corpus with a self-contained Python decoder/evaluator
that mechanically demonstrates the proved two-period window catches a local-coherence violation
the one-period window misses, differentially validated against the real
`lake exe check_certificate` Lean binary. Amended the certificate-redesign plan's D7 (window) and
D9 (state-sharing rationale) decisions and nine of its phases with the corrected constraints
while that plan was still not yet started. Corrected the one false claim about the paper's
semantics in the current test suite's exclusion comment (prose only) and wired the new document
into the theory's documentation index.

## What Changed

- `code/src/model_checker/theory_lib/bimodal/docs/ADEQUACY.md` — New. States (SOUND) and (ADEQ)
  precisely; proves (SOUND) in full via four lemmas (Frame, Histories, Time-shift preservation,
  Truth lemma) and the theorem; gives the Lean citation table (every name verified to resolve in
  `~/Projects/BimodalLogic/FormalSystem/`) and the transcription audit; states the proved
  re-check windows (`[-2*nb, nm+2*nf)` for local coherence/fulfilment, `[-nb, nm+nf)` for box
  faithfulness) and why they differ; states the wire contract and the four-step dual-verification
  protocol; records (ADEQ) as open (A0 permanent frame-class gap, A1 open compression with the
  one candidate reduction examined and rejected, A2 provable/testable now, A3 vacuous until A1);
  and records the three reasons the design is ℤ-time only.
- `code/src/model_checker/theory_lib/bimodal/tests/fixtures/certificates/` — New. Four
  checker-independent fixtures (`01_positive_box.json`, `02_infinite_postponement.json`,
  `03_box_unfaithful.json`, `04_window_discriminator_coherence.json`), `expected_verdicts.json`,
  and a `README.md` documenting the wire contract and, in detail, both the successful
  local-coherence window-discrimination construction and the attempted-and-rejected
  fulfilment-side construction (per the plan's Scope Hypothesis escape hatch).
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_certificate_fixtures.py` — New.
  A from-scratch decoder and evaluators for (C1)-(C4), independent of
  `model_checker.theory_lib.bimodal`, with 11 tests including two that assert the window
  parameter is load-bearing (narrow window misses the violation; wide window catches it in the
  outer band; narrowing the window flips the verdict).
- `code/src/model_checker/theory_lib/bimodal/tests/integration/test_certificate_lean_agreement.py`
  — New. Differentials the fixture corpus against the real `lake exe check_certificate` binary
  (6 tests, all green against BimodalLogic commit `6529c6e853f1c29358a7e74a76055f64f68b7ff7`),
  with a bounded probe-then-skip structure for hosts without the Lean toolchain, and the two
  required error-path assertions (missing `target`, missing `target.time`).
- `specs/184_refactor_bimodal_theory_tests_green_and_paper_lean_aligned/plans/01_witness-family-certificate-redesign.md`
  — Amended. Rewrote D7 (the proved windows, corrected from the plan's original single
  one-period bound) and D9 (the state-sharing blocker, corrected from Limit/Saturation to
  `total_eq_orbit` and the Box case); added an amendment block; amended Phases 2, 3, 4, 5, 8, 9,
  12, 16 (folding in Phase 17's one relevant point) and 22 with the theorem's hard constraints.
  Validated (`validate-artifact.sh`), 24 phases and their statuses unchanged.
- `code/src/model_checker/theory_lib/bimodal/docs/README.md` — Added ADEQUACY.md to the
  navigation and documentation-overview sections.
- `code/src/model_checker/theory_lib/bimodal/README.md` — Added an "Adequacy" section pointing
  to `docs/ADEQUACY.md`.
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_bimodal.py` — Comment-only. Corrected
  the exclusion comment's false claim that the modal-future axiom is not a theorem under the
  paper's semantics; cited `modal_future_valid` and `no_witnessFamily_of_MF` by name; recorded
  that the reported countermodel is a boundary-vacuity artifact of the current encoding. Exclusion
  membership, settings, and `expectation` are untouched (verified via `git diff`: comment lines
  only).

## Decisions

- Phase 1 and Phase 2 (both authoring `ADEQUACY.md`) were written in a single pass since the
  document is one continuous piece of mathematics; each phase was still closed independently
  against its own acceptance criteria before being marked complete.
- The fulfilment-side window-discriminating fixture was attempted (per the Scope Hypothesis) and
  found non-discriminating: keeping (C1) coherent throughout an unbounded back region while
  withholding the event forces the guard to be present throughout that region too, which then
  serves as a witness-guard from any distance, so no outer-band-only fulfilment violation could
  be constructed without also breaking local coherence there. This matches
  `Decide.lean`'s own characterization of the fulfilment window as resting on two separate facts
  (bounded witness plus periodicity) rather than a pure periodicity argument. Recorded in
  `fixtures/certificates/README.md` with the full argument; the local-coherence fixture ships
  alone, per the plan's own escape hatch.
- All fixture expected verdicts were pinned empirically against the real `lake exe
  check_certificate` binary (BimodalLogic commit `6529c6e853f1c29358a7e74a76055f64f68b7ff7`),
  not guessed, before being written into `expected_verdicts.json`.
- Every Lean name cited in `ADEQUACY.md` was individually verified to resolve at (or within a few
  lines of) its cited `file:line` in `~/Projects/BimodalLogic/FormalSystem/`; several path
  abbreviations inherited loosely from the research report were tightened to full paths during
  this check.

## Plan Deviations

- None (implementation followed plan). The one Scope-Hypothesis-anticipated outcome — the
  fulfilment-side seam proving non-discriminating — is not a deviation from the plan; it is the
  plan's own explicitly named contingency, exercised and recorded exactly as specified.

## Verification

- Build: N/A (documentation and test-fixture task; no build step)
- Tests: Passed. New modules: 11/11 (`test_certificate_fixtures.py`), 6/6
  (`test_certificate_lean_agreement.py`, live against the Lean binary). Full bimodal suite:
  345/350 passed, 5 pre-existing failures unrelated to this task (documented Z3 MBQI
  nondeterminism in `BM_CM_1`/`BM_CM_4`, already tracked by `pytest.mark.unstable` and a
  dedicated counter-isolation regression module respectively; the diff to `test_bimodal.py` is
  comment-only, confirmed via `git diff`).
- Files verified: Yes (existence, content, and — for the amended `184` plan —
  `validate-artifact.sh` and grep-based window/phase-count checks).

## Impacts

- The certificate-redesign task (184) now carries corrected windows in its D7/D9 decisions and
  nine phases, closing the "single most likely silent soundness bug" its own plan text had
  flagged, before any of those phases are dispatched.
- The bimodal theory now has a durable, in-repository statement and proof of the soundness
  correspondence that governs the redesign's target design, sited in `docs/ADEQUACY.md` and
  linked from the theory's documentation index.
- A checker-independent fixture corpus and Lean-differential test now exist in this repository
  for the first time (`grep -rin certificate` over `bimodal/` and `oracle/` previously returned
  zero matches, per the research report); both are available for the redesign task's own Phase 4
  and Phase 5 to build on or extend.

## Follow-ups

- The redesign task (184) should proceed against its now-corrected plan; its Phase 4 acceptance
  criterion now explicitly requires passing this task's window-discriminating fixture.
- (ADEQ)'s A1 (compression) remains open work in the BimodalLogic repository's own task tracker,
  outside this repository's scope.
- If lasso state-sharing is ever added for the stability modal, `ADEQUACY.md`'s "Why the design
  is deterministic" section and the corrected D9 rationale must both be revisited (Lemma 2 and
  the Box case of Lemma 4 would need re-proving), not merely a Limit/Saturation argument.

## References

- `specs/187_establish_adequacy_theorem_bimodal_countermodels/reports/01_adequacy-theorem-bimodal-countermodels.md`
- `specs/187_establish_adequacy_theorem_bimodal_countermodels/plans/01_adequacy-theorem-bimodal-countermodels.md`
- `code/src/model_checker/theory_lib/bimodal/docs/ADEQUACY.md`
- `code/src/model_checker/theory_lib/bimodal/tests/fixtures/certificates/README.md`
- `~/Projects/BimodalLogic/FormalSystem/Metalogic/Decidability/WitnessFamily/`
