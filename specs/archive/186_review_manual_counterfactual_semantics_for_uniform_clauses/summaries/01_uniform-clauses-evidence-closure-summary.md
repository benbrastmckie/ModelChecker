# Implementation Summary: Task #186

- **Task**: 186 - Review manual counterfactual semantics for uniform clauses
- **Status**: [COMPLETED]
- **Started**: 2026-09-25T00:00:00Z
- **Completed**: 2026-09-25T03:20:00Z
- **Effort**: ~3.5 hours
- **Dependencies**: None
- **Artifacts**: plans/01_uniform-clauses-evidence-closure.md, reports/01_family-level-settled-verification.md (amended), followup-task-spec.md
- **Standards**: summary-format.md, status-markers.md, artifact-management.md, tasks.md

## Overview

Executed all six phases of the round-2 plan: a BimodalLogic (665-668) alignment review, a
general-task-relation oracle implementing `@def-maximal-compatible-subevolutions` clauses (a)-(d)
directly, a certified temporally constrained frame closing two of report 01's five open items, a
directly-computed family-level hyperintensionality witness (Frame G2), the Settler
Minimality/padding resolution, and a full integration pass on report 01 plus a follow-up
specification. A significant mid-task discovery reshaped the work: the Logos manual has already
adopted almost the entire round-1 recommendation (via a separate, independently-running task in
that repository, ~3.5 hours after round 1's report completed), so this round's real contribution is
the BimodalLogic alignment, the constrained-frame and Frame-G2 measurements, and an honest
re-audit of what remains to be written into the manual — which turns out to be much narrower than
originally scoped.

## What Changed

- `specs/186_.../reports/01_family-level-settled-verification.md` — amended with four new findings
  (F11 alignment, F12 constrained frame, F13 G2 witness, F14 Settler Minimality/padding), a
  round-2 Executive Summary bullet plus inline corrections to two round-1 bullets, D1-D6 annotated
  with current status plus a new D7, a rewritten open-items list (2 items closed, 1 narrowed, 1
  unchanged-but-untested, 2 new), extended Appendix A/B, updated header Artifacts/Sources-Inputs
  lists, and a new `## Recommendations` section (fixing a pre-existing `validate-artifact.sh`
  defect from round 1).
- `specs/186_.../baselines/02_constrained-frame-oracle.py` — new (round 2's general-task-relation
  oracle: `GeneralFrame`/`GeneralModel`, `duration_uniform_relation`,
  `forbidden_transition_relation`, `certify_constrained_frame`, `frame_g2`, and the
  `regression`/`c1c2`/`g2` experiment drivers).
- `specs/186_.../baselines/02_constrained-frame-oracle-output-{regression,c12,g2}.txt` — new saved
  outputs.
- `specs/186_.../followup-task-spec.md` — new: a corrected, narrower manual/Lean change
  specification for a following task, superseding report 01's original F10 edit list with a
  re-audited, mostly-already-landed status table.
- `specs/186_.../progress/phase-{1-6}-progress.json`, `specs/186_.../handoffs/phase-{1-5}-handoff-*.md` — new (per-phase progress tracking and handoffs).

## Decisions

- D1 (principle), D2 (three adjustments), D3 (Settler Minimality), D5 (proof theory), D6 (F4) are
  all confirmed already adopted/landed in the current Logos manual, independently of this task.
  D4 (E3 form) is unchanged as a recommendation, strengthened by a realizable pointwise-E3-failure
  measurement (F12). D7 (new): the BimodalLogic alignment corroborates the manual's existing
  choices methodologically and mechanistically but supplies no content directly.
- The BimodalLogic shape ("`p` occurs exactly once along every history") did not transfer to Phase
  3's constrained-frame construction; a one-way transition ban was built directly instead.
- The direct `mcs` implementation enumerates ALL parts of the bounding family per point (not just
  per-point maximal-compatible parts), since a general/interacting relation can make a
  jointly-maximal `rho` fail to decompose into independently-maximal per-point choices; memoized,
  since the window-3 experiments otherwise do not finish in reasonable time.

## Plan Deviations

- **Phase 1** altered: F11 carries a preamble beyond the plan's task list (the manual-currency
  discovery), recorded because it is directly material to Phases 5-6.
- **Phase 2** altered: `thread()` checks EVERY pair in a family's domain (matching
  `@def-task-coherent`'s own quantifier), not only consecutive pairs, a stronger-than-asked
  implementation with no effect on the pinned regression. E4 (report 02's 256-state frame) was not
  re-run through the general engine; deferred as a follow-up run, not required by the plan's own
  Phase 2 verification criterion.
- **Phase 3** none beyond the BimodalLogic-shape non-transfer noted inline.
- **Phase 4** altered: the nested `[](.)` check does not separate on Frame G2 (both agree); reported
  honestly rather than manufacturing a separating example. Open item 5 is still closed since the
  V/F distinctness itself is the witness.
- **Phase 5** altered: D3's "remaining judgment" task is answered by reporting the manual's own
  already-made decision (axiom form) rather than presenting a live choice for a follow-up task.
- **Phase 6** altered: `followup-task-spec.md`'s scope is narrower than F10 originally implied,
  since re-reading the current manual found most of F10 already landed; D3 is reported as decided,
  not posed as an open choice.

## Verification

- Build: N/A (research task; no ModelChecker code changed).
- Tests: N/A.
- `python3 -m py_compile 02_constrained-frame-oracle.py`: clean.
- `python3 02_constrained-frame-oracle.py regression`: PASSED (131,584/131,584 mcs-agreement pairs;
  E1/E2/E3/E5 all match round 1's pinned baseline), re-verified after Phases 3 and 4's additions.
- Certificate perturbation test: correctly reports `CERTIFICATE FAIL` for a false claim.
- `bash .claude/scripts/validate-artifact.sh` on report 01 and the plan: both PASS, 0 warnings.
- `git status --short` before every phase commit: no path outside
  `specs/186_review_manual_counterfactual_semantics_for_uniform_clauses/` other than the shared
  `specs/TODO.md`/`specs/state.json` task-tracking files.
- Files verified: Yes.

## Impacts

- Report 01 is now the authoritative, up-to-date account of the manual's counterfactual semantics
  state, superseding its own round-1 content where the manual has since moved.
- The follow-up task this round hands off is much smaller in scope than round 1 anticipated: one
  confirmed manual edit (`@rem-event-status`'s E1/E3/E4 record for the world-quantifying family)
  plus two unverified secondary checks, rather than a ten-plus-site rewrite.
- `baselines/02_constrained-frame-oracle.py` is a reusable general-task-relation oracle for any
  future task needing to test the recipe against a non-memoryless frame; its direct `mcs`
  implementation and memoization pattern are recorded for reuse.

## Follow-ups

- `specs/186_.../followup-task-spec.md`'s primary deliverable: write `@rem-event-status`'s missing
  E1/E3/E4 record for the world-quantifying family in `03-dynamics.typ`.
- The tensed-antecedent multi-time-settler test (open item 1, narrowed) and the beyond-finite
  Settler Minimality necessity test (open item 3, narrowed) remain named but unexecuted, per the
  plan's own contingency against open-ended search.
- The world-history completion principle (`@rem-occurrence-possible-states` leg (d)) remains
  deferred by the manual's own text; F11/D7 supplies a candidate strength (`Completion`,
  BimodalLogic-corroborated) as a template for a future decision, not a recommendation to adopt one
  now.

## References

- `specs/186_review_manual_counterfactual_semantics_for_uniform_clauses/plans/01_uniform-clauses-evidence-closure.md`
- `specs/186_review_manual_counterfactual_semantics_for_uniform_clauses/reports/01_family-level-settled-verification.md`
- `specs/186_review_manual_counterfactual_semantics_for_uniform_clauses/followup-task-spec.md`
- `specs/186_review_manual_counterfactual_semantics_for_uniform_clauses/handoffs/` — one per phase (1-5)
