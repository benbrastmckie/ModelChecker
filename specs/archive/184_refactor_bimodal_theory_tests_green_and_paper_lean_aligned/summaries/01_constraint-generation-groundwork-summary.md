# Implementation Summary: Witness-family certificate redesign (constraint-generation groundwork)

- **Task**: 184 - Redesign the bimodal theory around witness-family certificates (discrete Z-time)
- **Status**: [IN PROGRESS]
- **Started**: 2026-09-25T18:32:00Z
- **Completed**: 2026-09-25T19:05:00Z
- **Effort**: ~2.5 hours (Phases 5-8 of 24; plan's own estimate for these four phases is 7.5 hours)
- **Dependencies**: Phases 1-4 (certificate foundation layer; see the prior summary)
- **Artifacts**: plans/01_witness-family-certificate-redesign.md
- **Standards**: summary-format.md, status-markers.md, artifact-management.md, tasks.md

## Overview

This dispatch continues from the certificate foundation layer (Phases 1-4, see
`01_certificate-foundation-layer-summary.md`) through Phase 8: the round-trip differential test
against BimodalLogic's Lean binary, and the full quantifier-free Z3 variable/constraint layer
(label bits, box guesses, witness-lasso allocation, and generators for all four certificate
conditions). None of this touches `BimodalSemantics`, `operators.py`, `iterate.py`, `examples.py`,
or the oracle yet -- those are Phase 9 onward. The task remains at `[IMPLEMENTING]`.

**Important, flagged explicitly**: Phase 6 (rewriting the shared-name `WitnessRegistry` class)
breaks `semantic/core.py:86`'s existing `WitnessRegistry(self.N, self.M)` call immediately, which
cascades to essentially the entire pre-existing bimodal test suite (128 failed + 87 errored of 339
unit tests, measured directly). The plan's own Rollback/Contingency section states the
unavoidably-red period begins at Phase 9; that is corrected in Phase 6's plan notes and repeated
here so it is not missed by a reader who only reads this summary. This is the accepted,
no-compatibility-layer cost of a clean-break class rewrite `core.py` already depended on, not a
regression introduced by mistake -- `core.py`'s call site is repaired on schedule at Phase 9.

## What Changed

- **Phase 5** (`semantic/certificate.py`, `tests/unit/test_certificate.py`,
  `tests/integration/test_certificate_lean_agreement.py`): added `recheck_json`, the JSON-boundary
  wrapper `recheck` itself cannot be (it takes an already-decoded family and an already-typed
  target time). Extended the round-trip harness a dependent, already-completed adequacy-layer
  task had already built (`test_certificate_lean_agreement.py`) with `TestPythonRecheckerAgreesWithLean`
  (comparing `recheck_json` against `lake exe check_certificate` directly on the whole fixture
  corpus) rather than creating a second, duplicate `test_certificate_roundtrip.py` harness -- see
  the plan's Phase 5 notes for the deviation record. The A2-triangle test is carried forward to
  when the Z3 encoding exists.
- **Phase 6** (`semantic/witness_registry.py`, rewrite): the Z3 variable layer. `wrap(t)` maps any
  integer position to its periodic slot, agreeing with `LabelledLasso.label`'s decoding; `bit`
  memoizes one Boolean per (lasso, slot, formula); `guess` memoizes the box-guess Boolean;
  `allocate_witness_lasso` hands out witness-lasso indices, round-robin once `max_witnesses` is
  reached. 45 new unit tests.
- **Phase 7** (`semantic/witness_constraints.py`, rewrite part 1): `local_coherence_constraints`
  (the five `LocalCoherentLab` biconditionals, one representative position per slot -- sound by
  construction since `bit` already collapses same-slot positions to the identical Z3 term) and
  `target_constraints` (one-hot `sel[t]` with exactly-one via `z3.AtMost`, plus the guarded
  premise/conclusion implications). 12 new unit tests, including an AST walk confirming no
  quantifier node.
- **Phase 8** (`semantic/witness_constraints.py` part 2, `semantic/certificate.py`): added
  `fulfilment_constraints` (generated over the *wide*, two-period window and the corrected scan
  bounds, imported directly from `certificate.py` rather than redefined, so the encoder and the
  re-checker cannot drift apart) and `box_faithfulness_constraints` (the narrower one-period
  window, caller-supplied lasso list). 10 new unit tests.

All 79 new/extended unit tests across the four phases are green, along with the 10 integration
tests against the live Lean binary present on this host.

## Decisions

- The Phase-7 argument that one representative position per slot suffices for local coherence
  (because `bit(lasso, t, f)` is the *same* Z3 term for every `t` sharing a slot, not merely equal
  under every model) does **not** extend to fulfilment: the scan bound is itself a function of
  `t`, not of `t`'s slot alone, so fulfilment is generated over the wide window exactly as the
  plan specifies. Documented explicitly in both modules' docstrings to prevent a future reader
  from over-generalizing the shortcut.
- `box_faithfulness_constraints` takes its lasso-index list from the caller rather than
  discovering lassos itself; orchestrating which lassos exist (main plus any witness lassos
  allocated for a false box) is Phase 9's `finalize_certificate()` job, matching D6.
- Reused `certificate.py`'s existing `_coherence_window`/`_scan_forward_bound`/
  `_scan_backward_bound`/`_box_window` directly (duck-typed on `.nb`/`.nm`/`.nf`, which
  `WitnessRegistry` also carries) rather than reimplementing them in `witness_constraints.py`,
  satisfying Phase 8's "factor into a single shared function" task without moving code.

## Plan Deviations

- Phase 5: no new `test_certificate_roundtrip.py` file was created; the round-trip harness a
  dependent, already-completed task had already built was extended in place instead, to avoid
  duplicating its probe/skip/subprocess plumbing. Recorded inline in the plan's Phase 5 section.
- Phase 6: the plan's Rollback/Contingency section's claim that the unavoidably-red period begins
  at Phase 9 is corrected (it begins at Phase 6, for the reason given above). Recorded inline in
  the plan's Phase 6 section.
- No other deviations. All other Phase 5-8 tasks completed exactly as specified.

## Impacts

- Phases 1-5's tests (formula/certificate/round-trip) remain fully green: no regression.
- Phase 6 onward: `BimodalSemantics.__init__` now raises `TypeError` immediately (128 failed + 87
  errored of 339 unit tests in `tests/unit/`), since `core.py:86` has not yet been updated to the
  new `WitnessRegistry` constructor -- that repair is Phase 9's own task, not deferred by
  accident. No integration test involving example-solving was run in this state, since it would
  uniformly fail for the same reason.
- Phases 9-24 (the actual `BimodalSemantics`/`BimodalProposition`/`BimodalStructure` rewrite,
  operators/iterate/examples migration, oracle rewrite, docs, `development`-marker removal) remain
  entirely to do. The task status should stay `[IMPLEMENTING]`, not move to any terminus.

## Follow-ups

- Next dispatch: Phase 9 (`BimodalSemantics` rewrite -- settings and framework contract). This is
  the highest-stakes remaining phase before green returns: it repairs `core.py:86`'s broken
  `WitnessRegistry` construction, deletes ~15 methods belonging to the retired encoding, and
  implements `true_at`/`premise_behavior`/`conclusion_behavior`/`finalize_certificate()`. Read
  Phase 9's own task list and D3/D4/D5/D6 before starting; the framework-contract details
  (`self.N`, `self.all_states`, `main_point` shape) are load-bearing for `models/structure.py`.
- Phases 10-13 (certificate extraction from the Z3 model, `BimodalProposition` rewrite,
  `BimodalStructure` rewrite) are where green substantially returns for construction; operators.py
  (Phase 14) is needed before any example can actually solve.

## References

- `specs/184_refactor_bimodal_theory_tests_green_and_paper_lean_aligned/plans/01_witness-family-certificate-redesign.md`
- `specs/184_refactor_bimodal_theory_tests_green_and_paper_lean_aligned/summaries/01_certificate-foundation-layer-summary.md`
- `specs/184_refactor_bimodal_theory_tests_green_and_paper_lean_aligned/handoffs/phase-8-handoff-20260925T190500Z.md`
- `code/src/model_checker/theory_lib/bimodal/semantic/certificate.py`
- `code/src/model_checker/theory_lib/bimodal/semantic/witness_registry.py`
- `code/src/model_checker/theory_lib/bimodal/semantic/witness_constraints.py`
