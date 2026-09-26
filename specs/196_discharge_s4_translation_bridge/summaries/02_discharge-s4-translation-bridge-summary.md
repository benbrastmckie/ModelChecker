# Implementation Summary: Discharge obligation S4 (Sentence-to-Formula translation bridge)

- **Task**: 196 - Discharge obligation S4, the Sentence-to-Formula translation bridge
- **Status**: [COMPLETED]
- **Started**: 2026-09-26T19:30:00Z
- **Completed**: 2026-09-26T20:45:00Z
- **Effort**: ~9 hours (matches plan estimate)
- **Dependencies**: 193, 194 (both completed prior to this dispatch)
- **Artifacts**: plans/01_discharge-s4-translation-bridge.md, summaries/02_discharge-s4-translation-bridge-summary.md
- **Standards**: summary-format.md, status-markers.md, artifact-management.md, tasks.md,
  git-workflow.md, no-task-references-in-deliverables.md

## Overview

Discharged obligation S4 (the `Sentence → Formula` translation bridge's truth-preservation
claim) for both its tense half and its previously-uncovered box half, via a differential
property test in `tests/unit/test_formula.py`. Per the two binding user decisions recorded in
`.decisions.json`, this required a scope-added prerequisite first: normalizing ModelChecker's
`\Until`/`\Since` argument order from event-first to guard-first, matching the Lean development
exactly, so `translate` is positional identity rather than a swap, and the verification phases
could be written against the normalized convention instead of immediately needing to be
rewritten out of it.

## What Changed

**Normalization (Phases 1-4):**
- `operators.py`: `UntilOperator`/`SinceOperator` `true_at`/`false_at` are now guard-first
  (`(self, guard_arg, event_arg, eval_point)`); `DefNextOperator`/`DefPrevOperator` derivations
  are now `[UntilOperator/SinceOperator, [BotOperator], argument]` (guard=bot, event=argument).
- `semantic/formula.py`: `translate`'s `\Until`/`\Since` rules are positional identity.
- `oracle/bimodal_logic/translation.py`: `_PRIMITIVE_BINARY`'s `untl`/`snce` tuples flipped to
  guard-first.
- Every order-bearing formula string across `examples.py` (16 BX axiom conclusions) and the
  bimodal/oracle test suites was swapped in lockstep, verified via a parse/swap/infix round-trip
  tool built on the codebase's own parser (not a blind sed), each result also inspected by hand
  against its own comment.
- `test_certificate_fixtures.py`'s internal `("untl"/"snce", ...)` tuple flipped to guard-first
  for one argument order throughout (objective 2.5's "flip" branch, not the fallback).
- Standalone docs (`README.md`, `docs/API_REFERENCE.md`, `docs/ARCHITECTURE.md`) rewritten to
  state the current convention, retaining one sentence of history each.

**Verification (Phases 5-9):**
- Relocated the certificate decoder/evaluator out of `test_certificate_fixtures.py` into a new
  `_certificate_model.py` (a move, not a duplicate), loaded via
  `importlib.util.spec_from_file_location` in both consumers (`pyproject.toml`'s
  `--import-mode=importlib` does not resolve a plain sibling-file import — the plan's Scope
  Hypothesis fallback, confirmed needed).
- Generalized `test_formula.py`'s two independent evaluators (`_eval_mc_ast`/`_eval_lean_formula`)
  from `(node, valuation, t, domain)` to `(node, family, i, t, domain)`, adding a family-global
  `\Box` clause to both, replacing the prior `NotImplementedError`.
- Added Axis 1 (three hand-built multi-lasso label families: box-true-everywhere,
  box-false-via-a-second-lasso, and mixed-atoms) with a coherence-precondition test class
  (`TestPropertyFamiliesAreCoherent`) using the imported `coherent_at`/`box_faithful`.
- Added Axis 2 (a deterministic, seeded generator over atoms `{p, q}` covering every operator the
  obligation names: `\neg, \wedge, \vee, \rightarrow, \Diamond, \top, \future, \past, \next,
  \prev`, plus mandatory asymmetric `\Until`/`\Since` instances), with coverage and asymmetry
  genuinely checked (`TestDefinedOperatorCoverage`, `TestAsymmetryIsGenuine`), not assumed.
- Added `TestTranslateTruthPreservationBox`, discharging S4's box half across the generated
  corpus plus hand-written box nestings, crossed with all three families.
- Added `TestNegativeControlsHaveTeeth`: six controls (non-vacuity, a Box-mutation control, a
  family-crossing control, two asymmetry-sensitivity controls, and an elimination control for the
  retired pre-normalization `\next` order) all pass by detecting their injected defect.
- Rewrote `docs/ADEQUACY.md` (§2 S4 row, §4.2 Residual, §6.3) and `docs/TRUST_PIPELINE.md`
  (Stage 1 evidence, "What remains") to record the new discharged state, the route decision, and
  the Lean-side deferral. Also fixed a sixth documentation location outside the plan's own
  enumeration — `docs/A2_GAP.md`'s stale "box half has no property-test coverage at all" claim.

## Decisions

- **Route 2 (property test) taken; Route 1 (relocate elimination into verified Lean code)
  recorded infeasible**: `translate` runs at Python evaluation time inside every primitive
  operator's own `true_at`, not only at export, and Lean has no callable verified elimination
  pass to relocate into.
- **Lean-side translation cross-check deferred**, its counterpart confirmed absent from the
  local `~/Projects/BimodalLogic` checkout.
- **Guard-first normalization taken as a scope addition** (user-directed, cycle 3 decision),
  landing before the verification phases as required.
- Two order-bearing occurrences (`test_certificate_a2_triangle.py`'s three identical
  `"(q \Until p)"` instances, and `test_proposition.py`'s single `"(A \Until B)"`) did NOT go
  red under the flipped convention. Both were individually diagnosed (not silently accepted):
  the triangle-test one is order-insensitive at that specific closure-size/enumeration-count
  model point (swapped anyway, for convention consistency, and re-verified green); the
  proposition-test one is order-insensitive by construction (it builds its own certificate
  directly from `translate()`'s output rather than comparing against an independent
  expectation), so it was correctly left unswapped as a genuine Class D (order-free) site
  rather than a missed Class B flip.
- `\top` is excluded from every `translate()`-exercising test (though it remains in the
  coverage-only corpus): it hits a pre-existing, already-documented `TopOperator` bug in
  `Sentence.update_types`, unrelated to this task and already routed around everywhere else in
  this theory (`examples.py`'s own "explicit expansion to avoid TopOperator bug" comment).

## Plan Deviations

- None (implementation followed plan). All 9 phases completed as scoped; the two Scope
  Hypotheses that had explicit fallback branches (Phase 5's decoder-import mechanism, Phase 2
  objective 2.5's tuple-flip-vs-fallback choice) both resolved to the branch the plan anticipated
  and named explicitly, not an undocumented deviation.

## Impacts

- `\Until`/`\Since` now read guard-first everywhere in this repository, matching the Lean
  development and the mainstream LTL reading of `A U B`. Any future formula string written
  against the old event-first convention would silently denote a different proposition — future
  contributors should consult `docs/ARCHITECTURE.md`'s guard-first paragraph.
- S4's box half is no longer an unaddressed gap in `docs/ADEQUACY.md`'s obligation table; a
  future reader of that document sees the current, accurate state.
- `_certificate_model.py` is now a second consumer point (alongside `test_certificate_fixtures.py`)
  for the independent certificate decoder; any future change to certificate semantics must keep
  both call sites' expectations in mind (though the underlying logic is now genuinely shared, not
  duplicated).

## Follow-ups

- The Lean-side `Sentence → Formula` elimination pass and its own truth-preservation theorem
  remain unbuilt in `~/Projects/BimodalLogic` — out of scope for this repository, tracked in
  `docs/TRUST_PIPELINE.md`'s "What remains" table.
- The pre-existing `TopOperator` bug (bare/nested `\top` fails `Sentence.update_types`) is
  unrelated to S4 and was not fixed here; `examples.py` already documents and routes around it.

## References

- `specs/196_discharge_s4_translation_bridge/plans/01_discharge-s4-translation-bridge.md`
- `specs/196_discharge_s4_translation_bridge/handoffs/phase-2-handoff-20260926T201304Z.md`
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_formula.py`
- `code/src/model_checker/theory_lib/bimodal/tests/unit/_certificate_model.py`
- `code/src/model_checker/theory_lib/bimodal/docs/ADEQUACY.md` §6.3
- `code/src/model_checker/theory_lib/bimodal/docs/TRUST_PIPELINE.md` Stage 1, "What remains"
