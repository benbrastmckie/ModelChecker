# Implementation Summary: Witness-family certificate redesign (certificate foundation layer)

- **Task**: 184 - Redesign the bimodal theory around witness-family certificates (discrete Z-time)
- **Status**: [IN PROGRESS]
- **Started**: 2026-09-25T18:03:00Z
- **Completed**: 2026-09-25T18:12:00Z
- **Effort**: ~4 hours (Phases 1-4 of 24; plan's own estimate for these four phases is 7.5 hours)
- **Dependencies**: None
- **Artifacts**: plans/01_witness-family-certificate-redesign.md
- **Standards**: summary-format.md, status-markers.md, artifact-management.md, tasks.md

## Overview

This dispatch implements Phases 1-4 of the 24-phase plan: the self-contained "certificate
foundation layer" -- a Lean-mirroring `Formula` ADT with subformula closure and a translation
from ModelChecker sentences, the `LabelledLasso`/`WitnessFamily` certificate datatypes with a
wire-format writer, and a pure-Python re-checker of the four certificate conditions (local
coherence, fulfilment, box faithfulness, target). None of this touches Z3, `BimodalSemantics`,
`operators.py`, `iterate.py`, `examples.py`, or the oracle -- those are Phases 6-24, not started.
The task remains at `[IMPLEMENTING]`; this is a deliberate mid-task handoff at a clean, fully
green, well-tested boundary (per the plan's own dependency-wave table, this is exactly Waves 1-2
plus the non-Z3 parts of Wave 3).

## What Changed

- Added `code/src/model_checker/theory_lib/bimodal/semantic/formula.py`: `Atom`/`Bot`/`Imp`/
  `Box`/`Untl`/`Snce` (frozen dataclasses, guard-first `Untl`/`Snce` matching the Lean
  constructor), `subformula_closure`/`closure_of`, `to_json`/`from_json` (verified against the
  existing fixture corpus), and `translate(sentence) -> Formula` for the 9 bimodal primitives
  (with the Until/Since guard/event swap and the `\Future`/`\Past` double-negation encoding).
- Added `code/src/model_checker/theory_lib/bimodal/semantic/certificate.py`: `LabelledLasso`
  (three-segment back/mid/fwd decoding), `WitnessFamily` (sparse box guess, non-empty lassos),
  `WitnessFamily.to_json` (the fixed wire shape), and `recheck()` (the four-condition
  re-verification, matching `check_certificate`'s verdict vocabulary and the proved window
  bounds from `Decide.lean`).
- Added `tests/unit/test_formula.py` (64 tests) and `tests/unit/test_certificate.py` (30 tests),
  all green. No existing file was modified.

## Decisions

- Confirmed (by inspection and by test) that `syntactic.DefinedOperator` instances are always
  fully expanded to the 9 primitives before `translate` sees a sentence -- `translate` needs no
  rules beyond those 9.
- `\Future`/`\Past` (ModelChecker's G/H) are encoded via the Lean-derived double-negation
  identity over `Untl`/`Snce` with a trivial guard, matching `Formula.allFuture`/`allPast`
  exactly.
- `recheck`'s structural check covers labels-outside-closure and fresh-indexed atoms, but not
  bx-keys-outside-closure -- `WitnessFamily.bx` is Lean-side a total, unrestricted function, and
  an unused key is inert rather than a precondition failure. This was tried the other way first,
  found to misrepresent the Lean semantics, and corrected (see Phase 4's handoff for detail).
- The positive fixture for the re-checker is a direct, by-hand port of `Examples.lean`'s
  Lean-verified `posFamily` (report 02 section 3, T3), not an independently invented example --
  the highest-confidence test available, since the Lean type-checker has already verified it.
- The two proved windows (wide `[-2nb, nm+2nf)` for local coherence/fulfilment, narrow
  `[-nb, nm+nf)` for box faithfulness) are implemented as separate functions per D7's correction,
  with a direct assertion that the wide window is what catches the window-discriminator
  fixture's violation and the narrow window would not.

## Plan Deviations

- Phase 2's truth-preservation property test (an amendment item) is implemented as two
  independent from-scratch pure-Python evaluators rather than by extracting a concrete model
  from the live (soon-to-be-replaced) `BimodalSemantics`/Z3 machinery -- recorded inline in the
  plan's Phase 2 section with the full rationale. Box is out of scope for that property test,
  matching the same limitation the plan text records for `oracle/bimodal_logic/ground_truth.py`.
- No other deviations. All other Phase 1-4 tasks completed exactly as specified.

## Impacts

- No behavioral change to any existing bimodal example, operator, or test: every addition is a
  new, unimported-by-anything-else module. The full bimodal suite was run once after Phase 2
  (377 passed, 5 pre-existing failures unrelated to this work, all in the old window-and-
  abundance encoding this task replaces) to confirm no regression from the additions.
- Phases 5-24 (round-trip against `lake exe check_certificate`; the Z3 label-bit encoding;
  `BimodalSemantics`/`BimodalProposition`/`BimodalStructure` rewrite; operators/iterate/examples
  migration; oracle rewrite; docs; `development`-marker removal) remain entirely to do. The task
  status should stay `[IMPLEMENTING]`, not move to any terminus.

## Follow-ups

- Next dispatch: Phase 5 (round-trip against `lake exe check_certificate`, which is present and
  built on this host at `~/Projects/BimodalLogic/.lake/build/bin/check_certificate`), then Phases
  6-9 (the Z3 encoding groundwork the A2-triangle sub-item of Phase 5 also needs).
- See `handoffs/phase-4-handoff-20260925T181126Z.md` for full phase-level detail and the "what
  not to try" notes.

## References

- `specs/184_refactor_bimodal_theory_tests_green_and_paper_lean_aligned/plans/01_witness-family-certificate-redesign.md`
- `specs/184_refactor_bimodal_theory_tests_green_and_paper_lean_aligned/handoffs/phase-2-handoff-20260925T180357Z.md`
- `specs/184_refactor_bimodal_theory_tests_green_and_paper_lean_aligned/handoffs/phase-4-handoff-20260925T181126Z.md`
- `code/src/model_checker/theory_lib/bimodal/semantic/formula.py`
- `code/src/model_checker/theory_lib/bimodal/semantic/certificate.py`
