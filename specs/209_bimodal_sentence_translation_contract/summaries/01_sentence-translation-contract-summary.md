# Implementation Summary: bimodal_sentence_translation_contract

- **Task**: 209 - bimodal_sentence_translation_contract
- **Status**: [COMPLETED]
- **Started**: 2026-09-28T07:09:00Z
- **Completed**: 2026-09-28T07:40:00Z
- **Effort**: ~2.5 hours (6-phase plan, all phases closed)
- **Dependencies**: Tasks 205 (certifying_countermodel_architecture) and 206
  (refactor_verification_test_harness), both completed prior to this task
- **Artifacts**: plans/01_sentence-translation-contract.md, reports/01_sentence-translation-contract.md
- **Standards**: summary-format.md, status-markers.md, artifact-management.md, tasks.md

## Overview

Discharged this repository's half of the certificate and sentence-translation contracts with
BimodalLogic, relocated here from BimodalLogic task 686. Of six originally-assumed items, only
two were real work: the `\top` extremal-operator defect in `Sentence.update_types` (item 6) and
the unwired sentence-translation conformance channel against BimodalLogic's fixture (item 5).
Items 1, 2, and 4 were verified as already landed and wired (via tasks 197/207); item 3's audit
was reconfirmed as a closed negative result. All six phases of the plan closed; the full
repository test suite is green with 46 new tests and zero regressions.

## What Changed

- **Item 6 (defect fix)**: `code/src/model_checker/syntactic/sentence.py`'s `store_types`
  extremal-operator branch now dispatches on `len(derived_type) == 1` (the shape of the derived
  type) rather than `self.name in {'\top', '\bot'}` (the original, pre-derivation operator name).
  `\top` (a `DefinedOperator` whose expansion is `[NegationOperator, [BotOperator]]`, a
  two-element derived type) was previously truncated to `(first_elem, None, None)`, discarding
  the negation's `BotOperator` argument; it now correctly falls through to the complex branch.
  `\bot` and logos' primitive `\top`/`\bot` are unaffected (genuinely one-element derived types).
- Added `TestExtremalOperatorUpdateTypes` (5 tests) to `test_formula.py`: bare `\top`
  type-updates with both `operator` and `arguments` set and translates to the two-`bot`
  implication shape (`Imp(Bot(), Bot())`); `\bot` is unchanged; nested `\top` (under `\Box`, and
  inside a conjunction) also type-updates and translates correctly.
- Removed the `\top` exclusion from `test_formula.py`'s `_BOX_TEST_CORPUS` (previously
  `[ast for ast in _GENERATED_CORPUS if ast[0] != "top"] + _BOX_PROPERTY_ASTS`, now the
  unfiltered `_GENERATED_CORPUS + _BOX_PROPERTY_ASTS`), and added `("top",)` and
  `("box", ("top",))` to `_BOX_PROPERTY_ASTS` so `\top` coverage is by construction.
- **Item 5 (conformance channel)**: created
  `code/src/model_checker/theory_lib/bimodal/tests/integration/test_sentence_translation_agreement.py`
  (new, ~330 lines). Two legs:
  - **Fixture-only leg** (always runs when the BimodalLogic checkout is present): renders each of
    BimodalLogic's 26 `Tests/fixtures/sentence-translation-fixtures.jsonl` rows' `sentence` field
    to this repository's infix syntax, builds the real type-updated `Sentence` via `Syntax`,
    calls `translate` + `to_json`, and asserts **dict equality** (never serialized-string
    comparison) against the row's `formula` field. Includes a row-count assertion (26), a
    `kind`-coverage assertion (`primitive`/`defined`/`asymmetry`/`nesting`), two individually
    named non-obvious-shape assertions (`\rightarrow` is disjunction-of-negation, `\future` is
    negated-universal), and an unknown-tag-fails-loudly test.
  - **Optional live differential leg** (skips cleanly when `lake`/the built binary are
    unavailable, independently of the fixture-only leg): invokes the built `translate_sentence`
    binary directly on a small representative selection (6 rows: one per kind plus `\top` and
    `\future p`) and compares its live output to the committed fixture, plus a negative-control
    sanity check that a deliberately corrupted expected value fails, not skips.
- Updated `code/src/model_checker/theory_lib/bimodal/tests/README.md`'s `integration/` table with
  a new row describing the module.

## Decisions

- **Items 1, 2, 4 verified, not reimplemented** (Phase 1): `assert_echo_matches_sent` defined and
  called at both consumer sites; `ensure_ascii=False` present at the sole wire-serialization site
  (`certificate.py:206`); both `.get("acceptance", "decided")` absent-default sites present.
  `test_certificate_lean_agreement.py` runs (11 passed, no skip).
- **Item 3 closed with a negative result, no work** (Phase 1): zero `.lean` files anywhere in
  this repository; no importer of `BimodalTools/CertificateImport`/`CanonicalWire` on this
  machine.
- **`translate_sentence` invoked directly, not through `lake exe`** (Phase 5): mirrors
  `_lean_check.py`'s own direct-invocation rationale (`semantic/checker.py`'s `_invoke`
  docstring) to avoid `lake`'s incremental build-check overhead on every call. `lake` on `PATH`
  is still checked as the buildability proxy `_lean_check.py` also uses; only the actual
  subprocess command differs from this plan's literal "invoke `lake exe translate_sentence`"
  wording.
- **`examples.py`'s `\neg \bot` hand-expansions left in place** (Phase 3, explicit decision):
  they are correct as written and now also mechanically identical to bare `\top`'s post-fix
  translation; rewriting them to use bare `\top` is an independently-motivated cleanup outside
  this task's Non-Goals. Their "avoid TopOperator bug" comments are now stale prose, not live
  workarounds.

## Plan Deviations

- **`BIMODAL_LOGIC_COMMIT` pin refresh (Phase 6) — not applied, recorded as a reasoned
  exclusion.** This plan's Phase 6 instructed refreshing `tests/_lean_check.py`'s
  `BIMODAL_LOGIC_COMMIT` constant. During this task's own Phase 1 baseline run, a concurrent
  sibling task (211, explicitly named in this task's dispatch as sharing `_lean_check.py`) landed
  "task 211 phase 2: retire the dead BIMODAL_LOGIC_COMMIT pin" (commit `ccedb978`), deleting the
  constant entirely with a documented rationale: it was "consumed by nothing" and had drifted
  twice before this task's own module existed, and the real enforcement mechanism is the live
  capability handshake in `semantic/checker.py`, not a commit pin. Task 211's own gate requires a
  repo-wide grep for `BIMODAL_LOGIC_COMMIT` to return zero hits in `code/`. Recreating the
  constant here would have directly undone a landed, reasoned sibling decision. Probed
  (`grep -rn "BIMODAL_LOGIC_COMMIT" code/` at Phase 6 implementation time: zero hits) and excluded
  per the pre-edit-gate contract rather than force-applied or silently skipped — full record in
  the plan's Phase 6 `#### Reasoned Exclusions` table. No source edit to `_lean_check.py` resulted
  from this task.
- All other plan items completed as specified; no other deviations.

## Impacts

- `syntactic/sentence.py`'s `store_types` is a core module shared by every theory
  (bimodal/logos/exclusion/imposition). The shape-keyed fix was verified behavior-identical
  outside bimodal by running the full repository suite before and after (3284 passed both
  before and after this specific edit, matching Phase 1's baseline plus the 5 new unit tests
  with zero non-bimodal changes).
- A new standing conformance channel now exists between this repository and BimodalLogic's
  source-sentence translation: any future drift in either side's operator elimination will be
  caught by `test_sentence_translation_agreement.py`'s fixture-only leg (always running when the
  checkout is present) rather than going unnoticed.
- `theory_lib/bimodal/tests/README.md` now documents the new module for future readers.

## Follow-ups

- None required to close this task. Noted for future, separate consideration (not owned by this
  task): `examples.py`'s now-stale "avoid TopOperator bug" comments could be simplified in a
  future drive-by cleanup; the citation-drift audit in `theory_lib/bimodal/docs/ADEQUACY.md`
  (catalogued by BimodalLogic, related to but out of scope for this task) remains uncoordinated.

## References

- `specs/209_bimodal_sentence_translation_contract/plans/01_sentence-translation-contract.md`
  (this task's plan, all 6 phases `[COMPLETED]` or `[COMPLETED WITH EXCLUSIONS]`)
- `specs/209_bimodal_sentence_translation_contract/reports/01_sentence-translation-contract.md`
  (this task's research report)
- `/home/benjamin/Projects/BimodalLogic/specs/686_modelchecker_contract_handoffs/` (upstream
  research and plan this task adopted, per the dispatch's explicit instruction)
- `/home/benjamin/Projects/BimodalLogic/BimodalTools/README.md`'s "Source-sentence translation
  protocol" section (the consuming-side obligation this task discharges)
- `code/src/model_checker/theory_lib/bimodal/tests/integration/test_sentence_translation_agreement.py`
  (new)
- `code/src/model_checker/syntactic/sentence.py` (modified)
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_formula.py` (modified)
- `code/src/model_checker/theory_lib/bimodal/tests/README.md` (modified)
