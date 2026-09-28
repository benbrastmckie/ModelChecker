# Research Report: Task #209

- **Task**: 209 - bimodal_sentence_translation_contract
- **Started**: 2026-09-28
- **Completed**: 2026-09-28 (this report)
- **Effort**: ~1h (verification-only pass against a complete, strict-validated upstream round)
- **Dependencies**: Sequenced after task 205 (certifying_countermodel_architecture) and task 206
  (refactor_verification_test_harness), both `completed` per `specs/state.json` at the time of
  this research
- **Sources/Inputs**: Upstream research and plan authored in the BimodalLogic repository (task
  686, relocated here per the dispatch), plus live re-verification of every cited claim against
  this repository's current tree (post-205/206/207/208)
- **Artifacts**: this report
- **Standards**: report-format.md, subagent-return.md

## Executive Summary

- **The upstream research and plan (BimodalLogic task 686) are correct and current.** This
  research round re-verified every load-bearing claim in both documents against this
  repository's tree as it stands today (after tasks 197, 205, 206, 207, 208 have all landed) and
  found **no drift**: every file:line citation, every "already landed" claim, and every
  "genuinely open" claim still holds exactly as described. **Adopt the upstream plan; do not
  rederive.**
- **Two items are real, outstanding work here**: item 6 (the `\top` defect in
  `Sentence.update_types`) and item 5 (the unwired sentence-translation conformance channel),
  with 6 a hard prerequisite for 5 because fixture row 13 is a `\top` sentence.
- **Three items are already fully landed** (echo comparison, `ensure_ascii=False`, the
  `"acceptance"` absent-default) — verification-only, confirmed live in this pass (see
  Verification section below). **One item (the out-of-repo Lean consumer audit) is closed with a
  confirmed negative result** — no re-search performed, per the dispatch's explicit instruction.
- **The sequencing gate is satisfied**: `specs/state.json` shows task 205
  (`certifying_countermodel_architecture`) and task 206 (`refactor_verification_test_harness`)
  both at `status: "completed"`, so the file-collision risk the dispatch flagged (both tasks
  touch `_lean_check.py`, `tests/README.md`, `test_certificate_lean_agreement.py`,
  `test_semantics_core.py`) is now resolved — this task can proceed against their landed state
  rather than racing them.
- **One correction to carry forward**: the upstream plan's commit-prefix assumption
  (`bimodal-contract:`) is explicitly superseded by the dispatch's provenance note — this task
  now has its own number (209) in this repository's sequence, so ordinary `task 209: {action}`
  commit messages are correct, not the upstream placeholder prefix.
- **One staleness fact worth carrying into planning**: `_lean_check.py`'s pinned
  `BIMODAL_LOGIC_COMMIT` (`d55e2760e...`) predates the translation channel's landing
  (BimodalLogic commit `c8940c305`, task 679 phase 4, current BimodalLogic `HEAD` is
  `e3155fd3204...`). Phase 6 of the upstream plan already accounts for refreshing this pin.

## Context & Scope

This is a relocated task: the research and plan were authored in the BimodalLogic repository
(task 686) because that repository's contract documents (`BimodalTools/README.md`,
`FormalSystem/SourceLanguage/Sentence.lean`, `Tests/fixtures/sentence-translation-fixtures.jsonl`)
are the source of truth for what ModelChecker must implement, but every source edit lands here in
ModelChecker. The dispatch is explicit that a fresh single-repo research round would be "strictly
weaker" than the upstream cross-repository audit, and instructs reading both upstream artifacts
rather than rederiving. This report therefore does not repeat the cross-repository investigation;
it (a) summarizes the upstream findings, and (b) re-verifies every claim against this repository's
**current** tree — which has moved forward by four completed tasks (197, 205, 206, 207) and one
more (208) since the upstream round — to confirm nothing has drifted before planning proceeds.

Scope of this pass: read both upstream artifacts in full; re-run the grep/read checks the upstream
report's Appendix lists, against the current tree; confirm the sequencing dependency
(tasks 205/206 status); confirm no naming collision for the new test module; confirm the fixture's
shape (row count, kind/tag vocabulary) directly from the live BimodalLogic checkout. No web search
was needed (fully internal, cross-repository contract conformance question, same as the upstream
round).

## Findings

### Upstream documents adopted as-is

- **Research**: `/home/benjamin/Projects/BimodalLogic/specs/686_modelchecker_contract_handoffs/reports/01_modelchecker-contract-handoffs.md`
- **Plan** (6 phases, 5 waves, `--strict` PASS): `/home/benjamin/Projects/BimodalLogic/specs/686_modelchecker_contract_handoffs/plans/01_modelchecker-contract-handoffs.md`

Both are read in full as part of this research and are the authoritative basis for planning. The
summary below is for this report's own record; the plan phase should read the upstream plan
directly rather than work from this summary alone.

**What is outstanding** (upstream's framing, re-confirmed live in this pass):
- **Item 6** (fix first): `Sentence.update_types`'s `store_types` extremal-operator branch keys
  off `self.name in {'\\top', '\\bot'}` (the *original* operator name) instead of the shape of
  `derived_type`. `\bot` is a genuine primitive (one-element derived type, branch is correct for
  it); `\top` is `bimodal`'s `TopOperator`, a `DefinedOperator` whose `derived_definition`
  produces `[NegationOperator, [BotOperator]]` — a two-element derived type — so the branch fires
  anyway (on name) and discards the expansion, returning `(first_elem, None, None)` instead of
  falling through to the complex-sentence branch just below it. Fix direction: dispatch on
  `len(derived_type) == 1` rather than `self.name`.
- **Item 5** (depends on 6): nothing in this repository consumes
  `Tests/fixtures/sentence-translation-fixtures.jsonl` (26 rows, 4 `kind` values, 18 sentence
  tags). A new integration test module must build each fixture row's `sentence` AST through the
  real `Syntax` pipeline, run `update_types` + `translate` + `to_json`, and assert dict equality
  (never byte/string equality) against the row's `formula` field. Natural home:
  `theory_lib/bimodal/tests/integration/`, following `_lean_check.py`'s skip-resolution idiom,
  with a **distinct**, checkout-absence-only skip reason (not `SKIP_REASON`, which additionally
  requires `lake` and a binary probe this leg does not need).
- **Already landed, verify only**: echo comparison (`assert_echo_matches_sent`), the sole
  producer's `ensure_ascii=False`, and the `.get("acceptance", "decided")` absent-default in both
  consumers.
- **Closed, negative result, no work**: no out-of-repository `.lean` consumer of
  `CheckResult.countermodel`'s two-argument shape exists anywhere on this machine (zero `.lean`
  files in this repository; zero hits across every other `~/Projects/*` checkout).

### Live re-verification performed in this pass

All of the following were checked directly against this repository's current tree (commit history
through `37ffbd98`, tasks 197/205/206/207/208 all landed) rather than trusted from the upstream
report's citations alone:

1. **Item 6's defect, still present exactly as described.**
   `code/src/model_checker/syntactic/sentence.py`'s `store_types` nested function still reads:
   ```python
   # Check for extremal operator
   if self.name in {'\\top', '\\bot'}:
       return first_elem, None, None
   ```
   immediately after the sentence-letter (`is_const`) check and immediately before the
   `len(derived_type) > 1` complex-sentence branch — the exact structure the upstream plan's
   Phase 2 targets. No intervening task has touched this function.

2. **`TopOperator.derived_definition`, confirmed two-element** (matching the upstream *plan's*
   correction of the upstream *research report's* three-element claim — the plan is the more
   carefully verified of the two documents on this specific point):
   `code/src/model_checker/theory_lib/bimodal/operators.py:504-518`:
   ```python
   class TopOperator(syntactic.DefinedOperator):
       name = "\\top"
       arity = 0
       def derived_definition(self):
           return [NegationOperator, [BotOperator]]
   ```

3. **Logos' `\top`/`\bot` remain primitive**, confirmed at
   `code/src/model_checker/theory_lib/logos/subtheories/extensional/operators.py:213` (
   `class TopOperator(syntactic.Operator)`) and `:249` (`class BotOperator(syntactic.Operator)`)
   — both subclass the primitive base, not `DefinedOperator`, so a shape-keyed branch changes
   nothing for logos. This bounds the blast radius exactly as the upstream plan's Scope Hypothesis
   states; the plan's own mitigation (run the **full** suite, not just bimodal, at Phase 2) is the
   correct verification tier and should be carried into this task's plan unchanged.

4. **Corroborating workaround comments, unchanged**:
   `code/src/model_checker/theory_lib/bimodal/examples.py:1050,1069` still read
   `# Note: \top = \neg \bot (explicit expansion to avoid TopOperator bug)`, and
   `code/src/model_checker/theory_lib/bimodal/tests/unit/test_formula.py:962-968` still excludes
   `\top` from `_BOX_TEST_CORPUS` with the same defect-citing comment. Neither has been touched by
   tasks 205/206/207/208.

5. **Item 5, still genuinely zero references.** `grep -rln "translate_sentence\|sentence-translation-fixtures"` across the whole repository (code and non-archived docs) returns nothing.

6. **The three "already landed" items, all still present and wired**, post-205/206/207:
   - `assert_echo_matches_sent` is defined in `_lean_check.py:173` and **called** at
     `test_certificate_lean_agreement.py:148,173,190` and `test_semantics_core.py:290` — the same
     three call sites the upstream report cites, confirmed to have survived task 205's rewrite of
     `test_certificate_lean_agreement.py`/`test_semantics_core.py` and task 206's restructuring of
     the `tests/` tree.
   - `certificate.py:206`: `json.dumps(payload, separators=(",", ":"), ensure_ascii=False)` — the
     sole serializing call site, docstring at `:195-198` still names it as the BimodalLogic
     phase-9 hand-off.
   - `.get("acceptance", "decided")` present at `test_certificate_lean_agreement.py:137` and
     `test_semantics_core.py:279`.

7. **No naming collision for the new module.** Current
   `theory_lib/bimodal/tests/integration/` contents: `test_certificate_a2_triangle.py`,
   `test_certificate_lean_agreement.py`, `test_data_extraction.py`, `test_injection.py`,
   `test_iterate.py`, `test_output_gate.py`, `test_search_period_coverage.py`,
   `test_until_since_integration.py`. The upstream plan's proposed
   `test_sentence_translation_agreement.py` is free.

8. **The fixture itself, read live from the resolved BimodalLogic checkout** (not a stale mirror):
   26 rows; `kind` values exactly `{primitive, defined, asymmetry, nesting}`; 18 distinct
   `sentence.tag` values (`allFut, allPast, atom, bicond, bot, box, cond, dia, neg, next, prev,
   snce, someFut, somePast, top, untl, vee, wedge`) — matching the upstream plan's stated counts
   exactly.

9. **Sequencing dependency, satisfied.** `specs/state.json`: task 205
   (`certifying_countermodel_architecture`) and task 206 (`refactor_verification_test_harness`)
   both show `"status": "completed"`. The dispatch's stated reason to sequence after both —
   avoiding a collision on `_lean_check.py`, `tests/README.md`,
   `test_certificate_lean_agreement.py`, `test_semantics_core.py`, since neither declares this
   task's files in a `file_scope` — no longer applies as a live race; this task can read and edit
   those files' **current, landed** contents directly. (Task 212,
   `consolidate_remaining_bimodal_test_helpers`, is `not_started` and unrelated to this task's
   files by name; task 211 is `researching` and, per the dispatch's Territory block, has no
   declared `file_scope`, so the standard concurrent-siblings discipline in
   `context/contracts/territory.md` still applies for any dispatch overlapping this cycle.)

10. **Pin staleness, relevant to the upstream plan's Phase 6.**
    `_lean_check.py:99`: `BIMODAL_LOGIC_COMMIT = "d55e2760e6731a2240f3db5d761658947bf69125"`.
    The translation channel landed in three later BimodalLogic commits
    (`19a893bcd`, `fb6a90537`, `c8940c305` — task 679, phases 1/2/4), and BimodalLogic's current
    `HEAD` is `e3155fd3204fcf1f7e76c5094f796cd017ef33a8`. The upstream plan's Phase 6 already
    directs refreshing this pin to "the BimodalLogic commit that actually landed the translation
    channel," resolved via `git log` at implementation time rather than copied from any research
    artifact — that instruction remains correct and should not be short-circuited by pasting
    `c8940c305` (or `HEAD`) directly without re-resolving at implementation time, since the
    BimodalLogic tree may move again before this task implements.

### One correction to the upstream plan, per this task's own dispatch

The upstream plan's "Assumptions" section proposes a `bimodal-contract:` commit-message prefix in
ModelChecker to avoid falsely claiming a BimodalLogic task number. This task's own dispatch
(Provenance Note) supersedes that: because this work now has its own number in *this*
repository's sequence (209), ordinary `task 209: {action}` commit messages are correct, and the
upstream placeholder prefix should **not** be carried into implementation. This is a
one-line correction to an otherwise-adoptable plan, not a reason to rederive it.

## Decisions

- **Adopt the upstream plan (BimodalLogic task 686, `plans/01_modelchecker-contract-handoffs.md`)
  as the basis for this task's plan**, with two adjustments for the planning phase to make
  explicit:
  1. Commit messages use `task 209: {action}`, not the upstream's `bimodal-contract:` placeholder.
  2. Phase 6's summary artifact path in the upstream plan
     (`specs/686_modelchecker_contract_handoffs/summaries/...` in BimodalLogic) does not apply
     here; this task's summary lands at
     `specs/209_bimodal_sentence_translation_contract/summaries/` in this repository per this
     repository's own artifact conventions, and nothing should be written back into BimodalLogic
     (the dispatch is explicit on this point).
  3. Everything else — the 6-phase structure, the 5-wave dependency graph, the shape-keyed fix
     direction, the fixture-only-then-optional-differential test split, the pin refresh, and the
     README update — is directly reusable without rederivation.
- **Treat items 1, 2, and 4 as verification-only** in the plan, exactly as upstream concluded;
  this pass independently re-confirmed all three are still landed and wired post-205/206/207.
- **Treat item 3 as closed with a negative result.** No further search.
- **Sequence item 6 before item 5**, per both the upstream plan and the fixture's row-13 `\top`
  dependency, independently confirmed by reading the live fixture in this pass.

## Risks & Mitigations

Carried forward from the upstream plan (independently re-confirmed relevant in this pass):

- **Risk**: the `store_types` shape-keyed fix changes behavior in a non-bimodal theory.
  **Mitigation**: confirmed logos' `\top`/`\bot` are primitive (this pass, item 3 above); the
  plan's Phase 2 still correctly specifies running the **full** test suite, not just bimodal, as
  the tie-break verification tier for a shared-module dispatch-behavior change.
- **Risk**: re-implementing items 1/2/4 at face value. **Mitigation**: this pass's own
  file:line re-verification (section above) gives an independently fresh, post-205/206/207 basis
  for the same "verify, don't reimplement" instruction the dispatch already states.
- **Risk**: the fixture pin (`BIMODAL_LOGIC_COMMIT`) is stale relative to what actually landed the
  translation channel. **Mitigation**: Phase 6 already directs resolving the correct commit via
  `git log` at implementation time, not from a cached value; this report's own citation of
  `c8940c305`/`e3155fd3204...` is for context only, not a value to paste in verbatim (the
  BimodalLogic tree may move further before implementation starts).
- **Risk**: concurrent siblings this cycle (task 211, no declared `file_scope`) touch overlapping
  files. **Mitigation**: standard territory discipline — re-read before editing, stage only named
  files, no destructive git commands, per `context/contracts/territory.md`.

## Context Extension Recommendations

None. This is a verification pass over an already-complete, cross-repository research/plan round;
no recurring pattern surfaced here beyond what the upstream report already recorded.

## Appendix

### Files read (this repository, this pass)

- `code/src/model_checker/syntactic/sentence.py:150-260` (`update_types`, `store_types`)
- `code/src/model_checker/theory_lib/bimodal/operators.py:504-519` (`TopOperator`)
- `code/src/model_checker/theory_lib/logos/subtheories/extensional/operators.py:213,249`
  (`TopOperator`, `BotOperator`, primitivity)
- `code/src/model_checker/theory_lib/bimodal/examples.py:1050,1069`
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_formula.py:950-1030`
  (`_BOX_PROPERTY_ASTS`, `_BOX_TEST_CORPUS`, `_sentence` helper at :70-77)
- `code/src/model_checker/theory_lib/bimodal/tests/_lean_check.py` (full — `resolve_bimodal_logic_path`,
  `SKIP_REASON`, `BIMODAL_LOGIC_COMMIT`, `assert_echo_matches_sent`)
- `code/src/model_checker/theory_lib/bimodal/tests/integration/test_certificate_lean_agreement.py:130-195`
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_semantics_core.py:225-290`
- `code/src/model_checker/theory_lib/bimodal/semantic/certificate.py:190-206`
- `code/src/model_checker/theory_lib/bimodal/semantic/formula.py:1-40,323-343`
- `code/src/model_checker/theory_lib/bimodal/tests/README.md:1-80`
- `specs/state.json` (task 205/206/207/208/209/211/212 status entries)
- `specs/209_bimodal_sentence_translation_contract/.dispatch/1.md` (this dispatch, in full)

### Files read (BimodalLogic, this pass)

- `specs/686_modelchecker_contract_handoffs/reports/01_modelchecker-contract-handoffs.md` (full)
- `specs/686_modelchecker_contract_handoffs/plans/01_modelchecker-contract-handoffs.md` (full)
- `Tests/fixtures/sentence-translation-fixtures.jsonl` (row count, `kind`/tag vocabulary,
  read live via Python)
- `git log --oneline -- FormalSystem/SourceLanguage/ Tests/fixtures/sentence-translation-fixtures.jsonl`
  (task 679 commits `19a893bcd`, `fb6a90537`, `c8940c305`), current `HEAD` (`e3155fd3204...`)

### Commands run

```
git log --oneline -20 -- code/src/model_checker/theory_lib/bimodal/ code/src/model_checker/syntactic/sentence.py
grep -rn "assert_echo_matches_sent" code/src/model_checker/theory_lib/bimodal/tests/
grep -n "ensure_ascii" code/src/model_checker/theory_lib/bimodal/semantic/certificate.py
grep -rn '.get("acceptance"' code/src/model_checker/theory_lib/bimodal/tests/
grep -rln "translate_sentence\|sentence-translation-fixtures" . --exclude-dir=specs
find code/src/model_checker/theory_lib/bimodal/tests/integration -name "*.py"
python3 -c "... fixture row-count / kind / tag audit ..." (BimodalLogic checkout)
```

No web search was performed (not needed; internal contract-conformance verification only, same
conclusion the upstream round reached).
