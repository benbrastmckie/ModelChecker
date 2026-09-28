# Implementation Plan: Task #209

- **Task**: 209 - bimodal_sentence_translation_contract
- **Status**: [IMPLEMENTING]
- **Effort**: 6 hours
- **Dependencies**: Tasks 205 (certifying_countermodel_architecture) and 206
  (refactor_verification_test_harness) — both `completed` per `specs/state.json`, so the
  sequencing gate is satisfied and this task proceeds against their landed state
- **Research Inputs**: specs/209_bimodal_sentence_translation_contract/reports/01_sentence-translation-contract.md
  (which adopts, and re-verifies live, the upstream BimodalLogic research and plan at
  `/home/benjamin/Projects/BimodalLogic/specs/686_modelchecker_contract_handoffs/`)
- **Artifacts**: plans/01_sentence-translation-contract.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: python
- **Lean Intent**: false

## Overview

Discharge this repository's half of the certificate and sentence-translation contracts that the
BimodalLogic repository has already landed. Only two of the six originally-assumed items are real
work here: the `\top` defect in `Sentence.update_types` (item 6) and the unwired translation
conformance channel (item 5), with 6 a hard prerequisite for 5 because at least one fixture row is
a `\top` sentence. Items 1, 2 and 4 are already implemented and wired here and get a verification
pass only; item 3's audit is closed with a confirmed negative result and gets no phase. Done means:
`store_types`'s extremal branch dispatches on the derived shape rather than the original operator
name, a new integration module asserts this repository's own `update_types` + `translate` +
`to_json` against every fixture row as **parsed JSON**, and the `\top` exclusion in
`_BOX_TEST_CORPUS` is removed because the defect it routed around is gone.

### Research Integration

Findings carried directly into the phase structure (each independently re-verified against the
current tree in this task's own research pass, post-197/205/206/207/208):

- **Items 1/2/4 are already landed and wired**: `assert_echo_matches_sent` defined at
  `_lean_check.py:173` and called at `test_certificate_lean_agreement.py:148,173,190` and
  `test_semantics_core.py:290`; `ensure_ascii=False` at the sole wire-serialization site
  (`certificate.py:206`); `.get("acceptance", "decided")` at
  `test_certificate_lean_agreement.py:137` and `test_semantics_core.py:279`. Phase 1 **verifies**
  these; it must not reimplement them. Re-doing them at face value from a stale description is the
  single most likely failure mode of this task.
- **Item 3 has no target**: zero `.lean` files in this repository, zero importers of
  `BimodalTools/CertificateImport`/`CanonicalWire` anywhere on this machine. Recorded as a closed
  negative-result audit; no phase, no re-search.
- **Item 6 is located precisely** at `code/src/model_checker/syntactic/sentence.py`'s `store_types`
  nested function, whose extremal branch tests `self.name in {'\\top', '\\bot'}` — the *original*
  operator name — instead of the shape of `derived_type`. Confirmed still present verbatim,
  immediately after the `is_const` sentence-letter check and immediately before the
  `len(derived_type) > 1` complex branch.
- **`TopOperator.derived_definition` returns `[NegationOperator, [BotOperator]]`** — a
  **two**-element derived type (`operators.py:504-518`). The name-keyed branch therefore fires
  anyway and discards the expansion, returning `(first_elem, None, None)`.
- **Logos' `\top`/`\bot` are primitive** `syntactic.Operator`s
  (`logos/subtheories/extensional/operators.py:213,249`), so their derived type is genuinely one
  element and a shape-keyed branch is behavior-identical there. This bounds — but does not prove —
  the blast radius; Phase 2 carries it as a Scope Hypothesis confirmed by a **full**-suite run.
- **Item 6 gates item 5**: the fixture contains a `\top` row, so the fixture loop cannot pass on
  all rows while the defect is open.
- **Comparison must be on parsed JSON, never bytes**: both repositories' docs say so independently,
  and the fixture shows why — Lean prints `untl` with `event` before `guard`, this repository's
  `to_json` emits the same two keys in the other order.
- **Zero current references** to `translate_sentence` or `sentence-translation-fixtures` anywhere
  in this repository; `test_sentence_translation_agreement.py` is a free name in
  `theory_lib/bimodal/tests/integration/`.
- **The pin is stale**: `_lean_check.py:99` pins `BIMODAL_LOGIC_COMMIT =
  "d55e2760e6731a2240f3db5d761658947bf69125"`, which predates the translation channel's landing.
  Phase 6 refreshes it by resolving the commit via `git log` at implementation time — **not** by
  pasting any value from this plan or from the research report, since the BimodalLogic tree may
  move again before implementation.

### Prior Plan Reference

The upstream BimodalLogic plan
(`/home/benjamin/Projects/BimodalLogic/specs/686_modelchecker_contract_handoffs/plans/01_modelchecker-contract-handoffs.md`,
6 phases, 5 waves, `--strict` PASS) was read in full and is the basis for this plan's structure,
per the dispatch's explicit instruction to adopt rather than rederive. Three adaptations for this
repository:

1. **Commit messages use `task 209: {action}`** (and `task 209 phase {P}: {name}`), not the
   upstream plan's `bimodal-contract:` placeholder prefix. That prefix existed only to avoid
   falsely claiming a number in this repository's sequence; this work now has its own number, so
   the workaround is superseded and must not be carried over.
2. **The implementation summary lands here**, at
   `specs/209_bimodal_sentence_translation_contract/summaries/01_sentence-translation-contract-summary.md`,
   under this repository's own artifact conventions. **Nothing is written under
   `/home/benjamin/Projects/BimodalLogic`** — that checkout is read-only for this task.
3. Phase 1's baseline and Phase 6's final gate are expressed in this repository's own commands
   (`PYTHONPATH=code/src pytest ...` from the project root).

Everything else — the six-phase structure, the five-wave dependency graph, the shape-keyed fix
direction, the fixture-only-then-optional-differential split, the pin refresh, and the README
update — is reused as-is.

### Roadmap Alignment

No `roadmap_path` was provided in this dispatch and no roadmap flag is set, so no roadmap phases
are included. `specs/ROADMAP.md` must not be modified by this task.

## Goals & Non-Goals

**Goals**:
- Fix the `\top` defect in `Sentence.update_types` so the extremal branch dispatches on the derived
  shape rather than on the original operator name.
- Remove the `\top` exclusion from `test_formula.py`'s `_BOX_TEST_CORPUS`, proving the fix from the
  site that documented the defect.
- Add a translation conformance test asserting, for every fixture row, that this repository's
  `update_types` + `translate` + `to_json` equals the fixture's `formula` field as parsed JSON.
- Add an optional, skippable differential leg against `lake exe translate_sentence`.
- Verify items 1, 2 and 4 still hold, and record item 3's negative result.
- Refresh `BIMODAL_LOGIC_COMMIT` and describe the new module in the bimodal tests README.

**Non-Goals**:
- Re-implementing items 1, 2 or 4. They are landed; source edits to those three sites are out of
  scope.
- Searching further for an out-of-repository Lean consumer of `CheckResult.countermodel` (item 3).
- Un-routing `examples.py`'s `\neg \bot` hand-expansions. Phase 3 makes an explicit, recorded
  decision to leave them rather than silently skipping the question.
- Any inverse (formula-to-sentence) pass. `tr` is not injective, so the channel is forward-only.
- Any write under `/home/benjamin/Projects/BimodalLogic` (read-only for this task).
- Coordinating the separately-catalogued `theory_lib/bimodal/docs/ADEQUACY.md` citation drift —
  related, explicitly out of scope here.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| An implementer re-does items 1/2/4 at face value from the task description | M | M | Phase 1 is verification-only and forbids source edits to those three sites; the research report carries file:line evidence checkable in under a minute |
| The `store_types` fix changes behavior in a non-bimodal theory | H | L | Research confirmed logos' `\top`/`\bot` are primitive (one-element derived type), so the shape-keyed branch is behavior-identical there; Phase 2 runs the **full** suite, not the bimodal subset, as the tie-break tier for a shared-module dispatch change |
| A concurrent sibling (task 211, no declared `file_scope`) edits an overlapping file on this shared tree | H | M | Re-read every target immediately before editing; stage only this plan's explicitly named files by exact path; never a directory or glob pathspec, never `git add -A`, never a destructive git command; treat a foreign commit or foreign uncommitted modification as a STOP-and-report condition after checking `git log` |
| The fixture read skips silently when the BimodalLogic checkout is absent, hiding a real disagreement | M | M | Phase 4 uses a distinct, named checkout-absence-only skip reason (not `SKIP_REASON`) and asserts the row count, so a truncated or partially-read fixture fails loudly instead of passing vacuously |
| A live differential leg costs one subprocess per fixture row | M | M | The fixture-only leg is the primary, always-run leg; Phase 5 probes once and compares a small representative selection, mirroring `_lean_check.py`'s probe-once idiom |
| The pin is refreshed from a value copied out of an artifact rather than resolved live | M | M | Phase 6 resolves the commit via `git log` in the BimodalLogic checkout at implementation time; no plan or report value is pasted verbatim |

### Assumptions (stated, not blocking)

- **Fixture source of truth**: the new test reads
  `Tests/fixtures/sentence-translation-fixtures.jsonl` from the resolved BimodalLogic checkout
  rather than from a copy mirrored into this repository. One source of truth cannot drift, and
  drift is exactly what this channel exists to detect; the cost is a loudly-named skip when no
  checkout is present.
- **Commit convention**: ordinary `task 209: {action}` / `task 209 phase {P}: {name}` messages,
  per this repository's own `git-workflow.md`.

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3, 4 | 2 |
| 4 | 5 | 4 |
| 5 | 6 | 3, 4, 5 |

Phases within the same wave can execute in parallel.

---

### Phase 1: Verify the already-landed items and establish a green baseline [COMPLETED]

**Goal**: Confirm items 1, 2 and 4 still hold, record item 3's negative result, and establish that
this repository's test suite is green *before* any edit, so a later failure is attributable.

**Tasks**:
- [x] Confirm the repository is on `master` and record the exact starting commit, so every later
      change is attributable and revertible.
- [x] Record the pre-existing dirty state (`git status --short`) so concurrent in-flight work from
      other sessions is distinguishable from this task's own changes throughout.
- [x] Run `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/integration/test_certificate_lean_agreement.py -v`
      and confirm it **runs** (does not skip). A clean skip means the BimodalLogic checkout or
      `lake` is unavailable — resolve it or record it explicitly; a skip is not a pass.
- [x] Confirm item 1 is actually exercised: `assert_echo_matches_sent` is reached on the
      `countermodel` path and both `error`-path negative checks pass.
- [x] Confirm `PROTOCOL_FAILURE` is `None` (`TestErrorPaths`) — a binary that answers wrongly must
      fail loudly, not skip.
- [x] Confirm item 2 by reading `semantic/certificate.py`'s `canonical_wire_bytes` and verifying
      `ensure_ascii=False` is present on the single serializing `json.dumps`.
- [x] Confirm item 4 by reading both `.get("acceptance", "decided")` sites
      (`tests/integration/test_certificate_lean_agreement.py`, `tests/unit/test_semantics_core.py`).
- [x] Record item 3's negative result (zero `.lean` files here; no importer of
      `BimodalTools.CertificateImport`/`CanonicalWire` anywhere under `~/Projects/`) in the
      progress record. No audit re-run.
- [x] Run the full suite once (`PYTHONPATH=code/src pytest code/tests/ code/src/model_checker -q`
      or the project's documented equivalent) to capture the pre-edit baseline, and record any
      pre-existing failures so they are not later misread as regressions.

**Timing**: 0.75 hours

**Depends on**: none

**Verification Tier**: local

Rationale: this phase makes no source edit and has no blast radius of its own; its purpose is to
establish the baseline that Phase 2's `full` tier is measured against.

**Files to modify**: none (verification only)

**Verification**:
- `test_certificate_lean_agreement.py` runs and passes, with no skip. **Confirmed**: 11 passed,
  0 skipped (`TestProtocolFailureIsLoud`, `TestLeanAgreement` x4, `TestErrorPaths` x2,
  `TestPythonRecheckerAgreesWithLean` x4).
- `ensure_ascii=False` confirmed present at the single wire-serialization site
  (`semantic/certificate.py:206`, the sole `json.dumps` call in that module).
- Both `"acceptance"` absent-default sites confirmed present
  (`test_certificate_lean_agreement.py:137`, `test_semantics_core.py:279`:
  `.get("acceptance", "decided")`).
- Item 1 fully confirmed: `assert_echo_matches_sent` defined at `_lean_check.py:173`, called at
  `test_certificate_lean_agreement.py:148,173,190` and `test_semantics_core.py:290`;
  `test_protocol_failure_is_none` passes.
- Item 3 negative result reconfirmed: `find . -name "*.lean"` returns zero results repo-wide.
- **Pre-edit baseline** (starting commit `c857d326155cee0f9e82c6a3cd46c8e43fc04a23`, branch
  `master`): `PYTHONPATH=code/src pytest code/tests/ code/src/model_checker -q` ->
  **3279 passed, 5 skipped, 2 warnings in 378.27s**. No pre-existing failures.
- **Pre-existing dirty paths at start** (concurrent in-flight work from other sessions, not this
  task's own): `specs/211_correct_kernel_checked_proof_overclaim/plans/01_kernel-checked-proof-overclaim.md`,
  `specs/TODO.md`, `specs/events.jsonl`, `specs/state.json`, plus this plan file's own
  pre-existing `[NOT STARTED]` -> `[IMPLEMENTING]` status-field edit from orchestrator preflight.
- **Concurrent sibling observed live**: task 211 (declared concurrent-sibling territory, no
  `file_scope`) landed 4 commits (`4fcf6968`..`1cd23cfb`) during this phase's baseline run,
  editing `code/src/model_checker/theory_lib/bimodal/docs/ADEQUACY.md` (doc-only, not in this
  task's `file_scope`) and, in its own phase 2, **retiring the `BIMODAL_LOGIC_COMMIT` constant**
  this plan's Phase 6 was written to refresh (`ccedb978`, "task 211 phase 2: retire the dead
  BIMODAL_LOGIC_COMMIT pin" — removed from `tests/_lean_check.py` because it was "consumed by
  nothing" and had already drifted; task 211's own plan explicitly names this task as the
  concurrent sibling sharing `tests/_lean_check.py`). This is carried forward as a scope
  adaptation for Phase 6 below rather than re-litigated here: no foreign commit touches this
  task's declared `file_scope`, so no collision, but Phase 6's literal "refresh
  BIMODAL_LOGIC_COMMIT" instruction is now inapplicable (probed and confirmed absent) and will be
  recorded as a reasoned exclusion when Phase 6 opens, not re-created against task 211's landed
  and reasoned decision.

---

### Phase 2: Fix the `\top` defect in `Sentence.update_types` [NOT STARTED]

**Goal**: Make `store_types`'s extremal-operator branch dispatch on the shape of `derived_type`
rather than on `self.name`, so a defined nullary operator whose expansion is complex falls through
to the complex branch it belongs in.

**Tasks**:
- [ ] Re-read `code/src/model_checker/syntactic/sentence.py`'s `store_types` immediately before
      editing (the tree is shared with concurrent work).
- [ ] Replace `if self.name in {'\\top', '\\bot'}:` with a shape-keyed test on `derived_type` (the
      natural form is `len(derived_type) == 1`), kept after the existing `is_const` sentence-letter
      check so a one-element `Const` still takes the letter branch first.
- [ ] Update the branch's comment (and the detection-logic comment block above it) to say what the
      branch now means — a nullary/extremal *derived* shape — rather than naming `\top`/`\bot` by
      surface spelling.
- [ ] Confirm the trailing `ValueError` fallthrough is still reachable only for genuinely invalid
      shapes: not made dead, and not newly reachable for valid input.
- [ ] Add a focused unit assertion that `\top` now type-updates correctly: a `\top` sentence has a
      non-`None` `operator` **and** non-`None` `arguments`, and `to_json(translate(...))` equals
      the two-`bot` implication shape its `[NegationOperator, [BotOperator]]` expansion implies
      (confirm the exact expected dict by running it, not by copying it from this plan).
- [ ] Add a companion assertion that `\bot` is unchanged: `arguments` remain `None` and it still
      translates to `{"tag": "bot"}`.
- [ ] Add an assertion that a *nested* `\top` (e.g. `\Box \top`, `(\top \wedge p)`) also
      type-updates and translates correctly, not only a bare one.
- [ ] Run the **full** test suite and compare against Phase 1's baseline — in particular the logos,
      exclusion and imposition suites, which share this code path.

**Timing**: 1.25 hours

**Depends on**: 1

**Verification Tier**: full

Rationale: `syntactic/sentence.py` is a core module shared by every theory, and this edit changes
runtime dispatch behavior with no signature change — precisely the case the tie-break rule assigns
to `full`.

**Scope Hypothesis**: only bimodal's `\top` changes behavior, because logos' `\top`/`\bot` are
primitive `syntactic.Operator`s whose derived type is genuinely one element, and
exclusion/imposition define no extremal operator at all. **Confirm at implementation time** by
running every theory's suite, not only bimodal's, and diffing against Phase 1's baseline. If any
non-bimodal test changes behavior, the hypothesis is wrong and the branch condition needs
revisiting before Phases 3-5 proceed.

**Files to modify**:
- `code/src/model_checker/syntactic/sentence.py` — the `store_types` extremal branch and its
  comments.
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_formula.py` (or a sibling unit module,
  implementer's choice) — the new `\top`/`\bot`/nesting assertions.

**Verification**:
- The new `\top` assertions pass; the `\bot` companion assertions are unchanged.
- The full suite matches Phase 1's baseline with no new failures in any theory.
- A `\top` sentence no longer reaches `translate` with `arguments` set to `None`.

---

### Phase 3: Remove the `\top` workaround in the box test corpus [NOT STARTED]

**Goal**: Delete the exclusion that routed around the now-fixed defect, so the differential
exercise actually covers `\top`.

**Tasks**:
- [ ] Re-read `code/src/model_checker/theory_lib/bimodal/tests/unit/test_formula.py` around
      `_BOX_TEST_CORPUS` immediately before editing.
- [ ] Replace `_BOX_TEST_CORPUS = [ast for ast in _GENERATED_CORPUS if ast[0] != "top"] +
      _BOX_PROPERTY_ASTS` with the unfiltered `_GENERATED_CORPUS + _BOX_PROPERTY_ASTS`.
- [ ] Delete the multi-line comment documenting the TopOperator bug and the reason for the
      exclusion, replacing it with a one-line note that the defect is fixed — citing
      `sentence.py`'s `store_types` by function name, not by line number.
- [ ] Add `("top",)` and at least one nesting containing it (e.g. `("box", ("top",))`) to
      `_BOX_PROPERTY_ASTS`, so `\top` coverage is by construction rather than incidental to the
      seeded generator.
- [ ] Record the explicit decision to **leave** `examples.py`'s `\neg \bot` hand-expansions and
      their "avoid TopOperator bug" comments in place: they are correct as written, and rewriting
      the theory's example corpus is a separate cleanup on its own merits. Note in the progress
      record that those comments are now stale prose, not live workarounds.
- [ ] Run `test_formula.py` in full.

**Timing**: 0.5 hours

**Depends on**: 2

**Verification Tier**: local

Rationale: a test-module-only edit with no externally visible signature change; the shared-code
risk was already discharged by Phase 2's `full` tier.

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_formula.py` — `_BOX_TEST_CORPUS`,
  `_BOX_PROPERTY_ASTS`, and the exclusion comment.

**Verification**:
- `test_formula.py` passes in full with `\top` present in the differential corpus.
- No `ast[0] != "top"` filter remains anywhere in the module.

---

### Phase 4: Wire the translation conformance channel (fixture-only leg) [NOT STARTED]

**Goal**: Assert, for every fixture row, that this repository's own operator elimination and
translation produce the same formula the Lean side's `tr` produces — compared as parsed JSON.

**Tasks**:
- [ ] Create
      `code/src/model_checker/theory_lib/bimodal/tests/integration/test_sentence_translation_agreement.py`
      (name confirmed free), beside the existing integration modules.
- [ ] Resolve the fixture via `_lean_check.resolve_bimodal_logic_path()` and read
      `Tests/fixtures/sentence-translation-fixtures.jsonl` live from the resolved checkout — never
      a copy mirrored into this repository. Use a **distinct, named skip reason for checkout
      absence only**; do not reuse `SKIP_REASON`, which additionally requires `lake` and a
      `check_certificate` probe this leg does not need.
- [ ] Write a renderer from a fixture row's structured `sentence` AST to this repository's infix
      syntax. Drive it from the `sentence` field, **not** the `surface` field, which is
      Polish/prefix notation that `Syntax` does not parse.
- [ ] Map each tag to its operator surface name: `allFut`->`\Future`, `allPast`->`\Past`,
      `untl`->`\Until`, `snce`->`\Since`, `cond`->`\rightarrow`, `bicond`->`\leftrightarrow`,
      `dia`->`\Diamond`, `someFut`->`\future`, `somePast`->`\past`, `next`->`\next`,
      `prev`->`\prev`, and the remaining tags to their like-named operators.
- [ ] Fail loudly on any unknown tag rather than skipping the row — an unmapped tag means the
      fixture grew a constructor this channel does not cover, which is exactly what to find out.
- [ ] For each row: build the sentence through the real `Syntax` pipeline (reusing
      `test_formula.py`'s `_sentence` idiom), call `translate`, call `to_json`, and assert **dict
      equality** against the row's `formula` field. Never compare serialized strings — the Lean
      side prints `untl` with `event` before `guard` and `to_json` emits them the other way round.
- [ ] Assert the fixture row count and that every `kind` value (`primitive`, `defined`,
      `asymmetry`, `nesting`) is represented, so a truncated or partially-read fixture fails
      instead of passing vacuously. Resolve the expected count by reading the fixture at
      implementation time.
- [ ] Add explicit, individually named assertions for the two operators that are wrong when written
      the obvious way: `\rightarrow p q` must equal the disjunction-of-a-negation shape and **not**
      a bare `imp(p, q)`; `\future p` must equal the negated-universal shape and **not** a bare
      `untl`/`someFuture` primitive.
- [ ] Add a module docstring recording that the channel is **forward-only** (`tr` is not injective,
      so no inverse pass is checkable) and that comparison is on parsed JSON by contract, not by
      convenience.
- [ ] Run the new module.

**Timing**: 1.75 hours

**Depends on**: 2

**Verification Tier**: local

Rationale: a single new test module; it adds no production code and changes no signature.

**Scope Hypothesis**: the fixture is expected to carry 26 rows across 18 distinct sentence tags,
each with a 1:1 operator counterpart here. **Confirm at implementation time** by reading the
fixture rather than trusting this plan: the row-count assertion is the mechanical form of that
confirmation, and the unknown-tag failure is the mechanical form of the 1:1 claim's confirmation.

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/tests/integration/test_sentence_translation_agreement.py`
  (new).

**Verification**:
- Every fixture row passes as dict equality against its `formula` field.
- The row-count and `kind`-coverage assertions pass.
- The two flagged-operator assertions pass in their non-obvious shapes.
- With `BIMODAL_LOGIC_PATH` pointed at a nonexistent directory, the module skips with the named
  checkout-absence reason rather than erroring.

---

### Phase 5: Optional live differential leg against `lake exe translate_sentence` [NOT STARTED]

**Goal**: Add a skippable check that the committed fixture still matches what the live binary
emits, so fixture staleness is detectable rather than assumed away.

**Tasks**:
- [ ] Add a probe-once helper resolving both the checkout and `lake`, mirroring `_lean_check.py`'s
      established idiom (one probe per session, named reasons for environment absence, loud failure
      for a binary that answers wrongly).
- [ ] Invoke `lake exe translate_sentence` on a small representative selection of rows — at minimum
      one row per `kind`, plus the `\top` row and the two flagged-operator rows — and compare its
      parsed stdout to that row's `formula` field. Do **not** loop one subprocess per row over the
      whole fixture.
- [ ] Keep the environment-absence vocabulary strictly separate from the protocol-disagreement
      vocabulary, exactly as `_lean_check.py` documents: a binary that answers with the wrong
      formula must fail, never skip.
- [ ] Run the module with the checkout present, and again with `BIMODAL_LOGIC_PATH` pointed at a
      nonexistent directory, to confirm the skip path is clean.

**Timing**: 1 hour

**Depends on**: 4

**Verification Tier**: local

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/tests/integration/test_sentence_translation_agreement.py`
  (extend), or a sibling helper module if the probe logic grows large enough to warrant one.

**Verification**:
- With a working checkout and `lake`, the differential rows pass.
- With the checkout absent, the differential leg skips with a named reason while Phase 4's
  fixture-only leg is unaffected.
- A deliberately corrupted expected value makes the leg fail, not skip (sanity check that the
  assertion is live).

---

### Phase 6: Documentation, pin refresh, and final gate [NOT STARTED]

**Goal**: Leave this repository's documentation truthful about what is now checked from both ends,
refresh the pinned upstream commit, and close the task.

**Tasks**:
- [ ] Re-read `code/src/model_checker/theory_lib/bimodal/tests/_lean_check.py` and
      `.../tests/README.md` immediately before editing (task 205 and 206 both landed edits here,
      and the tree is shared).
- [ ] Refresh `BIMODAL_LOGIC_COMMIT` from `d55e2760e...` to the BimodalLogic commit that actually
      landed the translation channel, **resolved live** via
      `git log --oneline -- FormalSystem/SourceLanguage/ Tests/fixtures/sentence-translation-fixtures.jsonl`
      in the BimodalLogic checkout — do not copy a value from this plan or the research report.
      Update the surrounding comment to say the constant now pins both the certificate and the
      translation contracts.
- [ ] Update `code/src/model_checker/theory_lib/bimodal/tests/README.md` to describe the new
      translation conformance module alongside the existing certificate agreement module,
      including its forward-only and parsed-JSON-comparison properties.
- [ ] Re-read BimodalLogic's `BimodalTools/README.md` source-sentence translation protocol section
      (read-only) and confirm every obligation it states of the consuming side is now discharged by
      a live assertion; list any residual gap explicitly rather than leaving it implied.
- [ ] Run the full test suite one final time and compare against Phase 1's baseline.
- [ ] Commit, staging only this plan's named files by explicit path — never a directory or glob
      pathspec, never `git add -A`, never `git commit -am`. Leave the pre-existing dirty `specs/**`
      files recorded in Phase 1 untouched and unstaged.
- [ ] Write the implementation summary to
      `specs/209_bimodal_sentence_translation_contract/summaries/01_sentence-translation-contract-summary.md`
      in **this** repository, recording per item: what was found already done (1, 2, 4), what had
      no target (3), and what was implemented (5, 6). Write nothing under
      `/home/benjamin/Projects/BimodalLogic`.

**Timing**: 0.75 hours

**Depends on**: 3, 4, 5

**Verification Tier**: full

Rationale: the phase closes the task, so it runs the complete gate set regardless of how narrow its
own edits are.

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/tests/_lean_check.py` — `BIMODAL_LOGIC_COMMIT` and its
  comment.
- `code/src/model_checker/theory_lib/bimodal/tests/README.md` — new module description.
- `specs/209_bimodal_sentence_translation_contract/summaries/01_sentence-translation-contract-summary.md`
  (new).

**Verification**:
- Full test suite green, matching or improving on Phase 1's baseline.
- `git status --short` shows this plan's files committed and the pre-existing `specs/**`
  modifications still unstaged and unmodified.
- The summary artifact exists and covers all six items.
- `git log` in `/home/benjamin/Projects/BimodalLogic` shows no new commit and its `git status` is
  unchanged by this task.

---

## Testing & Validation

- [ ] `test_certificate_lean_agreement.py` runs (does not skip) and passes — items 1 and 4 live.
- [ ] `PROTOCOL_FAILURE` is `None`.
- [ ] `ensure_ascii=False` present at the single wire-serialization site — item 2.
- [ ] `\top` type-updates with both `operator` and `arguments` set; `\bot` unchanged.
- [ ] A bare `\top` and a nested `\top` both translate to the two-`bot` implication shape.
- [ ] `test_formula.py` passes in full with `\top` present in `_BOX_TEST_CORPUS`.
- [ ] Every fixture row agrees as parsed JSON; row count and `kind` coverage asserted.
- [ ] `\rightarrow` asserts the disjunction-of-negation shape; `\future` asserts the
      negated-universal shape.
- [ ] Checkout-absent skip paths are clean and named for both the fixture-only and differential
      legs.
- [ ] Full test suite green across every theory, matching Phase 1's baseline.

## Artifacts & Outputs

- `code/src/model_checker/syntactic/sentence.py` (modified — the `store_types` branch)
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_formula.py` (modified — `\top`
  assertions, corpus exclusion removed)
- `code/src/model_checker/theory_lib/bimodal/tests/integration/test_sentence_translation_agreement.py`
  (new)
- `code/src/model_checker/theory_lib/bimodal/tests/_lean_check.py` (modified — pin refresh)
- `code/src/model_checker/theory_lib/bimodal/tests/README.md` (modified)
- `specs/209_bimodal_sentence_translation_contract/summaries/01_sentence-translation-contract-summary.md`
  (new)

## Rollback/Contingency

This repository's working tree carries concurrent, unrelated in-flight work from other sessions
(`specs/TODO.md`, `specs/events.jsonl`, `specs/state.json`, plus whatever task 211 touches).

- **Never run a destructive git command** (`git reset --hard`, `git checkout -- <path>`,
  `git clean -fd`, `git restore <path>`) while the tree is dirty — doing so would discard another
  session's uncommitted work.
- **Do not emit a bare, reverting `git-snapshot.sh {N}` call** as a routine checkpoint. If a
  defensive checkpoint before risky work is wanted, use `bash .claude/scripts/git-snapshot.sh 209
  --no-revert`, which is durable without reverting the working tree.
- To revert a landed phase, `git revert` that phase's own commit. Because each phase commits only
  its own explicitly named files, a revert is surgical.
- If Phase 2's full-suite run shows a regression in a non-bimodal theory, the Scope Hypothesis is
  wrong: revert Phase 2's commit and reconsider the branch condition (for example, keeping the
  name test as a fast path for genuinely primitive extremal operators while adding the shape test)
  before proceeding to Phases 3-5, all of which depend on it.
- If the BimodalLogic checkout is unavailable in the implementation environment, Phases 1 and 5
  cannot be fully verified. Phases 2, 3 and 4 remain implementable; mark 1 and 5 `[BLOCKED]` with
  the named environment reason rather than reporting them passed.
- If a foreign commit, a foreign uncommitted modification to one of this plan's target files, or a
  build this session did not start is observed, STOP and report it (after checking `git log` to
  confirm the work is not this task's own) rather than proceeding.
