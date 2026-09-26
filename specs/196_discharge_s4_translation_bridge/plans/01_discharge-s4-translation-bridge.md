# Implementation Plan: Discharge obligation S4 (Sentence-to-Formula translation bridge)

- **Task**: 196 - Discharge obligation S4, the Sentence-to-Formula translation bridge
- **Status**: [NOT STARTED]
- **Effort**: 4 hours
- **Dependencies**: None
- **Research Inputs**: specs/196_discharge_s4_translation_bridge/reports/01_discharge-s4-translation-bridge.md
- **Artifacts**: plans/01_discharge-s4-translation-bridge.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: python
- **Lean Intent**: false

## Overview

Obligation S4 asks for evidence that `semantic/formula.py`'s `translate` (the `Sentence → Formula`
bridge) preserves truth. The translation code and its two named hazards (defined-operator
elimination, the `Until`/`Since` guard/event swap) are already implemented and already
unit-tested; a differential property test also already exists for the propositional-plus-tense
fragment (`test_formula.py::TestTranslateTruthPreservation`), with the `\Box` case recorded as a
deliberate gap and `_eval_lean_formula`'s `Box` branch left as a hard `NotImplementedError`. This
plan closes exactly that gap: generalize the file's two independent evaluators from a single time
line to a small hand-built family of histories, add the family-global `\Box` clause to both
sides, add box-containing sentences and multi-history valuations, prove the new coverage has teeth
with a negative control, then update the three documents that currently assert the gap in matching
words. Definition of done: both halves of S4 (tense and box) are differentially property-tested,
the bimodal suite is green, and `ADEQUACY.md` §2/§4.2/§6.3 plus `TRUST_PIPELINE.md` Stage 1 and
"What remains" state the new position and record which route was taken and why.

### Research Integration

The report settles the two questions the dispatch posed, and this plan follows it:

- **Route 1 (relocate the elimination into verified code so the obligation is deleted) is
  rejected as architecturally inapplicable.** `translate` is not an export-time boundary step:
  every primitive operator's `true_at` in `operators.py` calls it at *evaluation* time to build
  the `_bit` lookup key, and Lean is only ever invoked offline, once per certificate, via
  `lake exe check_certificate`. Lean also has no separate callable elimination pass to relocate
  into — its `neg`/`and`/`always` are `def`-level abbreviations that are already six-primitive
  terms. `TRUST_PIPELINE.md` already tracks "Lean-side translation with a truth-preservation
  theorem" as separate, not-yet-built Lean-side work.
- **Route 2 (the §6.3 property test) is taken**, extending the existing scaffold rather than
  inventing new machinery.
- The Lean-side cross-check the dispatch conditions on ("once its counterpart lands in
  BimodalLogic") is confirmed **not available**; it is recorded as deferred, not attempted.
- The report flags two unresolved design decisions, which this plan resolves:
  1. *Duplicate vs. import `Lasso`/label-decoding from `test_certificate_fixtures.py`* →
     **neither.** A truth-preservation test needs semantic *valuations*, not certificate
     *labels*: every compound formula's value is computed by the two evaluators, so no label
     family, no periodic decoding, and no (C1)–(C3) coherence precondition is involved. This also
     dissolves the report's Risk 1 (an incoherent hand-built label family making the test
     vacuous) rather than mitigating it.
  2. *Extend `TestTranslateTruthPreservation`'s evaluators in place vs. add a parallel box-aware
     pair* → **extend in place.** One copy of the tense clauses, and the existing parametrized
     test becomes an immediate regression guard on the generalization.
- The box clause both evaluators must implement is family-global, per
  `NecessityOperator`'s own docstring and `box_faithful`'s implementation in
  `test_certificate_fixtures.py`: `□A` is true iff `A` holds at **every** position of **every**
  history in the family — not a per-point quantifier.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No roadmap context was provided to this dispatch.

## Goals & Non-Goals

**Goals**:
- Extend `test_formula.py`'s differential truth-preservation property test to cover `\Box`,
  alone and nested under the connectives and tense operators already covered.
- Keep the two evaluators genuinely independent of `translate` and of each other (one reads the
  ModelChecker event-first AST, the other the translated guard-first `Formula`), so the test
  remains a differential check and not a round-trip tautology.
- Demonstrate the new box coverage is non-vacuous with an explicit negative control.
- Record in `ADEQUACY.md` and `TRUST_PIPELINE.md` that both halves of S4 are now
  property-tested, which route was taken, and why Route 1 was rejected.
- Record the Lean-side truth-preservation counterpart as explicitly deferred.

**Non-Goals**:
- Any change to `semantic/formula.py`, `operators.py`, or any production code. This task
  produces evidence for existing behavior; if the property test finds a real defect in
  `translate`, that is a new finding to report, not silently patched under this plan (see
  Risks).
- The Lean-side `Sentence → Formula` elimination pass and its truth-preservation theorem
  (Route 1) — out of scope, tracked on the Lean side.
- Extending `oracle/bimodal_logic/ground_truth.py` to adjudicate the box case.
- Z3 or `BimodalSemantics` involvement of any kind; the test stays in the existing file's
  no-solver idiom.
- New certificate fixtures under `tests/fixtures/certificates/`.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| The box half is vacuous: family-global `□` is constant across points, so every family could happen to agree trivially | H | M | Phase 3's negative control is a required, not optional, step: assert the suite rejects a deliberately wrong box translation, and assert at least one family makes `\Box p` true and another makes it false |
| Generalizing the evaluators to `(family, history_index, t)` silently breaks a tense clause | M | M | The existing `TestTranslateTruthPreservation` parametrization is kept unchanged in behavior and run after Phase 1 as the regression guard; Phase 1 closes only when it is green |
| The two evaluators drift toward sharing logic, turning the differential test into a tautology | H | L | They stay two separate recursive functions over two different inputs (AST vs. `Formula`); no shared helper may consume both, and the `\Until`/`\Since` argument order must stay written out independently on each side |
| The property test finds a genuine `translate` defect | H | L | Stop, do not patch production code under this plan; record the failing case and report it (see Rollback/Contingency) |
| The three documents asserting the gap go stale unevenly | M | M | Phase 4 treats all five locations as one objective and enumerates them explicitly |
| Sibling tasks 192/193/194 are dispatched this same cycle with undeclared file scope | M | M | Re-read every file immediately before editing; stage only this task's own hunks by explicit path; never a directory or glob `git add`; never reverting-mode `git-snapshot.sh` |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4 | 3 |
| 5 | 5 | 4 |

Phases within the same wave can execute in parallel.

---

### Phase 1: Generalize both evaluators to a history family, with a Box clause [NOT STARTED]

**Goal**: `_eval_mc_ast` and `_eval_lean_formula` in
`code/src/model_checker/theory_lib/bimodal/tests/unit/test_formula.py` evaluate at a point
`(history_index, t)` of a small family of histories and each implement the family-global `\Box`
clause, with the existing tense-fragment test still green.

**Tasks**:
- [ ] Re-read `tests/unit/test_formula.py` immediately before editing (concurrent siblings).
- [ ] Introduce the family representation: a sequence of per-history valuations, each a
  `{atom: {t: bool}}` mapping over `_PROPERTY_DOMAIN` — the same shape `_valuations` already
  yields, lifted one index. Keep it a plain tuple/list of dicts; do **not** import `Lasso` or any
  label machinery from `test_certificate_fixtures.py` (see Research Integration, decision 1).
- [ ] Change both evaluators' signatures to take `(node, family, i, t, domain)`: atoms read
  `family[i]`, the tense clauses quantify over `domain` within history `i` only (unchanged
  mathematics), and the new clauses read:
  - `_eval_mc_ast`, tag `"box"`: `all(_eval_mc_ast(child, family, j, u, domain) for j in
    range(len(family)) for u in domain)`.
  - `_eval_lean_formula`, `isinstance(formula, Box)`: the same quantification over
    `formula.child`, replacing the `NotImplementedError` at `test_formula.py:499-500`. Write it
    out independently; do not delegate to the AST side.
- [ ] Add the `"box"` case to `_ast_to_infix` (`\Box {child}`) and confirm `_atoms_in_ast`
  already recurses through it (it recurses over `ast[1:]` generically).
- [ ] Update `TestTranslateTruthPreservation`'s existing test body to wrap each `_valuations`
  result in a one-history family and pass `i=0`, leaving `_PROPERTY_ASTS`, `_PROPERTY_DOMAIN`,
  `_valuations` and the assertion message semantics unchanged.
- [ ] Add a docstring note on each evaluator recording that `\Box` is family-global per
  `NecessityOperator`'s docstring and (C3) box faithfulness, not a per-point quantifier.

**Timing**: 1 hour

**Depends on**: none

**Verification Tier**: local

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_formula.py` - generalize
  `_eval_mc_ast`, `_eval_lean_formula`, `_ast_to_infix`; add both `Box` clauses; adapt the
  existing test call sites

**Verification**:
- `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/unit/test_formula.py -v`
  passes with the pre-existing test count unchanged and no skips — this is the regression guard on
  the generalization.
- `grep -n NotImplementedError code/src/model_checker/theory_lib/bimodal/tests/unit/test_formula.py`
  no longer reports the `Box` branch.

---

### Phase 2: Add hand-built multi-history families and box-containing sentences [NOT STARTED]

**Goal**: a new test class exercises `translate` differentially over box-containing sentences at
every point of every history of several hand-built families.

**Tasks**:
- [ ] Re-read the file immediately before editing.
- [ ] Add `_PROPERTY_FAMILIES`: a small number of hand-built families (target 3), each with 2-3
  histories over `_PROPERTY_DOMAIN`, chosen so the box quantifier is genuinely exercised:
  - one where an atom holds at every point of every history (`\Box p` true),
  - one where it holds everywhere in one history but fails at a single point of another
    (`\Box p` false, and false *only* because of the second history — the case a single-history
    family structurally cannot catch),
  - one mixing two atoms so `\Box p` and `\Box q` differ within the same family.
- [ ] Add `_BOX_PROPERTY_ASTS`: `\Box p`; `\Box (p \wedge q)`; `\neg \Box p`;
  `\Box p \vee q`; `(\Box p) \Until q`; `(\Box p) \Since q`; `\Future (\Box p)`;
  `\Box (p \Until q)`; and one nesting a box inside a box's argument's tense operator, e.g.
  `\Box (\Future p)`.
- [ ] Add `TestTranslateTruthPreservationBox` (sibling class in the same file), parametrized over
  `_BOX_PROPERTY_ASTS` × `_PROPERTY_FAMILIES`, asserting `_eval_mc_ast == _eval_lean_formula` at
  every `(i, t)`, with a failure message naming the ast, family index, history index and `t`.
- [ ] Replace the "Known, deliberate limitation" comment block (`test_formula.py:400-407`) with
  a short note stating the box case is now covered here, naming the new class.

**Timing**: 1 hour

**Depends on**: 1

**Verification Tier**: local

**Scope Hypothesis**: 3 families × 9 box-containing ASTs is the plan-time estimate for "enough to
exercise the quantifier without a combinatorial blow-up". Confirm at implementation time that (a)
runtime for the new class stays under a couple of seconds, and (b) the mix actually produces both
box-true and box-false outcomes — if either fails, adjust the counts and record the actual numbers
in the summary rather than treating 3×9 as fixed.

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_formula.py` - add
  `_PROPERTY_FAMILIES`, `_BOX_PROPERTY_ASTS`, `TestTranslateTruthPreservationBox`; retire the
  limitation comment

**Verification**:
- `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/unit/test_formula.py -v`
  green, with every new parametrization collected and passing (no skips, no xfails).

---

### Phase 3: Negative control — prove the box coverage has teeth [NOT STARTED]

**Goal**: recorded, executable evidence that the new box tests would actually fail on a wrong
translation, closing the vacuity risk.

**Tasks**:
- [ ] Re-read the file immediately before editing.
- [ ] Add a test asserting non-vacuity of the family corpus directly: over `_PROPERTY_FAMILIES`,
  `_eval_mc_ast(("box", ("atom", "p")), ...)` is `True` for at least one family and `False` for
  at least one other.
- [ ] Add a mutation/negative-control test: build the translated formula for a box-containing
  sentence, substitute a deliberately wrong translation (e.g. drop the `Box` wrapper, or
  translate `\Box A` as `A`), and assert the two evaluators **disagree** at some `(i, t)` for at
  least one family — i.e. the differential check detects the defect. Keep the mutation local to
  the test (construct the wrong `Formula` by hand; never monkeypatch `translate`).
- [ ] Add the same style of negative control for the family-crossing case: a wrong box
  translation that quantifies over one history only would pass a single-history family; assert
  the multi-history family catches it.

**Timing**: 45 minutes

**Depends on**: 2

**Verification Tier**: local

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_formula.py` - add the non-vacuity
  and negative-control tests

**Verification**:
- `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/unit/test_formula.py -v`
  green.
- The negative-control tests pass *by detecting* the injected defect (assert on disagreement, not
  via `pytest.raises` on an unrelated error).

---

### Phase 4: Update ADEQUACY.md and TRUST_PIPELINE.md to the new state [NOT STARTED]

**Goal**: every in-repo statement that S4's box half is uncovered is corrected, and the route
decision plus the Lean-side deferral are recorded where a future reader will find them.

**Tasks**:
- [ ] Re-read both documents immediately before editing.
- [ ] `docs/ADEQUACY.md` §2 obligation table, the **S4** row (`:80`): state that S4 is now
  discharged by property test for both the tense and box halves, naming
  `tests/unit/test_formula.py`'s two `TestTranslateTruthPreservation*` classes, and keep the
  standing fact that no Lean theorem covers it.
- [ ] `docs/ADEQUACY.md` §4.2 "Residual" paragraph (`:297-300`): keep the residual, add the
  pointer to the discharging evidence.
- [ ] `docs/ADEQUACY.md` §6.3 (`:464-480`): keep the statement of the obligation and the two
  hazards; replace the forward-looking "the discharge is a property test…" framing with what now
  exists, including the family-global box clause and the negative controls; state that
  `oracle/bimodal_logic/ground_truth.py`'s tense-only limit is unchanged and no longer load-bearing
  for the box half.
- [ ] `docs/TRUST_PIPELINE.md` Stage 1 "Evidence: property-tested, and incompletely." (`:69-74`):
  retitle and rewrite to the current position (both halves property-tested; the round-trip still
  cannot detect a translation defect; the oracle's tense-only scope unchanged).
- [ ] `docs/TRUST_PIPELINE.md` "What remains" rows: the **Discharge S4** row (`:246`) is
  satisfied on the ModelChecker side — rewrite or remove it, leaving the
  "Lean-side translation with a truth-preservation theorem" row (`:260`) in place as the
  remaining half, explicitly marked deferred and not attempted here.
- [ ] In the §6.3 text (or an adjacent note), record the route decision in one short paragraph:
  Route 2 taken; Route 1 rejected because `translate` is called at evaluation time by every
  primitive operator's `true_at` and Lean has no callable verified elimination pass to relocate
  into. Cite durable anchors (file and section names), never task numbers.

**Timing**: 45 minutes

**Depends on**: 3

**Verification Tier**: prose

**Scope Hypothesis**: five documentation locations are asserted above (three in `ADEQUACY.md`, two
in `TRUST_PIPELINE.md`). Confirm at implementation time with
`grep -rn 'S4\|tense half\|box half\|no coverage' code/src/model_checker/theory_lib/bimodal/docs/`
that no sixth location still asserts the gap; if one appears, fix it too and say so in the summary.

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/docs/ADEQUACY.md` - §2 S4 row, §4.2 Residual, §6.3
- `code/src/model_checker/theory_lib/bimodal/docs/TRUST_PIPELINE.md` - Stage 1 Evidence
  paragraph, "What remains" rows

**Verification**:
- The grep above reports no remaining claim that the box half is uncovered.
- Every cross-reference added resolves (file paths and section numbers exist).
- No task-number references introduced outside `specs/**`.

---

### Phase 5: Full gate [NOT STARTED]

**Goal**: the whole repository is green with the new tests in place, and the outcome is recorded.

**Tasks**:
- [ ] `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/ -v`
- [ ] `PYTHONPATH=code/src pytest code/tests/ -q`
- [ ] Confirm nothing outside this task's files was staged in any phase commit
  (`git log --stat` over this task's commits).
- [ ] Record in the implementation summary: route taken (Route 2) and why Route 1 was rejected;
  the Lean-side counterpart recorded as deferred; the confirmed family/AST counts from Phase 2's
  Scope Hypothesis; and whether any sixth doc location was found in Phase 4.

**Timing**: 30 minutes

**Depends on**: 4

**Verification Tier**: full

**Files to modify**:
- None (verification and summary only)

**Verification**:
- Both pytest invocations exit 0 with no new failures, errors, or skips relative to the
  pre-task baseline.
- A test failure in a file outside this task's scope is treated as possibly a concurrent
  sibling's in-flight edit: check `git log`/`git status` before attributing it to this work, and
  report rather than silently fixing.

## Testing & Validation

- [ ] `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/unit/test_formula.py -v` green
- [ ] `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/ -v` green
- [ ] `PYTHONPATH=code/src pytest code/tests/ -q` green
- [ ] The pre-existing `TestTranslateTruthPreservation` parametrization still collects and passes
      unchanged (regression guard on the evaluator generalization)
- [ ] `TestTranslateTruthPreservationBox` collects and passes with no skips or xfails
- [ ] The negative-control tests pass by detecting an injected wrong box translation
- [ ] No `NotImplementedError` remains on any evaluator branch in `test_formula.py`
- [ ] No production file under `semantic/` or `operators.py` is modified

## Artifacts & Outputs

- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_formula.py` — family-aware
  evaluators with box clauses, `TestTranslateTruthPreservationBox`, non-vacuity and
  negative-control tests
- `code/src/model_checker/theory_lib/bimodal/docs/ADEQUACY.md` — §2 S4 row, §4.2, §6.3 updated;
  route decision recorded
- `code/src/model_checker/theory_lib/bimodal/docs/TRUST_PIPELINE.md` — Stage 1 evidence and
  "What remains" rows updated; Lean-side half marked deferred
- `specs/196_discharge_s4_translation_bridge/summaries/01_*-summary.md` — route taken and why,
  confirmed scope hypotheses, deferral record

## Rollback/Contingency

All edits are confined to one test file and two documents, committed per green sub-step, so
rollback is `git revert` of this task's own commits in reverse order — no working-tree discard is
needed, and no snapshot is required for the ordinary path. If a genuine whole-tree rollback of
uncommitted work becomes necessary, follow `context/contracts/recovery.md`'s rollback rung for the
exact `git-snapshot.sh` invocation shape (including its out-of-scope override flag); never emit a
bare reverting-mode snapshot as a routine checkpoint, and prefer `--no-revert` for a defensive
checkpoint before risky work.

Contingency if the property test reveals a real defect in `translate`: stop at that phase, mark it
`[BLOCKED]`, leave production code untouched, and report the failing sentence, family, history
index and time point. A translation defect is a finding about the soundness claim S4 guards, not a
drive-by fix, and deserves its own task.
