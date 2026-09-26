# Research Report: Discharge obligation S4 (Sentence-to-Formula translation bridge)

- **Task**: 196 - Discharge obligation S4, the Sentence-to-Formula translation bridge
- **Started**: 2026-09-26T00:00:00Z
- **Completed**: 2026-09-26T00:00:00Z
- **Effort**: ~1 hour (research only)
- **Dependencies**: None
- **Sources/Inputs**:
  - Design/spec: `code/src/model_checker/theory_lib/bimodal/docs/ADEQUACY.md` (§2 obligation table,
    §4.2 "Residual", §6.3), `code/src/model_checker/theory_lib/bimodal/docs/TRUST_PIPELINE.md`
    (Stage 1, "What remains" table)
  - Implementation: `code/src/model_checker/theory_lib/bimodal/semantic/formula.py` (`translate`,
    `to_json`), `code/src/model_checker/theory_lib/bimodal/operators.py` (`NecessityOperator`,
    `UntilOperator`, `SinceOperator`, `FutureOperator`, `PastOperator`, `_bit`)
  - Existing test coverage: `code/src/model_checker/theory_lib/bimodal/tests/unit/test_formula.py`
    (`TestTranslateTruthPreservation` and its "Known, deliberate limitation" comment),
    `code/src/model_checker/theory_lib/bimodal/tests/unit/test_certificate_fixtures.py`,
    `code/src/model_checker/theory_lib/bimodal/tests/fixtures/certificates/` (`README.md`,
    `01_positive_box.json`, `03_box_unfaithful.json`)
  - Independent adjudicator: `oracle/bimodal_logic/ground_truth.py`,
    `oracle/bimodal_logic/translation.py`
  - Lean side: `~/Projects/BimodalLogic/FormalSystem/Syntax/Formula.lean` (local checkout present),
    grep sweep of `~/Projects/BimodalLogic/docs/` for any ModelChecker-facing translation work
- **Artifacts**: this report
- **Standards**: status-markers.md, artifact-management.md, tasks.md, report-format.md

## Executive Summary

- `translate` (the `Sentence -> Formula` bridge obligation S4 names) is **already fully
  implemented** at `semantic/formula.py:320-388`, including the operator-elimination rules and the
  Until/Since guard/event swap the task description calls out as the two hazards. It is not
  missing code; it is missing *evidence*.
- A property test discharging exactly the mechanism ADEQUACY.md §6.3 asks for **already exists**
  for the non-modal (propositional-plus-tense) fragment:
  `test_formula.py::TestTranslateTruthPreservation` (added, per its own header comment, as a
  "Phase 2 amendment"). Its own docstring records the box case as a known, deliberate gap.
- **Route 1 ("relocate the elimination into verified code so the obligation is deleted") is not
  feasible with the current architecture and is not recommended.** `translate` is not merely an
  export-time formatting step — every primitive operator's `true_at` (`operators.py`) calls
  `translate` on its own arguments at *evaluation* time to compute a label-bit lookup key. There is
  no Lean-side runtime component ModelChecker consults during search or evaluation (Lean is only
  invoked offline, after the fact, via `lake exe check_certificate` on an already-exported
  `Formula`). Lean's own "defined operators" (`neg`, `and`, `always`, …, `Formula.lean:141+`) are
  Lean `def`-level abbreviations that always unfold to the six primitives before anything is
  stated about them — there is no separate, callable, verified "elaborate a richer surface syntax"
  pass in the Lean development to relocate this into. Building one would be a nontrivial new Lean
  development (a parser for ModelChecker's Sentence grammar, an elimination function, and a
  truth-preservation theorem for it) that TRUST_PIPELINE.md already tracks separately, on the Lean
  side, as future work ("Lean-side translation with a truth-preservation theorem").
- **Route 2 (the property test) is feasible, partially built, and is the recommended discharge.**
  The missing piece is exactly the box half, and the fixture corpus at
  `tests/fixtures/certificates/` already contains hand-built, (C1)-coherent label families with a
  box case (`01_positive_box.json`, `03_box_unfaithful.json`) plus a from-scratch, semantics-package-independent
  decoder/evaluator (`test_certificate_fixtures.py`) that already computes label membership
  (including box faithfulness) for exactly this kind of hand-built "small Z-model". This is the
  natural scaffold to extend, rather than inventing a new one.
- Recommend: extend `TestTranslateTruthPreservation` (or a sibling test class in the same file)
  with a box-aware differential test built from 2-3 hand-built label families (reusing the fixture
  corpus's shape), covering `\Box` alone and nested under `\neg`/`\wedge`/`\vee`/`\Until`/`\Since`.
  Record the outcome (route taken, and why) in `ADEQUACY.md` §6.3 and the S4 row of §2's obligation
  table once landed. The Lean-side cross-check named in the dispatch ("verify against the Lean-side
  translation once its counterpart lands") is confirmed **not yet available** (see Findings) and
  should be recorded as deferred, not attempted now.

## Context & Scope

Task 196 is scoped to discharging obligation **S4** from `ADEQUACY.md`'s obligation table (§2):
*"The `Sentence -> Formula` translation preserves truth"* — the one obligation among the four that
decomposes (SOUND), that "is not covered by any Lean theorem cited here." The task description
names two hazards specific to the translation code (operator elimination and the Until/Since
argument swap) and one specific gap in existing coverage (the box half of the property test,
since `oracle/bimodal_logic/ground_truth.py` only adjudicates the tense fragment). It asks for
research to determine (a) whether the obligation can be *deleted* by relocating translation into
verified code, and (b) failing that, a property-test design, and to record which route was taken
and why. This is a research-only task; no implementation was performed.

## Findings

### 1. The translation code already exists, and already documents its own two hazards

`semantic/formula.py:1-68`'s module docstring and `translate`'s dispatch (`:320-388`) already:

- Eliminate all 8 `DefinedOperator`s the theory declares (`\rightarrow`, `\leftrightarrow`,
  `\top`, `\Diamond`, `\future`, `\past`, `\next`, `\prev`) *before* `translate` ever sees them —
  confirmed separately by `Sentence.update_types`'s contract and by
  `test_formula.py::TestScopeHypothesisDefinedOperatorsAreExpandedBeforeTranslate`
  (`test_formula.py:268-289`), which checks e.g. that `\Diamond` reaches `translate` already
  rewritten as `\neg\Box\neg`.
- Encode the 9 primitives (`\neg, \wedge, \vee, \bot, \Box, \Future, \Past, \Until, \Since`) into
  the six-constructor `Formula` grammar (`Atom | Bot | Imp | Box | Untl | Snce`), including the
  `\Future`/`\Past` "always" encoding via `¬(⊤ U ¬A)` / `¬(⊤ S ¬A)` (`formula.py:367-375`).
  matching `Formula.lean:141+`'s own documented derivation.
- Perform the Until/Since **guard/event swap**: ModelChecker's `UntilOperator.true_at` is
  event-first (`operators.py:397`, `sentence.arguments[0]` = event); Lean's `untl`/`snce` are
  guard-first (`Formula.lean:86-104`). `translate`'s `\Until`/`\Since` cases
  (`formula.py:376-382`) swap explicitly: `Untl(guard=translate(guard_arg),
  event=translate(event_arg))`. This is unit-tested directly, order-sensitively, at
  `test_formula.py::TestTranslateUntilSinceOrderSensitive` (`:331-356`).

So the translation code itself is not missing or newly authored work; the obligation is a
*verification* gap, not an implementation gap.

### 2. A tense-fragment property test already discharges half of S4

`test_formula.py:385-584`'s `TestTranslateTruthPreservation` is exactly the mechanism ADEQUACY.md
§6.3 asks for: two independent recursive evaluators — `_eval_mc_ast` (mirrors `operators.py`'s
event-first semantics directly over a small hand-rolled AST) and `_eval_lean_formula` (mirrors the
Lean guard-first `untl`/`snce` semantics over the translated `Formula`) — checked for agreement
over 11 hand-built ASTs (`_PROPERTY_ASTS`, `:526-538`) crossed with 5 hand-built valuation patterns
per atom (`_valuations`, `:543-557`) at every point of a 7-point domain (`_PROPERTY_DOMAIN = range(-3,
4)`). This is a genuine differential test of `translate` against the *original* sentence's own
semantics (not a round-trip of the same already-translated object), closing exactly the gap
ADEQUACY.md §6.3 identifies for the propositional-plus-tense fragment.

Its own docstring (`:400-407`) states the box gap in the same words the task description uses:
*"this covers only the five non-modal primitives ... not Box ... Discharging the Box case is left
to later phases."* `_eval_lean_formula`'s `Box` branch (`:499-500`) is a hard `NotImplementedError`,
confirming no accidental partial coverage exists.

`oracle/bimodal_logic/ground_truth.py` independently confirms the same gap from the oracle side:
its module docstring states it supports only *"the 5 primitive temporal-only tags: atom, bot, imp,
untl, snce"*, and `GroundTruthUnsupported`'s docstring explicitly lists `box` as out of scope
(`ground_truth.py:1-6, ~50-60`). `oracle/bimodal_logic/translation.py` is a distinct, unrelated
module (JSON-formula to prefix/infix string conversion for CLI display) and contributes nothing to
either side of this obligation.

### 3. Route 1 (relocate into verified code) does not apply to this architecture

The task description frames this as "put the Sentence on the wire and let the verified side
eliminate." Two findings close this off as infeasible for this task's scope:

- **`translate` is not an export-only boundary function.** Every rewritten primitive operator's
  `true_at` (`operators.py`: `NecessityOperator:292-296`, `UntilOperator:397-402`,
  `SinceOperator:428-432`, `FutureOperator:329-334`, `PastOperator:358-363`, plus `BotOperator`)
  calls `translate` on its own argument(s) at *evaluation* time, to build the exact `Formula` key
  it looks up via `_bit` (`operators.py:96-99`) in `witness_registry.bit(lasso, position,
  formula)`. This is the theory's actual truth-evaluation mechanism (module docstring,
  `operators.py:29-43`: *"D5: each primitive operator carries its translation rule and its
  true_at/false_at as bit lookup"*), not a side artifact produced only for the certificate wire.
  There is no point at which ModelChecker could hand an un-translated `Sentence` to a Lean process
  and get a bit back during search or reporting — Lean is invoked only once, offline, per
  certificate, via `lake exe check_certificate` (`ADEQUACY.md` §6.2 step 4, `TRUST_PIPELINE.md`
  Stage 4/5), strictly after the Z3 search and the Python re-checker have already run.
- **Lean has no separate, callable elimination pass to move this into.** Reading
  `~/Projects/BimodalLogic/FormalSystem/Syntax/Formula.lean` directly: `neg`, `and`/`or` (via
  duals), `always`/`sometimes`, etc. are Lean `def`s built directly from the six primitive
  constructors (`Formula.lean:141` onward, "Naming Convention" section) — they are notation-level
  abbreviations that are *already* six-primitive terms the moment they are written, not an AST
  node type with its own elaboration/elimination function whose *correctness* is a theorem
  something could invoke. `Conservativity.translate` (`FormalSystem/Metalogic/Conservativity/`,
  `docs/reference/API_REFERENCE.md:868-869`) is an unrelated Lean-internal translation between two
  different Lean proof systems (`TM⁻` to `TM`), not a Sentence-to-Formula bridge and not reachable
  from Python.
- `TRUST_PIPELINE.md`'s own "What remains" table (line ~260) already tracks *"Lean-side translation
  with a truth-preservation theorem"* as **Lean-side, not-yet-built** future work ("the other half
  of S4"), confirming route 1 requires a nontrivial new Lean development out of scope for a
  ModelChecker-repository task, not a relocation achievable here.

**Conclusion: Route 1 is not available for this task.** The only route open to this repository is
Route 2 (extend the property test), per the dispatch's own fallback instruction.

### 4. Materials already in-repo make the box-half property test straightforward, not novel design

The certificate fixture corpus at `tests/fixtures/certificates/` already contains hand-built,
by-construction-(C1)–(C3)-coherent label families with a box case:

- `01_positive_box.json`: a single lasso, `back = fwd = [{p, □p}]`, `bx = {p: true}` — `□p` holds
  at every position of the one lasso (positive box case), refuting `□p → q`.
- `03_box_unfaithful.json`: a deliberately *incoherent* fixture (bx says `□p` false, but `p` holds
  everywhere) — useful as a negative/boundary case, not directly for a truth-preservation
  positive test.

`tests/unit/test_certificate_fixtures.py` (`README.md`'s own description: *"a from-scratch
re-implementation of the wire format and the four certificate conditions (C1)-(C4)... deliberately
independent of `model_checker.theory_lib.bimodal.semantic`"*) already implements exactly the
label-decoding and closure machinery (`Lasso.lab`, `closure_of`, `parse_formula`) a box-aware
independent evaluator needs, and is explicitly designed to be reusable/importable without pulling
in the semantics package under test.

This means the box half of S4 does not require inventing new "hand-built Z-model" infrastructure:
it requires (a) one or two more small hand-built label families (2-3 lassos, so a genuinely
non-trivial `\forall i,u` quantification is exercised, not just the single-lasso case
`01_positive_box.json` already covers), (b) a `Box` clause added to an evaluator over the
*original* Sentence AST (paralleling `_eval_mc_ast`, quantifying over all lassos/positions of the
family — `M, τᵢ, t ⊨ □χ iff ∀ j, u. χ ∈ Lⱼ(u)`, i.e. `ADEQUACY.md` Corollary 3.1/Lemma 4's own
box clause), and (c) the matching `Box` clause already stubbed as `NotImplementedError` in
`_eval_lean_formula` (`test_formula.py:499-500`), filled in as a label-membership lookup against
the same hand-built family. Because the label families are hand-built to satisfy (C1)-(C3) by
construction (as the existing fixtures already are), no Z3 search and no `BimodalSemantics`
instantiation is needed — matching the dispatch's "small hand-built Z-model" framing and the
existing test file's own no-Z3, no-`BimodalSemantics` style.

### 5. What the property test would newly need, beyond what exists

- A representation for a small witness family (a handful of lassos, each with a short
  `back`/`mid`/`fwd`) that is independent of `translate`/`operators.py`, so the test remains a
  differential check and not a tautology. `test_certificate_fixtures.py`'s `Lasso`/`Certificate`
  classes already provide this independent representation and could be imported directly (it
  already avoids importing `model_checker.theory_lib.bimodal`), or the same shape could be
  duplicated inline in `test_formula.py` to keep that file's stated independence from the fixture
  corpus's own test target — this is a design choice for the plan phase, not resolved here.
- A small set of hand-built ASTs that include `\Box`, nested with the already-covered connectives
  (e.g. `\Box p`, `\Box(p \wedge q)`, `\neg\Box p`, `(\Box p) \Until q`), analogous to
  `_PROPERTY_ASTS`.
- Because `\Box`'s truth value depends on the *whole family*, not a single-lasso valuation, the
  valuation/label generator (`_valuations`) needs a family-level analogue: a small number of
  hand-picked multi-lasso label assignments (2-3 families, each with 2-3 lassos) rather than a
  per-atom Boolean pattern — this is the one genuinely new piece of test machinery, though it is
  structurally the same idea as `_valuations`, just indexed by `(lasso, t)` instead of `t` alone.

## Decisions

- **Route taken (recommended for the implementation phase): Route 2 — extend the existing
  property test to cover the box half.** Route 1 (relocating elimination into verified Lean code)
  is rejected for this task as architecturally inapplicable: `translate` is invoked at Python-side
  evaluation time by every rewritten primitive operator (Finding 3), and Lean has no separate,
  callable, verified elimination pass for a richer surface syntax to relocate this into — that
  would be new Lean-side work, already tracked separately in `TRUST_PIPELINE.md` as future work,
  not achievable by editing this repository.
- **The Lean-side cross-check named in the dispatch's fallback instruction ("verify against the
  Lean-side translation once its counterpart lands in BimodalLogic") is confirmed not currently
  available** (Finding 3, `~/Projects/BimodalLogic` grep sweep) and should be recorded as
  explicitly deferred/blocked-on-Lean-side-work in whatever plan or summary follows, not attempted.
- **No new "Z-model" infrastructure needs to be invented from scratch**: the fixture corpus
  (`tests/fixtures/certificates/`) and its independent decoder
  (`tests/unit/test_certificate_fixtures.py`) already supply hand-built, (C1)-coherent label
  families with a box case and a from-scratch label-membership evaluator; the plan phase should
  reuse or closely mirror that shape rather than designing new label-family plumbing.

## Recommendations

1. **Implement the box-half extension of `TestTranslateTruthPreservation`** in
   `test_formula.py`, following the existing file's own idiom (hand-built ASTs + hand-built
   valuations/families, no Z3, no `BimodalSemantics`):
   - Add a family-level valuation generator (2-3 small hand-built multi-lasso label families).
   - Add a `Box` clause to a new/extended AST evaluator (quantifying `∀ lasso, position` over the
     family, per `ADEQUACY.md` Corollary 3.1/Lemma 4).
   - Fill in `_eval_lean_formula`'s `NotImplementedError` `Box` branch (`:499-500`) with the
     matching label-membership clause against the same family.
   - Extend `_PROPERTY_ASTS` with a handful of box-containing cases nested under the operators
     already covered.
2. **Update `ADEQUACY.md` §6.3 and its §2/§4.2 cross-references** once the extension lands, to
   state that S4 is now property-tested for *both* halves (tense and box), naming the new test
   class/file, and update `TRUST_PIPELINE.md`'s Stage 1 "Evidence" paragraph (currently
   "property-tested, and incompletely" and "covers only the tense half") and its "What remains"
   table row ("Discharge S4 ... The box half has no coverage at all") to reflect the new state —
   these three documents currently make matching, specific claims about the gap and will go stale
   together if only the code changes.
3. **Do not attempt the Lean-side truth-preservation counterpart in this task.** It is out of
   scope (a separate Lean-repository development, already tracked in `TRUST_PIPELINE.md`) and the
   dispatch's own instruction only asks to verify against it "once its counterpart lands" — it has
   not landed.
4. **Record which route was taken and why** (as the dispatch requires) in the implementation
   summary: Route 2, because Route 1 requires new Lean-side verified infrastructure this
   repository cannot supply (see Decisions).

## Risks & Mitigations

- **Risk**: A hand-built multi-lasso label family that is *not* actually (C1)-(C3)-coherent would
  make the box-half test vacuous or misleading (agreement would follow from both evaluators reading
  an incoherent family the same way, not from `translate` being correct). *Mitigation*: build new
  families the same way `01_positive_box.json`/`03_box_unfaithful.json` were built — by explicit
  construction against the (C1)/(C3) biconditionals, as `tests/fixtures/certificates/README.md`
  documents for the existing corpus — and consider running each new family through
  `test_certificate_fixtures.py`'s own `coherent_at`/box-faithfulness checkers (already independent
  and already imported by that test module) as a coherence precondition before trusting the
  differential result.
- **Risk**: Duplicating `Lasso`/label-decoding logic between `test_formula.py` and
  `test_certificate_fixtures.py` would create two independently-maintained copies of the same
  periodic-decoding arithmetic. *Mitigation*: this is a plan-phase design decision (import one from
  the other, or accept the duplication for the stated reason `test_certificate_fixtures.py`'s
  header gives for its own independence) — flagged here, not resolved.

## Appendix

- `code/src/model_checker/theory_lib/bimodal/docs/ADEQUACY.md`: §2 (obligation table), §4.2
  ("Residual" paragraph), §6.3 (obligation S4 statement).
- `code/src/model_checker/theory_lib/bimodal/docs/TRUST_PIPELINE.md`: Stage 1 (lines ~60-79),
  "What remains" tables (lines ~246, ~260).
- `code/src/model_checker/theory_lib/bimodal/semantic/formula.py`: module docstring (`:1-68`),
  `translate` dispatch (`:320-388`).
- `code/src/model_checker/theory_lib/bimodal/operators.py`: module docstring D5 (`:29-43`), `_bit`
  (`:96-99`), `NecessityOperator` (`:270-307`), `UntilOperator`/`SinceOperator` (`:374-441`),
  `FutureOperator`/`PastOperator` (`:314-372`).
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_formula.py`: `:268-289`
  (scope-hypothesis test), `:331-356` (Until/Since order test), `:385-584`
  (`TestTranslateTruthPreservation`, including the "Known, deliberate limitation" comment at
  `:400-407` and the `Box` `NotImplementedError` at `:499-500`).
- `code/src/model_checker/theory_lib/bimodal/tests/fixtures/certificates/README.md` and
  `01_positive_box.json`, `03_box_unfaithful.json`.
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_certificate_fixtures.py`: module
  docstring (`:1-23`), `Lasso`/`Certificate` (`:110-186`).
- `oracle/bimodal_logic/ground_truth.py`: module docstring, `GroundTruthUnsupported`.
- `oracle/bimodal_logic/translation.py`: module docstring (confirmed unrelated to S4).
- `~/Projects/BimodalLogic/FormalSystem/Syntax/Formula.lean`: primitive grammar and derived-operator
  `def`s (`:76-141+`).
- `~/Projects/BimodalLogic/docs/reference/API_REFERENCE.md:868-869`,
  `~/Projects/BimodalLogic/docs/theorem-index.md:300-314` (confirming `Conservativity.translate` is
  an unrelated Lean-internal translation).
