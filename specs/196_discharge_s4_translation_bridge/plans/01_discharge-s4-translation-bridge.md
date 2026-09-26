# Implementation Plan: Discharge obligation S4 (Sentence-to-Formula translation bridge)

- **Task**: 196 - Discharge obligation S4, the Sentence-to-Formula translation bridge
- **Status**: [IMPLEMENTING]
- **Effort**: 9 hours
- **Dependencies**: 193, 194 (sequencing, user-directed: both touch the same bimodal test tree,
  and 193 adds closure formulas to `test_certificate_a2_triangle.py`; this task's normalization
  sweep must run after they land and must sweep any `\Until`/`\Since` occurrences they introduce)
- **Research Inputs**: specs/196_discharge_s4_translation_bridge/reports/01_discharge-s4-translation-bridge.md
- **Artifacts**: plans/01_discharge-s4-translation-bridge.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md,
  git-workflow.md, no-task-references-in-deliverables.md
- **Type**: python
- **Lean Intent**: false
- **Plan Version**: 2 (revision of the 5-phase v1; scope addition per user decision, cycle 3)
- **Reports Integrated**: 01_discharge-s4-translation-bridge.md

## Overview

Obligation S4 asks for evidence that `semantic/formula.py`'s `translate` (the `Sentence → Formula`
bridge) preserves truth. This plan now does two things, in this order, because the user directed a
scope addition that changes what the verification must be written against:

1. **Normalize ModelChecker to guard-first `\Until`/`\Since` throughout**, matching Lean's
   `untl`/`snce`, so `translate` no longer swaps and a reader working in both repositories sees
   one argument order. This is a *semantic* change to every existing two-argument
   `\Until`/`\Since` occurrence — approximately 300 `Until`/`Since` mentions across 28 files, of
   which the order-bearing subset must each be inspected and flipped deliberately. It lands
   first, so the verification tests are written against the normalized convention rather than the
   convention they would immediately have to be rewritten out of.
2. **Discharge S4's box half by a two-axis differential property test**, extending
   `test_formula.py::TestTranslateTruthPreservation`: generate small-depth sentences covering
   every defined operator, hand-build multi-lasso label families so the box dimension has genuine
   structure, and reuse the existing certificate fixture corpus and its independent decoder rather
   than inventing new infrastructure.

Definition of done: one argument order across ModelChecker, the oracle, and Lean; both halves of
S4 (tense and box) differentially property-tested with recorded non-vacuity; the bimodal suite,
the oracle suite, and the four-theory gate green; and `ADEQUACY.md` §2/§4.2/§6.3 plus
`TRUST_PIPELINE.md` Stage 1 and "What remains" stating the new position, the route taken, and the
Lean-side deferral.

### Research Integration

Newly integrated reports: none. This revision integrates no new research report — the research
inputs are unchanged from v1. It is driven entirely by two user decisions recorded in
`.decisions.json` (cycles 2 and 3), plus plan-time codebase grounding performed for this revision
(see "Sites discovered during this revision" below).

Carried forward from the report, unchanged and still governing:

- **Route 1 (relocate the elimination into verified code so the obligation is deleted) is
  INFEASIBLE.** `translate` is not an export-time boundary step: every primitive operator's
  `true_at` in `operators.py` calls it at *evaluation* time to build the `_bit` lookup key, and
  Lean is only ever invoked offline, once per certificate, via `lake exe check_certificate`. Lean
  also has no callable verified elimination pass to relocate into — its `neg`/`and`/`always` are
  `def`-level abbreviations that are already six-primitive terms. `TRUST_PIPELINE.md` already
  tracks "Lean-side translation with a truth-preservation theorem" as separate, not-yet-built
  Lean-side work. Recorded as infeasible with this reason, per user decision.
- **Route 2 (the §6.3 property test) is taken**, extending the existing scaffold.
- **The Lean-side cross-check is DEFERRED**, its counterpart confirmed absent from the local
  `~/Projects/BimodalLogic` checkout. Not attempted here.

### Revisions from v1 (what changed and why)

| v1 position | v2 position | Driver |
|-------------|-------------|--------|
| No normalization; `translate` keeps swapping | Guard-first normalization across ModelChecker + oracle, landing **before** verification | User decision, cycle 3 ("APPROVED AND REQUIRED, user-directed") |
| v1 Research-Integration decision 1: "neither import nor duplicate `Lasso`/label decoding — a truth-preservation test needs valuations, not labels" | **Reversed.** Hand-build multi-lasso *label families* and reuse `tests/fixtures/certificates/01_positive_box.json`, `03_box_unfaithful.json`, and the independent decoder in `test_certificate_fixtures.py` | User decision, cycle 2, design property (2): "reuse ... rather than inventing new infrastructure" |
| Box families as plain `{atom: {t: bool}}` dicts over a finite domain | Families as `Lasso` objects (periodic `back`/`mid`/`fwd`), genuinely Z-indexed, with `coherent_at`/`box_faithful` run as a coherence precondition | Same decision; also restores the report's own Risk 1 mitigation, which v1 had dissolved by dropping labels |
| Asymmetric `\Until`/`\Since` cases not required | **Mandatory.** Generated `Until`/`Since` cases must include instances where event and guard are distinguishable and swapping them changes the truth value somewhere in the model | User decision, cycle 2, design property (3), explicitly retained by cycle 3 for a different reason (general truth preservation across the event/guard distinction, since after normalization there is no swap left to catch) |
| Sentence corpus hand-written only | Two axes: **generated** small-depth sentences covering every defined operator (`\neg`, `\wedge`, `\vee`, derived tense operators, `\next`, `\prev`) **plus** hand-built label families | User decision, cycle 2, design property (2) |
| `Dependencies: None` | `Dependencies: 193, 194` | User decision, cycle 3, SEQUENCING clause |
| 5 phases, 4 hours | 9 phases, 9 hours | Scope addition |

Retained from v1 without change: the in-place extension of `TestTranslateTruthPreservation`'s
evaluators (one copy of the tense clauses, the existing parametrization as the regression guard);
the family-global box clause (`□A` true iff `A` holds at every position of every lasso of the
family, per `NecessityOperator`'s docstring and `box_faithful`); the negative-control requirement;
and the five-location documentation sweep.

### Sites discovered during this revision (beyond the decision's enumeration)

The cycle-3 decision enumerated four site classes as grep-confirmed. Plan-time grounding for this
revision found further **order-bearing** sites that must move in the same lockstep, because
leaving them would silently change meaning rather than merely read inconsistently:

1. **`operators.py:601` `DefNextOperator.derived_definition`** returns
   `[UntilOperator, argument, [BotOperator]]` — event-first. Under guard-first it must become
   `[UntilOperator, [BotOperator], argument]`. Its docstring ("Defined as Next(phi) = U(phi, bot)")
   must become `U(bot, phi)`.
2. **`operators.py:620` `DefPrevOperator.derived_definition`** — the same, for `Snce`.
   These two are the highest-severity discovered sites: `\next`/`\prev` are among the very
   defined operators the generated corpus in Phase 6 must cover, so a missed flip here would be
   both a real semantic defect and a defect the new test is specifically built to catch.
3. **`docs/ARCHITECTURE.md:221`** already states "`\Until`/`\Since` are guard-first ... so
   translation swaps them" — a prose claim about the mechanism (not a formula string), which
   becomes half-true and half-false after normalization and must be rewritten.
4. **`test_formula.py::TestTranslateUntilSinceOrderSensitive` (`:331-356`)** asserts the swap
   (`result == Untl(guard=guard, event=event)` for `(p \Until q)` with `event=p`). After
   normalization this test must assert **positional identity** instead, and its class docstring
   rewritten. It is a convention assertion, not a formula string, so the decision's file list did
   not reach it.
5. **`test_formula.py`'s `_eval_mc_ast` `until`/`since` clauses** assign
   `event, guard = ast[1], ast[2]`. This must become `guard, event = ast[1], ast[2]`.
6. **Files carrying `Until`/`Since` mentions but absent from the decision's list**:
   `docs/USER_GUIDE.md`, `docs/ADEQUACY.md`, `docs/TRUST_PIPELINE.md`, `semantic/core.py`,
   `tests/README.md`, `tests/_lean_check.py`, `oracle/bimodal_logic/KNOWN_EXTERNAL_DEFECTS.md`,
   `oracle/bimodal_logic/README.md`, `oracle/bimodal_logic/ground_truth.py`, and the oracle tests
   `test_cross_oracle_differential.py`, `test_ground_truth.py`,
   `test_disagreement_classification.py`. Phase 1 produces the authoritative inventory rather than
   trusting either list.
7. **`examples.py` carries its own convention annotations.** Each BX axiom example has a comment
   block of the form: `# BX name: left_mono_until_G` / `# Formula: G(phi -> chi) -> ((psi \Until
   phi) -> (psi \Until chi))` / `# Using binary infix: (event \Until guard)` / the concrete
   rendering. The abstract `Formula:` line states the Lean axiom and is the **meaning invariant**;
   the concrete rendering is the notation that flips; the `Using binary infix:` annotation
   (2 occurrences, `:882` and `:902`, single-backslash so absent from the `\\Until` grep) states
   the convention and must be rewritten to `(guard \Until event)`. This makes each example
   auditable per-occurrence instead of by guesswork.
8. **`test_certificate_fixtures.py`'s internal formula tuple is `("untl", event, guard)`** —
   positionally event-first for an object that represents a *Lean* formula. Because Phase 5 imports
   this decoder, leaving it would put two orders in one test's field of view. Decided: flip it, with
   a fallback (see Phase 2, objective 2.5).

**Not affected, confirmed:** the certificate wire format and everything reading it. `to_json`/
`from_json` and every oracle JSON path (`ground_truth.py:82,114,123`, `translation.py:415-525`,
`:638-674`, `:839-869`) address `event`/`guard` by **name**, so the wire is order-free. The only
order-bearing oracle site is the infix-rendering tuple `_PRIMITIVE_BINARY` at
`translation.py:60-61`. `translate`'s `\Future`/`\Past` rules use `Untl(top, ...)` positionally
against the `Untl` dataclass, whose fields are already `(guard, event)` — unchanged.

### Prior Plan Reference

`plans/01_discharge-s4-translation-bridge.md` v1 (5 phases, 4 hours, no phases started). All v1
phases were `[NOT STARTED]`; none is preserved as-is, and v1's phases 1-5 survive as this plan's
phases 5-9, rewritten to the label-family design and the normalized convention.

### Roadmap Alignment

No roadmap context was provided to this dispatch.

## Goals & Non-Goals

**Goals**:
- Normalize `\Until`/`\Since` to guard-first across `operators.py` (including the `\next`/`\prev`
  derivations), `semantic/formula.py`'s `translate`, `oracle/bimodal_logic/translation.py`'s infix
  mapping, and every order-bearing formula string, docstring, and document — all in lockstep, with
  every previously-passing truth-value assertion still passing.
- Extend `test_formula.py`'s differential truth-preservation property test to cover `\Box`, alone
  and nested, over hand-built multi-lasso label families built from the existing fixture corpus's
  shape and validated by its independent coherence checkers.
- Generate small-depth sentences covering every defined operator (`\neg`, `\wedge`, `\vee`,
  `\future`, `\past`, `\next`, `\prev`) so elimination coverage is broad, including asymmetric
  `\Until`/`\Since` instances where guard and event are genuinely distinguishable.
- Keep the two evaluators genuinely independent: the reference evaluator must **not** route
  through `translate`, or the test passes under the very bug it targets.
- Demonstrate the new box coverage and the asymmetry coverage are non-vacuous with explicit
  negative controls.
- Record in `ADEQUACY.md` and `TRUST_PIPELINE.md`: both halves of S4 property-tested; the box half
  covered directly (it cannot be inherited from `oracle/bimodal_logic/ground_truth.py`, which
  handles only the five primitive tense tags); Route 2 taken; Route 1 infeasible with its reason;
  the Lean-side counterpart deferred; and the guard-first normalization.

**Non-Goals**:
- The Lean-side `Sentence → Formula` elimination pass and its truth-preservation theorem (Route 1).
- Extending `oracle/bimodal_logic/ground_truth.py` to adjudicate the box case.
- Z3 or `BimodalSemantics` involvement in the new tests; they stay in the existing file's
  no-solver idiom. (The normalization phases do exercise Z3 indirectly, via the existing suites.)
- New certificate fixtures under `tests/fixtures/certificates/`. The existing corpus supplies the
  shape; new label families live in the test module.
- Renaming the `event`/`guard` JSON keys or changing the wire format in any way.
- Changing any example's `expectation` flag. An expectation that has to change is a **finding**
  (see Risks), not a sweep step.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| A missed order-bearing occurrence silently changes a formula's meaning while its test keeps passing | H | M | Phase 1 builds the authoritative inventory as an explicit checklist (both `\\Until` and `\Until` grep forms); Phase 2's deliberate red is captured and diffed against that checklist; blind `sed` is forbidden; every flip is inspected against the occurrence's own stated meaning |
| An `examples.py` BX axiom turns out to have denoted the wrong proposition under event-first, so its `expectation` was passing for the wrong reason | H | L | Each example's `# Formula:` comment line (the Lean axiom in `phi`/`psi` terms) is the meaning invariant; flip the concrete rendering to preserve it. If preserving it forces an `expectation` change, STOP: record the example, the two readings, and the expectation delta, and report it — do not adjust `expectation` to make the suite green |
| The theory and the oracle drift apart mid-sweep, so the brute-force adjudicator silently disagrees | H | M | Phase 2 is declared `Commit Mode: atomic-batch`: the semantic centers, the formula strings, and the oracle mapping are one commit. No intermediate state is committed |
| Phase 2's deliberate red is mistaken for a real regression, or used to justify reverting | M | M | The red is an expected, named signal (user decision, cycle 3: "that red should be used as the checklist of order-sensitive sites rather than avoided"). Phase 2 objective 2.1 captures it to a scratch file *before* any string flip, and that capture is the checklist |
| The box half is vacuous: family-global `□` is constant across points, so every family could agree trivially | H | M | Phase 7's controls are required, not optional: assert at least one family makes `\Box p` true and another false, and assert the differential detects a deliberately wrong box translation |
| The asymmetry requirement is satisfied only nominally — cases cover both operators but no case is actually order-sensitive | H | M | Phase 7 adds a dedicated sensitivity control: for at least one generated `Until` and one `Since` case, the operand-swapped formula must disagree with the original at some `(lasso, t)`. Operator coverage is not hazard sensitivity |
| Importing `test_certificate_fixtures.py` from `test_formula.py` fails (no `__init__.py` in `tests/unit/`) | M | M | Phase 5 Scope Hypothesis: plain `import test_certificate_fixtures` works under pytest's rootdir-relative `sys.path` insertion. If it does not, extract `parse_formula`/`Lasso`/`coherent_at`/`box_faithful` into `tests/unit/_certificate_model.py` imported by both — a move, not a reimplementation |
| Generalizing the evaluators to `(family, lasso_index, t)` silently breaks a tense clause | M | M | The existing `TestTranslateTruthPreservation` parametrization is kept behaviourally unchanged and run after Phase 5 as the regression guard; Phase 5 closes only when it is green |
| The two evaluators drift toward shared logic, turning the differential into a tautology | H | L | They stay two separate recursive functions over two different inputs (AST vs. `Formula`); no shared helper may consume both; the reference side never calls `translate`; the `\Until`/`\Since` clauses stay written out independently on each side |
| The property test finds a genuine `translate` defect | H | L | Stop, do not patch production code under the verification phases; record the failing case and report it (see Rollback/Contingency) |
| Flipping `test_certificate_fixtures.py`'s internal tuple breaks the fixture verdict tests | M | M | `expected_verdicts.json` is the invariant and must not change; if the flip proves entangled, fall back to leaving the tuple order and adding a one-line comment naming it (Phase 2 objective 2.5 records which was done) |
| Tasks 193/194 land concurrently and introduce new `\Until`/`\Since` occurrences | M | H | Phase 1 blocks until both have landed and re-runs the inventory against the post-193/194 tree; Phase 4's gate re-greps for occurrences introduced since Phase 1 |
| Sibling tasks are dispatched the same cycle with undeclared file scope | M | M | Re-read every file immediately before editing; stage only this task's own hunks by explicit path; never a directory or glob `git add`; never reverting-mode `git-snapshot.sh` |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | 193, 194 landing |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4 | 3 |
| 5 | 5 | 4 |
| 6 | 6 | 5 |
| 7 | 7 | 6 |
| 8 | 8 | 7 |
| 9 | 9 | 8 |

Strictly sequential by design. Phases 1-4 are the normalization; phases 5-9 are the verification.
The user decision requires the normalization to land **before** the verification phases, so no
verification phase is parallelized into the normalization waves even where their file sets are
disjoint.

---

### Phase 1: Dependency gate, authoritative occurrence inventory, and baseline [COMPLETED]

**Goal**: tasks 193 and 194 have landed; an inspected, per-occurrence checklist of every
order-bearing `\Until`/`\Since` site exists; and a green pre-change baseline is recorded so any
later red is attributable.

**Tasks**:
- [ ] Confirm tasks 193 and 194 are complete (`specs/state.json`). If either is not, mark this
  phase `[BLOCKED]` with the reason and stop — the sweep must not run against a tree those tasks
  are still editing.
- [ ] Build the inventory with **both** grep forms, since Python string literals carry `\\Until`
  while comments, docstrings, and markdown carry `\Until`:
  - `grep -rn 'Until\|Since' --include=*.py --include=*.md code/src/model_checker/theory_lib/bimodal/ oracle/`
  - Filter the English-word false positives ("Since bot is never true", prose "since").
- [ ] Classify every surviving occurrence into exactly one of:
  - **(A) order-bearing code**: a positional argument order in executable code
    (`operators.py` `true_at`/`false_at` signatures, `DefNextOperator`/`DefPrevOperator`
    derivations, `translate`'s `\Until`/`\Since` rules, `translation.py:60-61`,
    `test_formula.py`'s `_eval_mc_ast` clauses, `test_certificate_fixtures.py`'s formula tuple).
  - **(B) order-bearing formula string**: a two-argument `\Until`/`\Since` inside a formula
    literal or an expected-output string, in `examples.py`, the bimodal tests, the oracle tests,
    `README.md`, `docs/API_REFERENCE.md`, `docs/ARCHITECTURE.md`, `docs/USER_GUIDE.md`.
  - **(C) convention prose**: text asserting which order holds or that translation swaps
    (`operators.py` docstrings including the Burgess paragraph and the Key Properties/Example
    blocks, `semantic/formula.py`'s module docstring section "The Until/Since guard/event swap",
    `ARCHITECTURE.md:221`, `examples.py`'s `Using binary infix:` annotations,
    `test_formula.py`'s order-test docstring, `KNOWN_EXTERNAL_DEFECTS.md`).
  - **(D) order-free**: named-field JSON handling, one-argument `\next`/`\prev` strings, bare
    mentions of the operator name.
- [ ] Write the checklist to `/tmp/claude-1000/.../scratchpad/196_until_since_inventory.md`
  (scratchpad, not the repo) as `file:line class current-reading intended-reading`. For each (B)
  occurrence, record the *meaning* it currently denotes and the guard-first string that denotes
  the same meaning. For each `examples.py` BX axiom, record its `# Formula:` line as the invariant.
- [ ] Record the baseline: `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/ -q`,
  `PYTHONPATH=code/src pytest oracle/bimodal_logic/tests/ -q`, and
  `PYTHONPATH=code/src pytest code/tests/ -q` — pass/fail/skip counts saved to the scratchpad.

**Timing**: 1 hour 15 minutes

**Depends on**: 193, 194

**Verification Tier**: prose

**Commit Mode**: per-substep (inventory and baseline live in the scratchpad; nothing in the repo
changes, so this phase produces no commit)

**Scope Hypothesis**: the revision-time sweep found ~300 `Until`/`Since` mentions across 28 files,
of which the decision names ~91 across 16 files as order-bearing. Neither figure is a fact.
Confirm the real (A)+(B)+(C) counts at implementation time and record them; if the order-bearing
set is materially larger than ~100, say so before starting Phase 2 rather than discovering it
mid-batch.

**Files to modify**:
- None (inventory and baseline only; scratchpad output)

**Verification**:
- All three baseline suites are green (or their pre-existing failures/skips are explicitly
  enumerated, so Phase 2's red is attributable).
- The checklist covers every non-(D) occurrence the grep found, with no "unclassified" rows.

---

### Phase 2: Flip the convention to guard-first, in lockstep [COMPLETED]

**Goal**: ModelChecker, the oracle, and every order-bearing formula string read guard-first
together, in a single commit, with every previously-passing truth-value assertion still passing.

**Commit Mode**: `atomic-batch`. The declared file set is one objective: intermediate per-file
states are expected red and MUST NOT be committed, because a tree with `translate` flipped and the
formula strings not flipped (or the theory flipped and the oracle not) is a tree whose tests assert
the wrong propositions. One commit, taken only when the phase's verification is green.

**Tasks**:

*2.1 — Flip the semantic centers, capture the red (no commit)*
- [ ] Re-read each file immediately before editing.
- [ ] `operators.py`: `UntilOperator.true_at`/`false_at` and `SinceOperator.true_at`/`false_at`
  parameter order becomes `(self, guard_arg, event_arg, eval_point)`; the bodies become
  positional-identity `Untl(guard=translate(guard_arg), event=translate(event_arg))` with no swap.
- [ ] `operators.py:601`, `:620`: `DefNextOperator.derived_definition` becomes
  `[UntilOperator, [BotOperator], argument]` and `DefPrevOperator.derived_definition` becomes
  `[SinceOperator, [BotOperator], argument]`.
- [ ] `semantic/formula.py`: `translate`'s `\Until` and `\Since` rules become positional identity —
  `Untl(guard=translate(arguments[0]), event=translate(arguments[1]))` — and the local
  `event_arg, guard_arg = arguments` unpacking becomes `guard_arg, event_arg = arguments`.
- [ ] `oracle/bimodal_logic/translation.py:60-61`: `_PRIMITIVE_BINARY`'s `"untl"` and `"snce"`
  tuples become `("\\Until", "guard", "event")` / `("\\Since", "guard", "event")`.
- [ ] Run the three suites and **capture the full red output to the scratchpad**. This is the
  expected signal named in the user decision. Diff the set of failing sites against Phase 1's
  (B) checklist: a failure at a site not on the checklist is a discovered occurrence (add it); a
  checklist (B) site that did *not* fail is either order-insensitive at that point of the model
  or under-asserted — note which, because an order-bearing string whose test cannot see the flip
  is exactly the invisible-hazard class this task exists to close.
- [ ] Do **not** commit here.

*2.2 — Flip every order-bearing formula string in the bimodal package*
- [ ] Work the Phase 1 (B) checklist occurrence by occurrence, swapping the two operands of each
  two-argument `\Until`/`\Since` so the string denotes the **same proposition** in the new
  notation. A blind `sed` is forbidden.
- [ ] `examples.py` (~22 order-bearing string occurrences across the BX axiom schemas): for each,
  check the concrete rendering against that example's own `# Formula:` line (the Lean axiom in
  `phi`/`psi` terms) and its `# BX name:` line. Flip the rendering to preserve the `Formula:`
  line. Leave every `expectation` flag untouched. Note that several examples nest `\Until` inside
  `\Until` (`BX5_ACCUM_U_TH`, `BX6_ABSORB_U_TH`, `BX13_ENRICH_U_TH`) and two are four-operand
  conjunctive schemas (`:1270-1273`, `:1296-1299`) — each inner occurrence flips independently.
- [ ] Bimodal tests: `tests/integration/test_until_since_integration.py`,
  `tests/integration/test_certificate_a2_triangle.py` (`:228`, `:386`),
  `tests/unit/test_next_prev.py`, `tests/unit/test_formula.py`, `tests/unit/test_operators.py`
  (`:113`, `:126`, `:137`), `tests/unit/test_structure.py` (`:247`),
  `tests/unit/test_proposition.py` (`:124`). Sweep any occurrences tasks 193/194 introduced.
- [ ] `test_formula.py` specifically: rewrite `TestTranslateUntilSinceOrderSensitive`
  (`:331-356`) from a swap assertion to a **positional-identity** assertion, keeping its
  order-sensitivity (the swapped `Untl`/`Snce` must still not match), and rewrite its class
  docstring. Flip `_eval_mc_ast`'s `until`/`since` clauses to `guard, event = ast[1], ast[2]`.
  `_ast_to_infix`'s `until`/`since` cases render `ast[1]` then `ast[2]` positionally and need no
  change, but their meaning has changed — add a one-line comment saying so.

*2.3 — Flip the oracle's order-bearing strings*
- [ ] `oracle/bimodal_logic/tests/test_json_translation.py` (expected infix renderings),
  `test_oracle_interface.py`, `test_cross_oracle_differential.py`, `test_ground_truth.py`,
  `test_disagreement_classification.py` — per the Phase 1 checklist.

*2.4 — Code-adjacent docstrings that state the convention*
- [ ] `operators.py`: `UntilOperator`'s class docstring — drop the Burgess-convention paragraph
  (the citation is deliberately dropped in favor of cross-repository uniformity, per the user
  decision) and rewrite the Key Properties and Example blocks to guard-first;
  `SinceOperator`'s "Event-first, mirroring ..." paragraph; both `true_at` docstrings' "including
  its event/guard argument swap (D2)"; `DefNextOperator`/`DefPrevOperator` docstrings
  (`U(phi, bot)` → `U(bot, phi)`); the module docstring's operator summary (`:25-26`, `:53`).
- [ ] `semantic/formula.py`: rewrite the module docstring section titled
  "**The Until/Since guard/event swap**" to record that there is **no longer a swap** — ModelChecker
  and Lean share one guard-first order — and update the paragraph at `:18-22` that says
  "translation must swap".

*2.5 — `test_certificate_fixtures.py`'s internal tuple order*
- [ ] Flip the module's formula-tuple convention from `("untl", event, guard)` to
  `("untl", guard, event)` (likewise `snce`), updating `parse_formula`, `subformulas`, and every
  consumer (`coherent_at`, `fulfil_at`, `box_faithful`) in lockstep, plus the representation
  comment at `:15-23`. `parse_formula` reads named JSON fields, so the wire is unaffected.
- [ ] Invariant: `fixtures/certificates/expected_verdicts.json` must **not** change and every
  fixture verdict test must stay green. If the flip proves entangled beyond this phase's budget,
  fall back to leaving the tuple order as-is and adding a one-line comment naming it as a
  module-local positional convention distinct from the repository's guard-first order — and record
  in the summary which of the two was done and why.

**Timing**: 2 hours 30 minutes

**Depends on**: 1

**Verification Tier**: full (this changes runtime behavior of every `\Until`/`\Since` evaluation
and crosses `code/` and `oracle/`; the tie-break rule applies)

**Scope Hypothesis**: objective 2.2 is estimated at ~22 `examples.py` occurrences plus ~40 across
the bimodal tests and docs; 2.3 at ~15 oracle occurrences. Confirm against Phase 1's actual
checklist and record the real counts in the summary.

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/operators.py` — `Until`/`Since` `true_at`/`false_at`
  signatures and bodies; `\next`/`\prev` derivations; docstrings
- `code/src/model_checker/theory_lib/bimodal/semantic/formula.py` — `translate`'s `\Until`/`\Since`
  rules; module docstring swap section
- `oracle/bimodal_logic/translation.py` — `_PRIMITIVE_BINARY` `untl`/`snce` tuples
- `code/src/model_checker/theory_lib/bimodal/examples.py` — BX axiom renderings and the two
  `Using binary infix:` annotations
- `code/src/model_checker/theory_lib/bimodal/tests/integration/test_until_since_integration.py`,
  `tests/integration/test_certificate_a2_triangle.py`, `tests/unit/test_next_prev.py`,
  `tests/unit/test_formula.py`, `tests/unit/test_operators.py`, `tests/unit/test_structure.py`,
  `tests/unit/test_proposition.py`, `tests/unit/test_certificate_fixtures.py`
- `oracle/bimodal_logic/tests/test_json_translation.py`, `test_oracle_interface.py`,
  `test_cross_oracle_differential.py`, `test_ground_truth.py`,
  `test_disagreement_classification.py`

**Verification**:
- `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/ -q` green, with the
  **same** pass/fail/skip counts as Phase 1's baseline.
- `PYTHONPATH=code/src pytest oracle/bimodal_logic/tests/ -q` green, same counts as baseline.
- `PYTHONPATH=code/src pytest code/tests/ -q` green, same counts as baseline.
- Every previously-passing truth-value assertion still passes, and **no `expectation` flag in
  `examples.py` changed**. If one had to change, the phase is `[BLOCKED]` on a reported finding,
  not green.
- `fixtures/certificates/expected_verdicts.json` unchanged (`git diff --stat` shows it absent).
- `grep -rn 'event-first\|guard/event swap\|Burgess' code/src/model_checker/theory_lib/bimodal/ oracle/`
  returns only occurrences that are deliberate history notes, not live claims.
- Exactly one commit for the whole phase.

---

### Phase 3: Sweep the standalone documentation to one argument order [COMPLETED]

**Goal**: no user-facing document still states the event-first convention or that translation
swaps.

**Tasks**:
- [ ] Re-read each document immediately before editing.
- [ ] `code/src/model_checker/theory_lib/bimodal/README.md` — the `\Until`/`\Since` operator
  descriptions and any example formula strings.
- [ ] `docs/API_REFERENCE.md` — the `UntilOperator`/`SinceOperator` entries, their signatures, and
  any example strings.
- [ ] `docs/ARCHITECTURE.md:221` — rewrite the paragraph that says `\Until`/`\Since` are
  guard-first "the opposite of ModelChecker's historical event-first argument order — so
  translation swaps them". State that ModelChecker is now guard-first too and translation is
  positional identity; keep one sentence of history naming the retired event-first order so a
  reader of an older commit is not confused.
- [ ] `docs/USER_GUIDE.md` — operator table / examples.
- [ ] `oracle/bimodal_logic/KNOWN_EXTERNAL_DEFECTS.md` and `oracle/bimodal_logic/README.md` — any
  claim about the order or about a theory/oracle order mismatch.
- [ ] `code/src/model_checker/theory_lib/bimodal/tests/README.md`, `tests/_lean_check.py`,
  `semantic/core.py` — single mentions from the Phase 1 checklist.
- [ ] Cite durable anchors (file and section names) only; no task numbers outside `specs/**`.

**Timing**: 45 minutes

**Depends on**: 2

**Verification Tier**: prose

**Commit Mode**: per-substep

**Scope Hypothesis**: seven documents are asserted above. Confirm against Phase 1's (C) checklist;
if an eighth appears, fix it and say so in the summary.

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/README.md`
- `code/src/model_checker/theory_lib/bimodal/docs/API_REFERENCE.md`
- `code/src/model_checker/theory_lib/bimodal/docs/ARCHITECTURE.md`
- `code/src/model_checker/theory_lib/bimodal/docs/USER_GUIDE.md`
- `code/src/model_checker/theory_lib/bimodal/tests/README.md`
- `code/src/model_checker/theory_lib/bimodal/tests/_lean_check.py`
- `code/src/model_checker/theory_lib/bimodal/semantic/core.py`
- `oracle/bimodal_logic/KNOWN_EXTERNAL_DEFECTS.md`, `oracle/bimodal_logic/README.md`

**Verification**:
- Diff read-through confirms every changed hunk lies inside prose, a comment, or a docstring.
- Every (C) row on the Phase 1 checklist is resolved.
- Every formula string appearing in a document is guard-first and denotes what its surrounding
  prose says it denotes.

---

### Phase 4: Normalization gate and audit record [COMPLETED]

**Goal**: the whole repository is green under one argument order, and what the sweep found is
recorded before verification work begins.

**Tasks**:
- [ ] `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/ -v`
- [ ] `PYTHONPATH=code/src pytest oracle/bimodal_logic/tests/ -q`
- [ ] `PYTHONPATH=code/src pytest code/tests/ -q` (the four-theory gate)
- [ ] Re-run the Phase 1 grep and confirm no order-bearing occurrence remains unflipped, including
  any introduced by a concurrent sibling since Phase 1.
- [ ] Record in the progress file (carried into the summary): confirmed (A)/(B)/(C) counts; every
  checklist site whose test did *not* go red in objective 2.1, with the reason (order-insensitive
  at that model point vs. under-asserted); whether any `examples.py` expectation delta was found;
  and which branch objective 2.5 took.
- [ ] Confirm nothing outside this task's declared files was staged
  (`git log --stat` over this task's commits).

**Timing**: 30 minutes

**Depends on**: 3

**Verification Tier**: full

**Commit Mode**: per-substep

**Files to modify**:
- None (verification and record only)

**Verification**:
- All three suites exit 0 with counts matching the Phase 1 baseline.
- A failure in a file outside this task's scope is checked against `git log`/`git status` before
  being attributed to this work, and reported rather than silently fixed.

---

### Phase 5: Import the independent label-family decoder and add the Box clause [COMPLETED]

**Goal**: `_eval_mc_ast` and `_eval_lean_formula` in
`code/src/model_checker/theory_lib/bimodal/tests/unit/test_formula.py` evaluate at a point
`(lasso_index, t)` of a small **label family** and each implement the family-global `\Box` clause,
with the existing tense-fragment test still green.

**Tasks**:
- [ ] Re-read `tests/unit/test_formula.py` and `tests/unit/test_certificate_fixtures.py`
  immediately before editing (concurrent siblings).
- [ ] Import the existing independent decoder rather than reimplementing it: `parse_formula`,
  `Lasso`, `coherent_at`, `box_faithful` from `test_certificate_fixtures.py` (per user decision,
  cycle 2, design property (2)). That module deliberately imports nothing from
  `model_checker.theory_lib.bimodal`, so importing it keeps the reference side independent of the
  code under test.
- [ ] Introduce the family representation: a tuple of `Lasso` objects (each with `back`/`mid`/`fwd`
  label lists) plus the family's `bx` map, exactly the shape
  `fixtures/certificates/01_positive_box.json` uses. Atom truth at `(i, t)` is
  `parse_formula({"tag": "atom", "name": a}) in family[i].lab(t)` — genuinely Z-indexed via the
  lasso's periodic decoding, which a finite `{atom: {t: bool}}` dict cannot express.
- [ ] Change both evaluators' signatures to take `(node, family, i, t, domain)`:
  - atoms read `family[i].lab(t)`;
  - the tense clauses quantify over `domain` within lasso `i` only (unchanged mathematics);
  - `_eval_mc_ast`, tag `"box"`:
    `all(_eval_mc_ast(child, family, j, u, domain) for j in range(len(family)) for u in domain)`;
  - `_eval_lean_formula`, `isinstance(formula, Box)`: the same quantification over
    `formula.child`, replacing the `NotImplementedError` at `test_formula.py:499-500`. Write it out
    independently; do **not** delegate to the AST side.
- [ ] **Oracle independence invariant**: neither evaluator may call `translate`, and no helper may
  consume both an AST and a `Formula`. Add an assertion-free comment stating this and why (a
  reference evaluator routed through `translate` passes under the very bug the test targets).
- [ ] Add the `"box"` case to `_ast_to_infix` (`\Box {child}`) and confirm `_atoms_in_ast` already
  recurses through it (it recurses over `ast[1:]` generically).
- [ ] Update `TestTranslateTruthPreservation`'s existing test body to wrap each `_valuations`
  result in a one-lasso family (a `Lasso` whose `back`/`fwd` encode the same per-`t` atom pattern),
  leaving `_PROPERTY_ASTS`, `_PROPERTY_DOMAIN` and the assertion message semantics unchanged.
- [ ] Add a docstring note on each evaluator recording that `\Box` is family-global per
  `NecessityOperator`'s docstring and (C3) box faithfulness, not a per-point quantifier.

**Timing**: 1 hour 15 minutes

**Depends on**: 4

**Verification Tier**: local

**Commit Mode**: per-substep

**Scope Hypothesis**: `import test_certificate_fixtures` is expected to resolve under pytest's
rootdir-relative `sys.path` insertion (`tests/unit/` has no `__init__.py`; `tests/conftest.py`
exists). Confirm at implementation time by running the file directly. If it does not resolve, move
`parse_formula`/`Lasso`/`coherent_at`/`box_faithful` into `tests/unit/_certificate_model.py`
imported by both modules — a relocation, not a second copy — and record that this was needed.

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_formula.py` — import the decoder;
  generalize `_eval_mc_ast`, `_eval_lean_formula`, `_ast_to_infix`; add both `Box` clauses; adapt
  the existing test call sites
- `code/src/model_checker/theory_lib/bimodal/tests/unit/_certificate_model.py` — only if the
  Scope Hypothesis fails

**Verification**:
- `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/unit/test_formula.py -v`
  passes with the pre-existing test count unchanged and no skips — the regression guard on the
  generalization.
- `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/unit/test_certificate_fixtures.py -v`
  still green (the decoder is now imported by a second module).
- `grep -n NotImplementedError .../test_formula.py` no longer reports the `Box` branch.
- `grep -n 'translate' ` inside the two evaluator function bodies returns nothing.

---

### Phase 6: Two axes — generated sentences and hand-built multi-lasso families [COMPLETED]

**Goal**: a new test class exercises `translate` differentially over generated small-depth
sentences covering every defined operator, including asymmetric `\Until`/`\Since` instances, at
every point of every lasso of several hand-built multi-lasso label families.

**Tasks**:
- [ ] Re-read the file immediately before editing.
- [ ] **Axis 1 — hand-built label families.** Add `_PROPERTY_FAMILIES`: a small number of families
  (target 3), each with 2-3 lassos over `_PROPERTY_DOMAIN`, built the way
  `01_positive_box.json` and `03_box_unfaithful.json` were built — by explicit construction
  against the (C1)/(C3) biconditionals documented in `fixtures/certificates/README.md`:
  - one where an atom holds at every position of every lasso (`\Box p` true — the shape
    `01_positive_box.json` already has, reused as the template);
  - one where it holds everywhere in one lasso but fails at a single position of another
    (`\Box p` false, and false *only* because of the second lasso — the case a single-lasso family
    structurally cannot catch);
  - one mixing two atoms so `\Box p` and `\Box q` differ within the same family.
  - Assert coherence as a **precondition**, not an outcome: run each family through the imported
    `coherent_at` and `box_faithful` in a dedicated test, so an incoherent family fails loudly
    instead of making the differential vacuous. `03_box_unfaithful.json` is the reference for what
    an incoherent family looks like and is used as the negative case of that precondition test.
- [ ] **Axis 2 — generated sentences covering every defined operator.** Add a small deterministic
  generator (seeded, bounded depth ≤ 3, atoms from `{p, q}`) producing sentences over
  `\neg`, `\wedge`, `\vee`, `\Box`, `\Future`, `\Past`, `\Until`, `\Since` **and** the defined
  operators `\future`, `\past`, `\next`, `\prev`, `\rightarrow`, `\Diamond`, `\top` — so the
  elimination coverage the obligation names is broad rather than only what someone thought to
  write down. Assert as part of the corpus that every defined operator appears in at least one
  generated sentence (coverage is checked, not assumed).
- [ ] **Asymmetric `\Until`/`\Since` are mandatory.** The generated corpus must include instances
  where guard and event are genuinely distinguishable *and* swapping them changes the truth value
  at some `(i, t)` of some family. Assert this property of the corpus directly (Phase 7 adds the
  control that proves the assertion has teeth). Retained per the cycle-3 decision for its new
  reason: after normalization there is no swap left to catch, so these cases now test general
  truth preservation across the event/guard distinction.
- [ ] Keep a hand-written `_BOX_PROPERTY_ASTS` alongside the generated corpus for the nestings a
  bounded generator may not reach: `\Box p`; `\Box (p \wedge q)`; `\neg \Box p`;
  `\Box p \vee q`; `(q \Until \Box p)`; `(q \Since \Box p)`; `\Future (\Box p)`;
  `\Box (q \Until p)`; `\Box (\Future p)`. (Operand order shown guard-first.)
- [ ] Add `TestTranslateTruthPreservationBox` (sibling class in the same file), parametrized over
  the generated corpus plus `_BOX_PROPERTY_ASTS`, crossed with `_PROPERTY_FAMILIES`, asserting
  `_eval_mc_ast == _eval_lean_formula` at every `(i, t)`, with a failure message naming the ast,
  family index, lasso index and `t`.
- [ ] Replace the "Known, deliberate limitation" comment block (`test_formula.py:400-407`) with a
  short note stating the box case is now covered here, naming the new class, and stating that the
  box half could not be inherited from `oracle/bimodal_logic/ground_truth.py` (five primitive tense
  tags, no box case) and is therefore covered directly.

**Timing**: 1 hour 30 minutes

**Depends on**: 5

**Verification Tier**: local

**Commit Mode**: per-substep

**Scope Hypothesis**: 3 families × (generated corpus + 9 hand-written box ASTs) is the plan-time
estimate for "enough to exercise the quantifier and the elimination without a combinatorial
blow-up". Confirm at implementation time that (a) runtime for the new class stays under a few
seconds, (b) the mix actually produces both box-true and box-false outcomes, (c) every defined
operator is covered, and (d) at least one asymmetric `Until` and one asymmetric `Since` case are
present. If any fails, adjust and record the actual numbers in the summary rather than treating
3×N as fixed.

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_formula.py` — add
  `_PROPERTY_FAMILIES`, the sentence generator, `_BOX_PROPERTY_ASTS`, the coherence-precondition
  test and `TestTranslateTruthPreservationBox`; retire the limitation comment

**Verification**:
- `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/unit/test_formula.py -v`
  green, with every new parametrization collected and passing (no skips, no xfails).
- The coherence-precondition test passes, and passes *for the right reason*: it rejects
  `03_box_unfaithful.json`.
- The defined-operator coverage assertion names every one of `\neg`, `\wedge`, `\vee`, `\rightarrow`,
  `\Diamond`, `\top`, `\future`, `\past`, `\next`, `\prev`.

---

### Phase 7: Negative controls — prove the new coverage has teeth [NOT STARTED]

**Goal**: recorded, executable evidence that the box coverage and the asymmetry coverage would
actually fail on a wrong translation, closing the vacuity risk.

**Tasks**:
- [ ] Re-read the file immediately before editing.
- [ ] **Non-vacuity of the family corpus**: over `_PROPERTY_FAMILIES`,
  `_eval_mc_ast(("box", ("atom", "p")), ...)` is `True` for at least one family and `False` for at
  least one other.
- [ ] **Box mutation control**: build the translated formula for a box-containing sentence,
  substitute a deliberately wrong translation (drop the `Box` wrapper, i.e. translate `\Box A` as
  `A`), and assert the two evaluators **disagree** at some `(i, t)` for at least one family. Keep
  the mutation local to the test — construct the wrong `Formula` by hand; never monkeypatch
  `translate`.
- [ ] **Family-crossing control**: a wrong box translation that quantifies over one lasso only
  would pass a single-lasso family; assert the multi-lasso family catches it. This is what makes
  the multi-lasso structure load-bearing rather than decorative.
- [ ] **Asymmetry sensitivity control**: for at least one generated `Until` case and one `Since`
  case, construct the operand-swapped `Formula` by hand and assert it disagrees with the
  translated original at some `(i, t)`. Operator coverage is not hazard sensitivity; this is the
  assertion that the corpus is order-sensitive at all.
- [ ] **Elimination control**: for at least one defined operator (e.g. `\next`), construct a
  wrong elimination by hand (`\next A` as `Untl(guard=A, event=Bot())`, the pre-normalization
  operand order) and assert the differential detects it. This is the control that would have
  caught the `DefNextOperator` derivation had Phase 2 missed it.

**Timing**: 1 hour

**Depends on**: 6

**Verification Tier**: local

**Commit Mode**: per-substep

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_formula.py` — add the non-vacuity and
  the four negative-control tests

**Verification**:
- `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/unit/test_formula.py -v`
  green.
- Every control passes *by detecting* the injected defect (assert on disagreement, not via
  `pytest.raises` on an unrelated error).

---

### Phase 8: Update ADEQUACY.md and TRUST_PIPELINE.md to the new state [NOT STARTED]

**Goal**: every in-repo statement that S4's box half is uncovered is corrected, and the route
decision, the normalization, and the Lean-side deferral are recorded where a future reader will
find them.

**Tasks**:
- [ ] Re-read both documents immediately before editing.
- [ ] `docs/ADEQUACY.md` §2 obligation table, the **S4** row (`:80`): state that S4 is now
  discharged by property test for both the tense and box halves, naming
  `tests/unit/test_formula.py`'s two `TestTranslateTruthPreservation*` classes, and keep the
  standing fact that no Lean theorem covers it.
- [ ] `docs/ADEQUACY.md` §4.2 "Residual" paragraph (`:297-300`): keep the residual, add the
  pointer to the discharging evidence.
- [ ] `docs/ADEQUACY.md` §6.3 (`:464-480`): keep the statement of the obligation; the two named
  hazards now read differently — operator elimination is unchanged and is what the generated
  corpus covers, while the `Until`/`Since` guard/event swap **no longer exists**, ModelChecker
  having been normalized to Lean's guard-first order, so the residual hazard there is general
  truth preservation across the event/guard distinction rather than a swap. Replace the
  forward-looking "the discharge is a property test…" framing with what now exists: the
  family-global box clause, the coherence precondition, the generated defined-operator coverage,
  and the five negative controls. State that `oracle/bimodal_logic/ground_truth.py`'s tense-only
  scope (five primitive tags, no box case) is unchanged and is no longer load-bearing for the box
  half, which is covered directly.
- [ ] `docs/TRUST_PIPELINE.md` Stage 1 "Evidence: property-tested, and incompletely." (`:69-74`):
  retitle and rewrite to the current position — both halves property-tested; the round-trip against
  `lake exe check_certificate` still structurally cannot detect a translation defect, since both
  sides consume the same already-translated `Formula`; the oracle's tense-only scope unchanged.
- [ ] `docs/TRUST_PIPELINE.md` "What remains" rows: the **Discharge S4** row (`:246`) is satisfied
  on the ModelChecker side — rewrite or remove it, leaving the "Lean-side translation with a
  truth-preservation theorem" row (`:260`) in place as the remaining half, explicitly marked
  deferred and not attempted here (counterpart confirmed absent from the local `BimodalLogic`
  checkout).
- [ ] Record the route decision in one short paragraph in §6.3 or an adjacent note: **Route 2
  taken**; **Route 1 infeasible** because `translate` is called at evaluation time by every
  primitive operator's `true_at` (not only at export) and Lean has no callable verified elimination
  pass to relocate into; **Lean cross-check deferred**. Also record the guard-first normalization
  and why (cross-repository uniformity; the Burgess-convention citation deliberately dropped),
  pointing at `ARCHITECTURE.md`'s rewritten paragraph.
- [ ] Cite durable anchors (file and section names), never task numbers.

**Timing**: 1 hour

**Depends on**: 7

**Verification Tier**: prose

**Commit Mode**: per-substep

**Scope Hypothesis**: five documentation locations are asserted above (three in `ADEQUACY.md`, two
in `TRUST_PIPELINE.md`). Confirm at implementation time with
`grep -rn 'S4\|tense half\|box half\|no coverage' code/src/model_checker/theory_lib/bimodal/docs/`
that no sixth location still asserts the gap; if one appears, fix it too and say so in the summary.

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/docs/ADEQUACY.md` — §2 S4 row, §4.2 Residual, §6.3
- `code/src/model_checker/theory_lib/bimodal/docs/TRUST_PIPELINE.md` — Stage 1 Evidence paragraph,
  "What remains" rows

**Verification**:
- The grep above reports no remaining claim that the box half is uncovered.
- No document still describes a `translate`-level `Until`/`Since` swap as live.
- Every cross-reference added resolves (file paths and section numbers exist).
- No task-number references introduced outside `specs/**`.

---

### Phase 9: Full gate [NOT STARTED]

**Goal**: the whole repository is green with the normalization and the new tests in place, and the
outcome is recorded.

**Tasks**:
- [ ] `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/ -v`
- [ ] `PYTHONPATH=code/src pytest oracle/bimodal_logic/tests/ -q`
- [ ] `PYTHONPATH=code/src pytest code/tests/ -q` (the four-theory gate)
- [ ] Confirm nothing outside this task's files was staged in any phase commit
  (`git log --stat` over this task's commits).
- [ ] Record in the implementation summary: the guard-first normalization and its confirmed
  occurrence counts; the Phase 4 audit record (checklist sites that did not go red, and why; any
  `examples.py` expectation delta; which branch objective 2.5 took); route taken (Route 2) and why
  Route 1 is infeasible; the Lean-side counterpart recorded as deferred; the confirmed
  family/corpus counts from Phase 6's Scope Hypothesis; whether the Phase 5 decoder import needed
  the `_certificate_model.py` fallback; and whether any sixth doc location was found in Phase 8.

**Timing**: 30 minutes

**Depends on**: 8

**Verification Tier**: full

**Commit Mode**: per-substep

**Files to modify**:
- None (verification and summary only)

**Verification**:
- All three pytest invocations exit 0 with no new failures, errors, or skips relative to the
  Phase 1 baseline.
- A test failure in a file outside this task's scope is treated as possibly a concurrent sibling's
  in-flight edit: check `git log`/`git status` before attributing it to this work, and report
  rather than silently fixing.

## Testing & Validation

- [ ] `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/unit/test_formula.py -v` green
- [ ] `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/ -v` green
- [ ] `PYTHONPATH=code/src pytest oracle/bimodal_logic/tests/ -q` green
- [ ] `PYTHONPATH=code/src pytest code/tests/ -q` green
- [ ] Every previously-passing truth-value assertion still passes after both the convention and its
      formula strings are flipped together; no `examples.py` `expectation` flag changed
- [ ] `fixtures/certificates/expected_verdicts.json` unchanged
- [ ] `translate`'s `\Until`/`\Since` rules are positional identity; no code path swaps operands
- [ ] `DefNextOperator`/`DefPrevOperator` derivations are guard-first (`U(bot, phi)` / `S(bot, phi)`)
- [ ] `oracle/bimodal_logic/translation.py`'s `_PRIMITIVE_BINARY` renders guard-first
- [ ] No document or docstring states the event-first convention as live
- [ ] The pre-existing `TestTranslateTruthPreservation` parametrization still collects and passes
      (regression guard on the evaluator generalization)
- [ ] `TestTranslateTruthPreservationBox` collects and passes with no skips or xfails
- [ ] The coherence-precondition test passes and rejects `03_box_unfaithful.json`
- [ ] All five negative controls pass by detecting their injected defect
- [ ] Neither evaluator calls `translate`; no helper consumes both an AST and a `Formula`
- [ ] Every defined operator (`\neg`, `\wedge`, `\vee`, `\rightarrow`, `\Diamond`, `\top`,
      `\future`, `\past`, `\next`, `\prev`) appears in the generated corpus
- [ ] At least one asymmetric `\Until` and one asymmetric `\Since` case are present and provably
      order-sensitive
- [ ] No `NotImplementedError` remains on any evaluator branch in `test_formula.py`

## Artifacts & Outputs

- `code/src/model_checker/theory_lib/bimodal/operators.py` — guard-first `Until`/`Since`
  `true_at`/`false_at`; guard-first `\next`/`\prev` derivations; docstrings rewritten
- `code/src/model_checker/theory_lib/bimodal/semantic/formula.py` — `translate` positional identity;
  module docstring records that there is no longer a swap
- `oracle/bimodal_logic/translation.py` — guard-first infix rendering, in lockstep with the theory
- `code/src/model_checker/theory_lib/bimodal/examples.py` — BX axiom renderings flipped, meanings
  preserved, expectations untouched
- Bimodal and oracle test files — every order-bearing formula string flipped; the order test
  rewritten to positional identity
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_formula.py` — family-aware evaluators
  with box clauses, generated defined-operator corpus, `TestTranslateTruthPreservationBox`,
  coherence precondition, and five negative controls
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_certificate_fixtures.py` — internal
  tuple order aligned (or the documented fallback)
- `code/src/model_checker/theory_lib/bimodal/README.md`, `docs/API_REFERENCE.md`,
  `docs/ARCHITECTURE.md`, `docs/USER_GUIDE.md`, `oracle/bimodal_logic/README.md`,
  `oracle/bimodal_logic/KNOWN_EXTERNAL_DEFECTS.md` — one argument order throughout
- `code/src/model_checker/theory_lib/bimodal/docs/ADEQUACY.md` — §2 S4 row, §4.2, §6.3 updated;
  route decision and normalization recorded
- `code/src/model_checker/theory_lib/bimodal/docs/TRUST_PIPELINE.md` — Stage 1 evidence and
  "What remains" rows updated; Lean-side half marked deferred
- `specs/196_discharge_s4_translation_bridge/summaries/01_*-summary.md` — normalization record,
  route taken and why, confirmed scope hypotheses, deferral record

## Rollback/Contingency

Every phase's edits are confined to an enumerated file set and committed per green sub-step (Phase
2 as one atomic batch), so rollback is `git revert` of this task's own commits in reverse order —
no working-tree discard is needed and no snapshot is required for the ordinary path. Phase 2's
single commit is deliberately the unit of rollback for the whole normalization: reverting it
restores one consistent convention rather than leaving a half-flipped tree. If a genuine whole-tree
rollback of uncommitted work becomes necessary, follow `context/contracts/recovery.md`'s rollback
rung for the exact `git-snapshot.sh` invocation shape (including its out-of-scope override flag);
never emit a bare reverting-mode snapshot as a routine checkpoint, and prefer `--no-revert` for a
defensive checkpoint before risky work.

**Contingency — an `examples.py` expectation would have to change.** Stop at Phase 2, mark it
`[BLOCKED]`, and report the example, its `# Formula:` invariant, the two readings, and the
expectation delta. An axiom schema that was denoting a different proposition than its name and
comment claim is a finding about the example corpus, not a sweep step, and the recorded
`expectation` may have been passing for the wrong reason.

**Contingency — tasks 193 or 194 have not landed.** Mark Phase 1 `[BLOCKED]` and stop. The sweep
must not run against a tree those tasks are still editing, and 193 adds closure formulas to
`test_certificate_a2_triangle.py` that this sweep must cover.

**Contingency — the property test reveals a real defect in `translate`.** Stop at that phase, mark
it `[BLOCKED]`, leave production code untouched, and report the failing sentence, family, lasso
index and time point. A translation defect is a finding about the soundness claim S4 guards, not a
drive-by fix, and deserves its own task. (A defect *introduced* by the normalization is different:
that is this task's own regression and is fixed in place.)
