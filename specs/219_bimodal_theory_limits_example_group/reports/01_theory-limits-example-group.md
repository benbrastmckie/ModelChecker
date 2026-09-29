# Research Report: Bimodal Theory-Limits Example Group

- **Task**: 219 - Add a documented THEORY-LIMITS example group to bimodal's examples.py
- **Started**: 2026-09-29T00:00:00Z
- **Completed**: 2026-09-29T00:00:00Z
- **Effort**: ~2 hours
- **Dependencies**: None (task 217, re-scoping the blocked adequacy-consumer entries in
  specs/state.json, is a concurrent sibling this cycle; it edits specs/ metadata only and shares
  no file with this task's own scope)
- **Sources/Inputs**:
  - `code/src/model_checker/theory_lib/bimodal/examples.py` (full read; structure, conventions,
    registry wiring)
  - `code/src/model_checker/theory_lib/bimodal/operators.py` (operator inventory; confirmed no
    stability-modal operator exists)
  - `code/src/model_checker/theory_lib/bimodal/docs/ADEQUACY.md` (never-report-validity rule;
    the name-plus-manifest citation convention, section with the Lean citation table)
  - `code/src/model_checker/theory_lib/bimodal/tests/unit/test_bimodal.py` (registry-to-test
    wiring; confirmed no exclusion set is currently needed)
  - `/home/benjamin/Projects/BimodalLogic/FormalSystem/Metalogic/Decidability/PlusWitnessFamily/Incompleteness.lean`
    (full read; the congruence lemma and the two non-certification theorems)
  - `/home/benjamin/Projects/BimodalLogic/FormalSystem/PlusLanguage/PlusNonValidities.lean`
    (the sibling refutation whose two histories the incompleteness proof reuses)
  - `/home/benjamin/Projects/BimodalLogic/FormalSystem/Syntax/Formula.lean`,
    `FormalSystem/PlusLanguage/Formula.lean`, `FormalSystem/ProofSystem/Axioms.lean` (constructor
    lists for `Formula`, `PlusFormula`, and the `Axiom` inductive's domain)
  - `specs/state.json` (project 200 `extend_bimodal_to_stability_modal`, blocked; project 217
    `rescope_blocked_adequacy_consumers`, the source of the superseded-diagnosis correction)
  - Empirical probes against the live checker (four scratch scripts, not committed; see Appendix)
- **Artifacts**: this report
- **Standards**: status-markers.md, artifact-management.md, tasks.md, report-format.md

## Executive Summary

- The upstream result is confirmed exactly as described: `(g S e) -> [stab](g S e)` is a genuine
  ℤ-time non-validity (`not_plusValidZTime_stabSnce`), yet BimodalLogic's branching L⁺ certificate
  provably certifies **no** instance of it, at any time or size, in either target placement
  (`not_plusCertifies_stabSnce`, `not_plusCertifies_stabSnce_premise`). That is a completeness gap
  in a certificate system, not unsoundness and not a defect of this theory.
- Confirmed against the live Lean tree: the stability modal is outside the base `Formula`
  language entirely (`Formula`'s six constructors are atom/bot/imp/box/untl/snce; `Axiom` ranges
  only over `Formula`). `stab` exists only in `PlusFormula`. So this was never a candidate axiom.
- The "temporal asymmetry" diagnosis (since-clause quantifies at its own time, until-clause
  "escapes" at the successor time) is confirmed superseded. The actual mechanism is shape-based,
  not temporal: any local-coherence clause of the form "for all j accessible from i, phi holds at
  i iff a condition on j alone" forces invariance across the whole accessibility class, derivable
  from reflexivity alone by reading the clause twice and chaining. `snce_share_congr`'s entire
  proof is exactly that two-instance chain.
- Two nearest-expressible probes were built and run empirically against the live checker (no
  files changed): `\Past A -> \Box \Past A` and `(A \Since B) -> \Box (A \Since B)`. **Both are
  genuinely invalid here too** -- countermodels found in well under 150ms, stable across 20
  consecutive runs each, at both the default and enlarged segment lengths. This checker has no
  difficulty with either; the certificate gap is specific to BimodalLogic's `stab`-certification
  design, not to expressibility in this theory.
- **The Box-versus-stability question is answered, not assumed**: Box's countermodels do not
  even require the two histories to agree at the evaluation time -- `\Box`'s accessibility
  carries no same-state restriction at all. The Box-form's invalidity is the same elementary
  "necessitation fails for any contingent formula" pattern already exercised by
  `MD_CM_3`/`BM_CM_1`/`BM_CM_2`, not evidence of, and not needing, the share-class invariance
  mechanism that empties the verified side's certificate class for the `stab`-form. Box and the
  stability modal reach the same qualitative verdict on these schemas for unrelated reasons.
  Nothing here says they agree in general.
- Recommendation: add a `THEORY-LIMITS` section with two real, currently-decidable
  `TL_CM_*`-prefixed countermodel entries (wired into both `countermodel_examples` and the active
  `example_range` as ordinary regression tests), a header block covering the required six points,
  and record the `stab`-form itself only in prose as pending the blocked stability-modal
  extension task -- it cannot be written as a runnable entry today and must not be.

## Context & Scope

Task 219 asks for a new, documented example group in
`code/src/model_checker/theory_lib/bimodal/examples.py` that records results which are limits of
this theory or of its verified (BimodalLogic Lean) counterpart -- kept deliberately so they are
learned from rather than rediscovered. The seed case is the stability-modal ("since is stable",
`⊡`) non-certification result. This research phase's job is to verify every claim in the task
description against the live trees (both repositories), determine what is actually expressible in
this Python theory today, run the nearest-expressible probes empirically, and answer the
Box-versus-stability question the task explicitly forbids assuming. No file under `code/` was
changed during this research; all empirical checks used disposable scratch scripts that
instantiate `BimodalSemantics`/`BimodalStructure` directly (see Appendix), never `examples.py`
itself.

BimodalLogic (`/home/benjamin/Projects/BimodalLogic`) is read-only ground truth for this task and
was not edited. Cross-repository task numbers appear in this report and may appear in this task's
other `specs/` artifacts, but must not appear in any file under `code/` (a separate repository
rule, `no-task-references-in-deliverables.md`, which the draft header text below already
respects).

## Findings

### 1. The two-fact structure is confirmed exactly

- **Fact 1 (genuine, desirable non-validity)**: `stabSnceTarget g e := (g S e) → ⊡(g S e)`
  (`FormalSystem.Metalogic.Decidability.PlusSharingWitnessFamily.stabSnceTarget`). At `g := ⊤`,
  `e := p` this is `Pp → ⊡Pp` (P = "at some past time"), proved non-valid over ℤ-time by
  `FormalSystem.Metalogic.Decidability.PlusSharingWitnessFamily.not_plusValidZTime_stabSnce`,
  which refutes it on the permissive frame `NF` using the same two histories
  `FormalSystem.PlusLanguage.PlusNonValidities.refute_somePast_stab` uses (one constantly at
  state `0`; one at state `1` for every negative time, `0` elsewhere). They agree at time `0`
  but differ in their pasts -- exactly "the past is not determined by the present world state."
  Nothing about this theory should change to make the schema valid.
- **Fact 2 (the actual limit -- a certificate-completeness gap)**:
  `FormalSystem.Metalogic.Decidability.PlusSharingWitnessFamily.not_plusCertifies_stabSnce` and
  `...not_plusCertifies_stabSnce_premise` jointly prove that **no** `PlusSharingWitnessFamily`
  certifies any instance of the schema, at any time `t`, at any size, whether the schema sits in
  the conclusion list or as a negated premise. The certificate class is empty for this schema.
  Both theorems' module docstring is explicit that soundness (`plusTruth_iff_mem`,
  `plusRefutes_of_certifies`) is untouched; what fails is completeness of one certificate design.

### 2. Confirmed not an axiom problem, against the live constructor lists

- `FormalSystem.Syntax.Formula` (`FormalSystem/Syntax/Formula.lean:76`) has exactly six
  constructors: `atom`, `bot`, `imp`, `box`, `untl`, `snce`.
- `FormalSystem.ProofSystem.Axiom` (`FormalSystem/ProofSystem/Axioms.lean:152`) is declared
  `Axiom : Formula → Type` -- it ranges over the base `Formula` type only.
- `FormalSystem.PlusLanguage.PlusFormula` (`FormalSystem/PlusLanguage/Formula.lean:91`) adds
  exactly one constructor beyond `Formula`'s six: `stab`.
- So `stab` cannot appear inside any `Axiom` instance by construction, independent of any
  soundness argument. Soundness constrains derivability against validity; what fails for the
  `stab`-schema is the converse-direction obligation (every non-validity admits a finite
  certificate), which is a different property from anything an axiom system states or needs.

### 3. The "temporal asymmetry" diagnosis is confirmed superseded

`specs/state.json` project 217 (`rescope_blocked_adequacy_consumers`, a concurrent sibling this
cycle, specs-metadata-only) records the correction directly: an earlier explanation attributed
the certificate gap to "the since-clause quantifies its predecessor at the label's own time while
the until-clause escapes by quantifying at the successor time." That explanation is refuted by a
second upstream research round. The mechanism has no temporal content:

- `snce_share_congr` (`FormalSystem.Metalogic.Decidability.PlusSharingWitnessFamily.snce_share_congr`,
  `Incompleteness.lean:108-114`) proves: for `share`-related indices `i`/`j` at time `t`, `i` and
  `j` agree on every `snce` formula of the closure. Its entire proof is two readings of the one
  local-coherence clause chained together -- once at `j` from `i`'s side (using `hij : share t i
  j`), once at `j` from `j`'s own side (using reflexivity, `share_refl`) -- then `.trans .symm`.
- The general shape: any clause of the form "for all `j` accessible from `i`, `phi` holds at `i`
  iff `<condition mentioning only j>`" is an invariance axiom for `phi` across the whole
  accessibility class, derivable from **reflexivity alone**, by exactly that two-instance chain.
  Nothing about *which* direction (`untl` vs `snce`) is quantified matters; what matters is that
  the clause's right-hand side depends only on the class member, not on which representative
  asked.
- `share` is confirmed to be an equivalence relation (reflexive, per `share_refl` used above; the
  module docstring calls it "literally an equality of representatives"), so the forced invariance
  runs across the *entire* class, not merely a pair -- consistent with the report's requirement.
- The module's own "What this does NOT show" section states the `untl` side is defect-free "by
  inspection, not by machine check" -- i.e. no theorem asserts `untl` avoids the collapse; it is
  recorded as an open positive obligation for the substrate redesign, not a proved asymmetry.

### 4. What is expressible today, verified against operators.py

`code/src/model_checker/theory_lib/bimodal/operators.py` defines exactly: `NegationOperator`,
`AndOperator`, `OrOperator`, `BotOperator`, `NecessityOperator` (`\Box`), `FutureOperator`
(`\Future`, "always in the future"/G), `PastOperator` (`\Past`, "always in the past"/H),
`UntilOperator` (`\Until`, guard-first), `SinceOperator` (`\Since`, guard-first), plus the defined
`\rightarrow`/`\leftrightarrow`/`\top`/`\Diamond`/`\future`/`\past`/`\next`/`\prev` operators. A
repo-wide grep for `stab`/`stability` inside the bimodal package (`.py` files) returns nothing.
There is no stability-modal operator, confirming the task description's premise directly against
the live source rather than trusting it.

Given that, the task's two named candidates were built and run empirically (see Appendix for the
exact scratch harness and raw output):

| Probe | Premises | Conclusion | Result | Timing |
|---|---|---|---|---|
| Since-form (general) | `(A \Since B)` | `\Box (A \Since B)` | Countermodel found (invalid) | 20/20 runs pass, 41-101ms; stable at enlarged segment lengths (back=4/mid=3/fwd=4) too |
| Past-form (`\Past`, H) | `\Past A` | `\Box \Past A` | Countermodel found (invalid) | 20/20 runs pass, 61-143ms; stable at enlarged segment lengths too |
| (reference only) atomic mirror | `\past A` | `\Box \past A` | Countermodel found (invalid) | 20/20 runs pass, 55-102ms |

All three decide `sat` (a countermodel exists) reliably and fast at the file's own default
segment lengths (`back=2, mid=1, fwd=2`). A sanity probe (`\Box A -> \Box \Box A`, i.e. Modal 4,
already `MODAL_4_TH`) correctly decided `unsat` (no countermodel, a genuine theorem) under the
same harness, confirming the harness distinguishes the two outcomes correctly rather than always
returning "sat."

`dev_cli.py` output for the Since-form and Past-form (full transcript in Appendix) shows both
countermodels use **two histories that differ at the evaluation time itself** -- e.g. for the
Past-form, the main history has `A` at `t=-2` while the witness history has `∅` at `t=-2`, the
very time the conditional is evaluated at. This is the load-bearing empirical fact behind Finding
5 below.

### 5. The Box-versus-stability question, answered rather than assumed

The task forbids assuming Box and the stability modal agree on this schema. They do agree on the
bottom-line verdict here (both invalid) but for **different, unrelated reasons**:

- `⊡` (stability) quantifies only over histories that **share the current world state** with the
  evaluation history. Fact 2's certificate gap is specifically about that restricted,
  same-state-anchored quantification: the local-coherence clause forces every member of that
  restricted class to agree on `snce` formulas, which is exactly what makes `(g S e) → ⊡(g S e)`
  uncertifiable.
- `\Box` in this theory has no analogous restriction: it is necessity over the full accessible
  set of world-histories, unconstrained by agreement at the evaluation time. The countermodels
  found above confirm this directly -- the witness history disagrees with the main history even
  at the evaluation time itself, something a `⊡`-style same-state restriction would forbid by
  construction.
- Consequently, `\Past A -> \Box \Past A` and `(A \Since B) -> \Box (A \Since B)` fail for the
  same elementary reason `MD_CM_3` ("Actuality to Necessity", `A -> \Box A`) and `BM_CM_1`/`BM_CM_2`
  ("All Future/Past to Necessity") already fail: any formula that is not itself necessary can be
  falsified by *some* accessible world, and Box has no filter excluding worlds that disagree with
  the present state. This is not the share-class invariance argument from Finding 3 -- it is a
  simpler, pre-existing pattern this file already tests elsewhere.
- So: the Box-form's invalidity is real, checker-verified, and worth recording as a limit-adjacent
  fact (it is the nearest expressible relative of the `stab`-form) -- but it must not be presented
  as confirming, explaining, or standing in for Fact 2's mechanism. The two invalidities are
  coincidentally aligned in verdict, not causally linked.

### 6. Registry and wiring conventions confirmed

- Countermodel/theorem naming follows `{PREFIX}_CM_n`/`{PREFIX}_TH_n` with prefixes `EX`, `MD`,
  `TN`, `BM` (verified against the module's own top docstring and every entry). No existing
  prefix fits a cross-cutting "theory limits" category; a new `TL` prefix (`TL_CM_*`, reserving
  `TL_TH_*` for a future limit that is theorem-shaped) is consistent with the existing scheme and
  immediately greppable.
- `countermodel_examples`/`theorem_examples` feed `unit_tests` (`{**countermodel_examples,
  **theorem_examples}`), which is aliased to `test_example_range` (required by
  `theory_lib.get_test_examples`) and separately parametrized directly by
  `tests/unit/test_bimodal.py`. `example_range` is the independently-curated active subset run by
  the CLI/`dev_cli.py`.
- `KNOWN_TIMEOUT_EXAMPLES` and `UNSTABLE_EXAMPLES` in `test_bimodal.py` are both currently empty
  by design (the certificate encoding removed the quantifier-heavy cost profile that motivated
  them historically). Both new entries decide in well under 150ms, so neither set needs a new
  member.
- Precedent for "provable but not encodable as a boolean-`expectation` entry" already exists:
  `A0`'s `prior_UZ`/`z1` frame-class instances are tested directly in
  `tests/unit/test_structure.py::TestA0FrameClassStandingTest` instead of as `examples.py`
  entries, because their true verdict ("no certificate at any length, but not thereby valid")
  does not fit the boolean field. That precedent does **not** apply to the `stab`-schema itself:
  `A0`'s instances are expressible `Formula`-level schemas whose problem is decidability, whereas
  `stab` cannot be written in this theory's syntax at all. The correct treatment for the
  `stab`-form is therefore prose-only (header commentary), with no corresponding Python object of
  any kind -- not a standing test, not an inactive dict entry.

### 7. Citation convention confirmed against this theory's own precedent

`docs/ADEQUACY.md`'s Lean-citation table states the convention this task's citations must follow:
"the declaration names in this table are the load-bearing citation; the line numbers are a
derived view taken from BimodalLogic's generated, C35-gated `scripts/lean-citation-manifest.json`"
-- recorded there specifically because line numbers previously drifted silently under unchanged
names. `BimodalLogic/scripts/lean-citation-seeds.txt`/`lean-citation-manifest.json` do not yet
list the five declarations this task needs to cite (`snce_share_congr`, `stabSnceTarget`,
`not_plusCertifies_stabSnce`, `not_plusCertifies_stabSnce_premise`,
`not_plusValidZTime_stabSnce`) -- confirmed by grep. That manifest lives in BimodalLogic, which
this task must not edit, so the new header/comments should cite by fully-qualified name only (no
file:line at all, stricter than `docs/ADEQUACY.md`'s own table), matching the task instruction
directly. Flagged as a minor, non-blocking follow-up: a future BimodalLogic-side task could add
these five names to its seed list so a future ModelChecker citation table gains the same
manifest-backed drift protection `docs/ADEQUACY.md`'s existing table has.

### 8. Baseline test status

`PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/unit/test_bimodal.py
-q` passes at 53/53 before any change from this task, establishing a clean baseline for the
implementation phase to diff against.

## Decisions

- The new group's inclusion criterion (for the implementation phase to encode verbatim in the
  header) is: an entry belongs here iff it records either (a) a genuine, currently-passing
  countermodel test whose significance -- why the schema fails and why that is desirable --
  deserves recording alongside the test, or (b) a completeness gap in the verified side's
  certificate system, where the gap is a property of that system's design and not evidence
  against this theory. Nothing whose real content is a retracted upstream claim may be encoded as
  a passing assertion.
- Both empirically-verified Box-analogue probes are added as real, active regression tests
  (`countermodel_examples` and `example_range`), not recorded-but-inactive: their expected outcome
  ("countermodel found") is a legitimate, currently-true fact about this checker, unlike the
  `stab`-schema itself.
- The `stab`-schema is recorded in prose only, in the group's header, explicitly marked pending
  the blocked stability-modal extension task (project 200 in this repository's own tracking, not
  to be named by number inside `code/`). No Python object, active or inactive, is created for it.
- The Box-versus-stability relationship is stated explicitly as "same verdict, different and
  unrelated mechanism" -- never as agreement, and never left silently unaddressed.

## Recommendations

1. **Add a `THEORY-LIMITS` section to `examples.py`**, positioned after the existing `THEOREMS`
   section and before `BX AXIOM SYSTEM EXAMPLES` (or after that section; either placement is
   fine, since section order in this file does not encode a dependency), with the header content
   below and two entries, `TL_CM_1` and `TL_CM_2`.

   Header block (ready to use verbatim; already respects
   `no-task-references-in-deliverables.md` -- no task numbers, no BimodalLogic task numbers):

   ```python
   ##############################################################################
   ############################# THEORY-LIMITS #################################
   ##############################################################################
   # INCLUSION CRITERION: an entry belongs here iff it records an outcome that is a genuine,
   # permanent limit of this theory or of its verified (BimodalLogic Lean) counterpart -- never
   # a bug, never something a future encoding change should remove, and never evidence that any
   # axiom, operator, or truth clause in this file is wrong. Two independent kinds of limit
   # qualify: (a) a genuine ZZ-time non-validity this checker correctly reports as a countermodel,
   # whose significance deserves recording alongside the passing test; (b) a completeness gap in
   # the VERIFIED side's own certificate system -- a schema for which no certificate meeting that
   # system's conditions exists at any time or size, even though the schema is a genuine
   # non-validity, so the empty certificate class is a fact about the certificate DESIGN, not
   # about whether the schema is valid. Never encode a retracted upstream claim as a passing
   # assertion here.
   #
   # --- FACT 1: a genuine ZZ-time non-validity (correct and desirable, not a limit of anything) ---
   # `(g S e) -> [stab](g S e)` (`g`/`e` = Since's guard/event) is genuinely INVALID over ZZ-time.
   # Its atomic instance at g:=top, e:=p is `Pp -> [stab]Pp` (P = "at some past time"), proved
   # non-valid by
   # `FormalSystem.Metalogic.Decidability.PlusSharingWitnessFamily.not_plusValidZTime_stabSnce`
   # (BimodalLogic). This says the past is not determined by the present world state: two
   # histories can agree now and disagree in how they got here. Nothing here should change to
   # make this schema valid.
   #
   # --- FACT 2: a completeness gap in the VERIFIED SIDE's certificate system (the actual limit) ---
   # BimodalLogic's branching L-plus certificate provably CANNOT certify any instance of
   # `(g S e) -> [stab](g S e)`, at any time, at any size, whether the schema is a conclusion or a
   # negated premise
   # (`FormalSystem.Metalogic.Decidability.PlusSharingWitnessFamily.not_plusCertifies_stabSnce`,
   # `...not_plusCertifies_stabSnce_premise`). The certificate class is EMPTY for this schema.
   # That is a gap in that certificate SYSTEM's completeness -- not unsoundness, not a defect of
   # this theory, and not a defect of THIS checker (see below).
   #
   # --- NOT AN AXIOM PROBLEM ---
   # The stability modal is not even in the language BimodalLogic's axioms are stated over:
   # `FormalSystem.ProofSystem.Axiom` is `Formula -> Type`, and `FormalSystem.Syntax.Formula`'s
   # constructors are atom, bot, imp, box, untl, snce -- no `stab`. `stab` exists only in the
   # extended `FormalSystem.PlusLanguage.PlusFormula`. This schema was never a candidate axiom,
   # and no soundness proof could have ruled it in or out: soundness constrains derivability
   # against validity, while what fails here is the converse obligation that every non-validity
   # admit a finite certificate.
   #
   # --- A LIMIT OF THE VERIFIED SIDE, NOT OF THIS CHECKER ---
   # `[stab]` is also absent from THIS theory's operators today (adding it is the blocked
   # stability-modal-extension task's scope, not this group's -- see the last section below).
   # But this checker finds countermodels to the nearest EXPRESSIBLE relatives of this schema,
   # substituting `\Box` for the missing `[stab]`, perfectly well and fast (TL_CM_1/TL_CM_2
   # below). "No certificate exists" above is a fact about BimodalLogic's certificate design, not
   # about this Python checker's search.
   #
   # --- THE SHAPE MECHANISM (a temporal-asymmetry diagnosis is SUPERSEDED; corrected here) ---
   # An earlier diagnosis blamed a temporal asymmetry -- that the local-coherence `snce` clause
   # quantifies its predecessor at the same time as the label it is about, while the `untl`
   # clause "escapes" by quantifying at the successor time. That diagnosis is REFUTED: `snce` is
   # already the exact mirror of `untl` relative to the underlying thread's step relation, and
   # BOTH clauses collapse the same way; the mechanism has no temporal content. Any
   # local-coherence clause of the shape "for all j accessible from i, phi holds at i iff a
   # condition on j alone" is an invariance axiom for phi across the whole accessibility class,
   # derivable from REFLEXIVITY ALONE: read the clause once at an arbitrary class member, once
   # more at that member against itself via reflexivity, then chain the two biconditionals
   # (`FormalSystem.Metalogic.Decidability.PlusSharingWitnessFamily.snce_share_congr`'s entire
   # proof is exactly that two-instance chain). The certificate's "share" relation is literally an
   # equality of representatives -- an equivalence -- so the forced invariance runs across the
   # entire class, not merely a pair.
   #
   # --- STANDING CONSEQUENCE ---
   # On this fragment, the verified side has a SEMI-decision procedure, not a decision procedure:
   # an empty enumeration of certificates licenses no conclusion about validity (see
   # docs/ADEQUACY.md section 7.4's never-report-validity rule, which this reinforces rather than
   # contradicts). Recorded here as a limit to learn from, not a bug to chase.
   #
   # --- THE STABILITY-MODAL SCHEMA ITSELF: PENDING, NOT ENCODED ---
   # `(g S e) -> [stab](g S e)` cannot be written as an examples.py entry today: `[stab]` has no
   # ModelChecker operator, and adding one pre-empts the blocked stability-modal extension task,
   # which remains blocked for its own, still-current soundness/design reasons (the histories
   # characterization and the box case of the truth lemma). This is intentional; it should stay
   # this way until that task lands.
   #
   # --- NEAREST EXPRESSIBLE PROBES, AND THE BOX-VERSUS-STABILITY QUESTION ---
   # `\Box` (necessity over ALL accessible world-histories) and `[stab]` (quantification
   # restricted to histories sharing the CURRENT world state) are different modals with
   # different reach; this file does not assume they agree on this schema. Both
   # nearest-expressible relatives below -- substituting `\Box` for `[stab]` -- ARE invalid here
   # too, but for a DIFFERENT, more basic reason than Fact 2's share-class invariance argument:
   # `\Box`'s countermodels use histories that do not even agree at the evaluation time itself
   # (see each entry below), because `\Box`'s accessibility carries no same-state restriction at
   # all. Any contingent formula can falsify `phi -> \Box phi` this way -- the same elementary
   # pattern already exercised by MD_CM_3 and BM_CM_1/BM_CM_2 above. The Box-form's failure is
   # NOT evidence of, and does not need, the invariance-across-equivalence-class mechanism that
   # empties the verified side's certificate class for the `[stab]`-form. Both entries below are
   # ordinary, currently-passing countermodel regression tests.
   ##############################################################################
   ```

   Entries:

   ```python
   # TL_CM_1: SINCE-STABILITY LIMIT, BOX-ANALOGUE (general guard/event form)
   # Nearest expressible translation of BimodalLogic's `(g S e) -> [stab](g S e)`
   # (`FormalSystem.Metalogic.Decidability.PlusSharingWitnessFamily.stabSnceTarget`), substituting
   # `\Box` for the not-yet-implemented `[stab]`. Genuinely invalid here -- see the header's
   # "Box-versus-stability question" discussion for why. Measured (2026-09-29): decides in well
   # under 150ms at these defaults; confirmed stable across 20 consecutive runs and at enlarged
   # segment lengths (back=4/mid=3/fwd=4).
   TL_CM_1_premises = ['(A \\Since B)']
   TL_CM_1_conclusions = ['\\Box (A \\Since B)']
   TL_CM_1_settings = {
       'back' : 2,
       'mid' : 1,
       'fwd' : 2,
       'max_time' : 10,
       'expectation' : True,
   }
   TL_CM_1_example = [
       TL_CM_1_premises,
       TL_CM_1_conclusions,
       TL_CM_1_settings,
   ]

   # TL_CM_2: PAST-STABILITY LIMIT, BOX-ANALOGUE (the \Past/H probe)
   # A second nearest-expressible probe, using the "always in the past" operator rather than the
   # fully general Since-schema. Also genuinely invalid, same reason as TL_CM_1 (see header).
   # Measured (2026-09-29): decides in well under 150ms at these defaults; confirmed stable across
   # 20 consecutive runs and at enlarged segment lengths.
   TL_CM_2_premises = ['\\Past A']
   TL_CM_2_conclusions = ['\\Box \\Past A']
   TL_CM_2_settings = {
       'back' : 2,
       'mid' : 1,
       'fwd' : 2,
       'max_time' : 10,
       'expectation' : True,
   }
   TL_CM_2_example = [
       TL_CM_2_premises,
       TL_CM_2_conclusions,
       TL_CM_2_settings,
   ]
   ```

2. **Registry wiring**: add both to `countermodel_examples` (a new "Theory-Limits Countermodels"
   subsection) and to `example_range`'s countermodels block. Both flow through to `unit_tests` /
   `test_example_range` automatically via the existing `{**countermodel_examples,
   **theorem_examples}` merge, so `test_bimodal.py` picks them up with no code change there.
   Neither `KNOWN_TIMEOUT_EXAMPLES` nor `UNSTABLE_EXAMPLES` needs a new member.

3. **Update the top-of-file docstring's naming-convention list** ("Countermodels: EX_CM_*,
   MD_CM_*, TN_CM_*, BM_CM_*") to add `TL_CM_*` (reserve `TL_TH_*` for a future limit that turns
   out to be theorem-shaped; none is needed now).

4. **Do not** create any Python object -- active, inactive, or a standing test in
   `test_structure.py` -- for the `(g S e) -> [stab](g S e)` schema itself. It is not
   representable in this theory's syntax today (unlike A0's `prior_UZ`/`z1`, which are
   expressible `Formula`-level schemas with a decidability problem, not a syntax problem). Prose
   in the header is the entire treatment.

5. **Verification for the implementation phase**: after adding the section, run
   `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/unit/test_bimodal.py -q`
   and confirm 55/55 (53 existing + `TL_CM_1` + `TL_CM_2`), then the full bimodal suite, then the
   four-theory gate per this repository's own convention. No existing example's premises,
   conclusions, or settings should change.

## Risks & Mitigations

- **Risk**: a future reader conflates the Box-form countermodels (TL_CM_1/TL_CM_2) with the
  `stab`-form's certificate gap, treating the former as if it explained or validated the latter.
  **Mitigation**: the header's dedicated "Box-versus-stability question" paragraph states the
  relationship explicitly (same verdict, unrelated mechanism); this is the single most
  load-bearing paragraph in the whole header and should not be trimmed during implementation.
- **Risk**: the fully-qualified Lean citations drift if BimodalLogic renames the cited
  declarations, with nothing on the ModelChecker side to catch it (BimodalLogic's own
  citation-manifest gate does not yet track these five names; see Finding 7).
  **Mitigation**: accepted as a known, non-blocking gap consistent with the task's own
  instruction to cite by name rather than file:line; flagged here for a possible future
  BimodalLogic-side seed-list addition, out of scope for this task.
- **Risk**: a future contributor extends this group by adding an entry whose real content is an
  upstream claim not yet independently re-verified in this repository's own research.
  **Mitigation**: the inclusion criterion in Decisions/Recommendation 1 states this explicitly
  ("never encode a retracted upstream claim as a passing assertion"), giving a concrete bar for
  any future addition to check against.

## Appendix

### Empirical probe harness (not committed; scratch only)

Four scratch scripts under the session scratchpad directory instantiated
`BimodalSemantics`/`ModelConstraints`/`BimodalStructure` directly (the same pipeline
`utils/testing.py::run_test` uses) and read `z3_model_status` directly, independent of the
`expectation` setting, so a single run distinguishes "countermodel found" (`True`) from "no
countermodel" (`False`/theorem) without needing to guess the expected outcome first. A `dev_cli.py`
run against a throwaway `example_range` (not `examples.py` itself) confirmed the same verdicts
with full countermodel printouts, reproduced below for the record.

`dev_cli.py` output, Past-form (`\Past A -> \Box \Past A`):

```
EXAMPLE PROBE1: there is a countermodel.
Search bounds: back=2, mid=1, fwd=2 (2 lassos: 1 main + 1 reserved witness)
Histories:
  L0  main                      ... [-2:A] => (-1:A) => (0:{}) => (+1:{}) => (+2:A) ...
  L1  witness for \Box \Past A  ... (-2:{}) => (-1:A) => (0:{}) => (+1:A) => (+2:A) ...
Box guesses:
  \Box \Past A  false  falsified at L1, t=-2
Solver Run Time: 0.0015 seconds
```

`dev_cli.py` output, Since-form (`(A \Since B) -> \Box (A \Since B)`):

```
EXAMPLE PROBE2: there is a countermodel.
Histories:
  L0  main                           ... [-2:{}] => (-1:B) => (0:{}) => (+1:{}) => (+2:{}) ...
  L1  witness for \Box (A \Since B)  ... (-2:{}) => (-1:{}) => (0:{}) => (+1:{}) => (+2:{}) ...
Box guesses:
  \Box (A \Since B)  false  falsified at L1, t=-2
Solver Run Time: 0.0012 seconds
```

Both transcripts show `L0` and `L1` disagreeing on their atoms at `t=-2`, the evaluation time
itself -- the concrete evidence behind Finding 5 (Box's accessibility carries no same-state
restriction, unlike `stab`'s share-class).

### References (fully qualified declaration names, BimodalLogic)

- `FormalSystem.Metalogic.Decidability.PlusSharingWitnessFamily.stabSnceTarget`
- `FormalSystem.Metalogic.Decidability.PlusSharingWitnessFamily.notStabSnceTarget`
- `FormalSystem.Metalogic.Decidability.PlusSharingWitnessFamily.snce_share_congr`
- `FormalSystem.Metalogic.Decidability.PlusSharingWitnessFamily.not_plusCertifies_stabSnce`
- `FormalSystem.Metalogic.Decidability.PlusSharingWitnessFamily.not_plusCertifies_stabSnce_premise`
- `FormalSystem.Metalogic.Decidability.PlusSharingWitnessFamily.not_plusValidZTime_stabSnce`
- `FormalSystem.PlusLanguage.PlusNonValidities.refute_somePast_stab`
- `FormalSystem.Syntax.Formula` (inductive; six constructors: atom, bot, imp, box, untl, snce)
- `FormalSystem.PlusLanguage.PlusFormula` (inductive; the six above plus `stab`)
- `FormalSystem.ProofSystem.Axiom` (inductive, `Formula -> Type`)

### References (this repository)

- `code/src/model_checker/theory_lib/bimodal/examples.py` (structure and conventions this group
  extends)
- `code/src/model_checker/theory_lib/bimodal/operators.py` (confirmed operator inventory)
- `code/src/model_checker/theory_lib/bimodal/docs/ADEQUACY.md` (never-report-validity rule,
  name-plus-manifest citation convention)
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_bimodal.py` (registry wiring,
  `KNOWN_TIMEOUT_EXAMPLES`/`UNSTABLE_EXAMPLES` both currently empty)
