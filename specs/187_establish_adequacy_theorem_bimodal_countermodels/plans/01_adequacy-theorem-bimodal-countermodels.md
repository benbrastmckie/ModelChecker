# Implementation Plan: Task #187

- **Task**: 187 - Establish an adequacy theorem connecting ModelChecker's bimodal countermodels to the paper's task semantics
- **Status**: [IMPLEMENTING]
- **Effort**: 9.5 hours
- **Dependencies**: None blocking. Layered over the certificate-redesign task (see "Relationship to the certificate redesign" below), which is `planned` but not started; this plan is written so that every phase lands green against the repository as it stands today.
- **Research Inputs**: specs/187_establish_adequacy_theorem_bimodal_countermodels/reports/01_adequacy-theorem-bimodal-countermodels.md
- **Artifacts**: plans/01_adequacy-theorem-bimodal-countermodels.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: formal:logic
- **Lean Intent**: false

## Overview

The research report settles the substance: (SOUND) is stated, proved in full, and every step of
the proof maps to a landed, sorry-free Lean theorem; (ADEQ) is recorded as open, reduced to four
named components with the deciding tests spelled out; and the relationship to the
certificate-redesign task is settled as option (a) — this is the adequacy layer, subsuming none
of that plan's phases. What is left is therefore not further proof work but **making the settled
result durable and mechanically load-bearing in this repository**, in the three places where it
can act today: a theory document carrying the statements and the proof, a certificate fixture
corpus that mechanically pins the proved re-check windows *before* any re-checker is written
against a wrong one, and a set of hard constraints routed into the redesign plan while that plan
is still `[NOT STARTED]`.

The plan deliberately does **not** attempt the refactor the task description contemplates. The
report's D-187-6 found that the refactor is the redesign task's own 24 phases, that this task
subsumes none of them, and that the adequacy layer's own implementation surface is narrow. Every
phase below is therefore executable against the repository in its current state, with no
dependence on code that does not yet exist.

### Research Integration

- The report's §2 (the two statements), §3 (four lemmas and the theorem, with the Lean citation
  table of §3.6 and the transcription audit of §3.7), §4 (both gaps closed), §7 (presentation and
  dual re-verification) and §8 ((ADEQ) status) are the content of Phases 1-2.
- The report's §4.1 defect finding — the proved collapse windows are `[-2*nb, nm + 2*nf)` for
  local coherence and fulfilment and `[-nb, nm + nf)` for box faithfulness, against a decision
  in the redesign plan that states one period each side — is the highest-value output and drives
  both Phase 3 (a fixture that mechanically discriminates the two windows) and Phase 5 (the plan
  amendment).
- The report's §6.3 expectation corrections and §6.4 translation bridge are recorded as
  constraints on the redesign plan (Phase 5), not implemented here: both require code that the
  redesign creates. The one exception is the false *claim* in the current test suite's exclusion
  comment, which is prose and is corrected in Phase 6.
- The report's §9.3 finding that `oracle/bimodal_logic/` is not an independent oracle removes
  oracle work from this task's scope entirely.

### Prior Plan Reference

No prior plan for this task. The certificate-redesign plan
(`specs/184_refactor_bimodal_theory_tests_green_and_paper_lean_aligned/plans/01_witness-family-certificate-redesign.md`)
was read as prior art: its decisions D1-D9, its 24 phases, and its wave structure are taken as
fixed, and Phase 5 below amends it rather than restating it. Effort calibration is taken from
that plan's 1.5-2 hour phase sizing, which this plan matches.

### Roadmap Alignment

No roadmap context was provided in the delegation context, so no roadmap consultation was
performed and no roadmap phases are included.

### Relationship to the certificate redesign

Settled in the report as **option (a)**: this task is the adequacy layer over the
witness-family certificate redesign, depends on it, and subsumes none of its phases. Concretely:

- Everything the theorem *requires of the implementation* (an unbounded time domain, a modal
  range that is the histories of a constructed frame, frame conditions discharged by construction,
  a certificate as the extraction output, a solver-independent re-checker) is that plan's work,
  not this one's.
- Everything the theorem *contributes* is either a durable statement of the result (Phases 1-2),
  a mechanical guard on a bound that plan currently gets wrong (Phases 3-4), or a constraint
  written into that plan (Phase 5).

## Goals & Non-Goals

**Goals**:
- A durable, in-repository statement of (SOUND) and (ADEQ) with the full proof of (SOUND), the
  Lean citation table, and the transcription audit, sited with the bimodal theory it governs.
- A certificate fixture corpus, independent of every ModelChecker bimodal module, that
  mechanically distinguishes the proved re-check windows from the narrower ones the redesign plan
  currently specifies, together with a differential against `lake exe check_certificate` where
  that binary is available.
- The redesign plan amended, while still `[NOT STARTED]`, with the corrected windows, the
  corrected state-sharing rationale, the three new tests, and the uncovered translation bridge.
- Removal of the one false claim about the paper's semantics that the current test suite asserts
  in prose.

**Non-Goals**:
- Refactoring the bimodal encoding. The report establishes that the obstruction is structural and
  that the replacement is the redesign task's 24 phases; duplicating any of them here is
  explicitly forbidden by D-187-6.
- Flipping `MF_MODAL_FUTURE_TH`'s `expectation`, or changing its membership in the exclusion set.
  Both are correct only after the encoding is replaced; doing either now turns the suite red for
  a reason the theorem does not endorse.
- Any work in `oracle/bimodal_logic/` beyond leaving the report's §9.3 finding recorded.
- Proving anything inside the Lean development, or re-deriving any result it already carries.
- Asserting (ADEQ), or any rendering of "no certificate found" as validity.
- Dense or continuous time, and the stability modal.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| The window-discriminating fixture (Phase 3) turns out not to be constructible as sketched, and the phase silently degrades into fixtures that do not discriminate | H | M | The phase carries an explicit construction sketch (the back-segment seam) *and* a Scope Hypothesis requiring the implementer to confirm mechanically that the violation is invisible in `[-nb, nm+nf)` and visible in `[-2*nb, nm+2*nf)`; if a fulfilment-side seam proves impossible, that finding is recorded with evidence rather than a non-discriminating fixture being shipped |
| `lake exe check_certificate` cannot be built within a sane time budget on this host, and Phase 4 stalls | M | M | Phase 4 is bounded: a hard timeout on the build probe, a clean skip with a named reason when it is not available, and fixture expectations that stand on Phase 3's own decoder; the phase never blocks on the Lean toolchain |
| The plan amendment (Phase 5) edits another task's plan and diverges from it mid-flight | M | L | That plan is `[NOT STARTED]`; the amendment is made as an explicit, sourced amendment block plus in-place decision edits, touching no phase status marker |
| The theory document accumulates task-number references and trips the deliverable lint | M | M | `docs/` is outside `specs/**`; Phase 1 and Phase 2 cite only paper line anchors, Lean names with file:line, and repository paths, and Phase 6 runs the task-reference lint as a gate |
| The correction to the exclusion comment is read as a behavioral change and perturbs the suite | M | L | Phase 6 changes comment text only, with the set membership, the settings and the expectation untouched, and runs the bimodal suite to confirm the collected-test set is unchanged |
| (ADEQ) is recorded in the document in a way a later reader mistakes for a result | M | L | Phase 2 states it as a conditional with an explicit status table (A0-A3), reproduces the negative finding on the one candidate reduction, and states the never-report-validity rule with both of its independent grounds |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 3 | -- |
| 2 | 2, 4 | 1 (for 2), 3 (for 4) |
| 3 | 5 | 2 |
| 4 | 6 | 2, 4, 5 |

Phases within the same wave can execute in parallel. Phases 1/2 and 3/4 are two independent
tracks (document, corpus) that converge at Phase 6.

---

### Phase 1: State (SOUND) and its proof in a durable theory document [COMPLETED]

**Goal**: `code/src/model_checker/theory_lib/bimodal/docs/ADEQUACY.md` exists and carries the
soundness half in full: the certificate definition, the statement, the construction, four lemmas
with proofs, the theorem, and the mapping of every step to its landed Lean counterpart.

**Tasks**:
- [x] Create `ADEQUACY.md` with a scope preamble: what the document claims, what it does not
      (it is not a validity claim and not a claim about the current encoding), and that it is
      stated for discrete time only. *(completed)*
- [x] Write the certificate definition: the pair `(bx, <L_0, ..., L_k>)` with a target time, the
      three-segment decoding, and conditions (C1) local coherence, (C2) fulfilment, (C3) box
      faithfulness, (C4) target — including the remark that atoms are deliberately unconstrained. *(completed)*
- [x] State (SOUND) verbatim from the report's §2, with its four obligations S1-S4 and each
      obligation's status, and state the architectural point: the antecedent is decided on every
      reported countermodel rather than the encoder being proved correct. *(completed)*
- [x] Write the construction (`D := <Z,+,0,<=>`, `W := {0..k} x Z`, the shift relation, the
      valuation, the lassos) and the reflection-convention check. *(completed)*
- [x] Write Lemma 1 (Frame) with all four constraints proved, Lemma 2 (Histories) with
      Corollaries 2.1 (translation closure, derived) and 2.2 (Box's range), Lemma 3 (time-shift
      preservation, instantiated) with Corollary 3.1, and Lemma 4 (truth lemma) with every case. *(completed)*
- [x] Write the remark on why both (C1) and (C2) are needed and where discreteness enters, and
      the theorem with its proof and the non-vacuity corollary. *(completed)*
- [x] Add the Lean citation table of the report's §3.6 (this report's step -> Lean name ->
      file:line) and the `IntNormalForm.ofStep` near-miss note recording why it is *not* the
      mechanization of Lemma 1. *(completed)*
- [x] Add the transcription audit table of the report's §3.7 (paper anchor -> Lean definition ->
      verdict), labelled as an audit discharged by inspection, not as a theorem. *(completed)*
- [x] Use only durable anchors: paper line numbers, Lean names with file:line, repository paths.
      No task numbers, and no `specs/` paths (this file is outside `specs/**`). *(completed)*

**Timing**: 2 hours

**Depends on**: none

**Verification Tier**: prose

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/docs/ADEQUACY.md` - new file

**Verification**:
- The file exists and contains the statement of (SOUND), four lemma headings, the theorem, the
  Lean citation table and the audit table.
- Every Lean name in the citation table resolves: for each row, `grep -rn "<name>"
  ~/Projects/BimodalLogic/FormalSystem/` returns the cited file, and the cited line is within a
  few lines of the definition. Any row that does not resolve is corrected against the source, not
  dropped.
- `grep -nE "task [0-9]+|specs/" code/src/model_checker/theory_lib/bimodal/docs/ADEQUACY.md`
  returns nothing.

---

### Phase 2: State (ADEQ), the proved windows, the re-check protocol and the scope rationale [COMPLETED]

**Goal**: `ADEQUACY.md` is complete: the re-check windows and their proofs, the two gaps as
closed, the presentation-and-re-verification protocol, (ADEQ) with its status table and deciding
tests, and the recorded reasons for discrete time only.

**Tasks**:
- [x] Add the periodicity section: the two decoding periodicities, the four collapse results with
      their Lean names and file:line, and the window table — `[-2*nb, nm + 2*nf)` for local
      coherence and for fulfilment, `[-nb, nm + nf)` for box faithfulness, and the two witness
      scan bounds — with the reason two periods are required (the clause at `t` reads `t-1` and
      `t+1`, so a representative position needs its whole neighbourhood inside the periodic
      region). *(completed)*
- [x] Add the second half of the periodicity obligation as a differential obligation, not a
      proof: the Python re-checker's verdict must agree with `lake exe check_certificate` over a
      corpus that includes a coherent-but-unfulfilling family, a family failing only outside the
      one-period window, and a family failing box faithfulness only. *(completed)*
- [x] Add the determinism section: Limit is genuinely non-free (separation is not derivable from
      the action laws), Saturation follows from subsingleton fibres, and — the correction — the
      real blocker to lasso state-sharing is that determinism is what makes the histories exactly
      the orbits, hence what makes the Box case of the truth lemma go through. *(completed)*
- [x] Add the presentation and re-verification section: the wire contract (required `target` with
      a required `time`, sparse `bx`, `lassos[0]` the main lasso, the formula tag vocabulary,
      base-only atom identity), the output vocabulary including that it is never a validity claim,
      and the four-step dual verification with its fail-fast rule. *(completed)*
- [x] State (ADEQ) as a conditional, at frame class discrete-time only, with the A0-A3 status
      table: A0 the permanent frame-class gap with the two named axioms and their citations, A1
      open with the compression route and the literature citation, A2 provable and testable now,
      A3 vacuous until A1 supplies a bound. *(completed)*
- [x] Record the examined-and-rejected reduction: the presentation-relative bounded-completeness
      theorem is the template for A1, not a reduction of it, with the three blocking facts and
      the three conditions under which a genuine reduction would go through. *(completed)*
- [x] Record the deciding tests by name: the A2 three-way differential at the smallest lengths,
      and the A0 standing test that the two discrete-time-only axioms must render inconclusive. *(completed)*
- [x] Add the discrete-time-only section with all three recorded reasons, the sharpest being the
      finite descent in the truth lemma's until case. *(completed)*
- [x] State the never-report-validity rule with both of its independent grounds (search
      one-sidedness, and the frame-class gap). *(completed)*

**Timing**: 2 hours

**Depends on**: 1

**Verification Tier**: prose

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/docs/ADEQUACY.md` - extend

**Verification**:
- The document states (ADEQ) with an explicit status table in which no row reads as proved, and
  the words asserting validity appear nowhere except in the prohibition.
- The window table gives two distinct windows and names the coherence/fulfilment one as
  `[-2*nb, nm + 2*nf)`.
- Lean names cited in this phase resolve the same way as in Phase 1.
- `grep -nE "task [0-9]+|specs/"` over the file still returns nothing.

---

### Phase 3: Certificate fixture corpus with a self-contained window evaluator [NOT STARTED]

**Goal**: A JSON fixture corpus in the wire format, plus a test module that decodes and evaluates
the four conditions over an explicit window parameter, mechanically demonstrating that the proved
window catches a violation the one-period window misses.

**Tasks**:
- [ ] Create `code/src/model_checker/theory_lib/bimodal/tests/fixtures/certificates/` and write a
      `README.md` there stating the wire contract, that the corpus is checker-independent, and
      that expected verdicts are adjudicated by the Lean binary where available.
- [ ] Write a positive fixture: a family that satisfies (C1)-(C4), expected verdict
      `countermodel`.
- [ ] Write a coherent-but-not-fulfilling fixture (infinite postponement): an eventuality carried
      forward at every position with its event never labelled. Expected verdict `rejected` with
      condition `fulfilling`.
- [ ] Write a box-faithfulness-only fixture: (C1), (C2) and (C4) hold, `bx` disagrees with actual
      labelling at some position. Expected verdict `rejected` with condition `box_faithful`.
- [ ] Write the window-discriminating fixture(s): a violation sited in the outer band
      `[-2*nb, -nb)` that no position in `[-nb, nm + nf)` exhibits. Construction sketch: the
      forward region is genuinely one-period-representative (for `t >= nm`, the label triple at
      `t` recurs at `t - nf`), but the back region is not, because a position just left of the
      first repeated back period has the mid segment to its right while its periodic image does
      not — the seam between the repeated `back` period and `mid` is where the neighbourhoods
      differ. Build the violation at that seam, once for local coherence and once for fulfilment.
- [ ] Write `expected_verdicts.json` mapping each fixture filename to its expected status,
      condition, and (where determinate) lasso and position.
- [ ] Write `code/src/model_checker/theory_lib/bimodal/tests/unit/test_certificate_fixtures.py`
      containing a self-contained decoder (three-segment unroll to a total label function over the
      integers) and direct evaluators for (C1)-(C4) parameterised by a half-open window. The
      module MUST NOT import from `model_checker.theory_lib.bimodal.semantic` — its independence
      from the theory under test is the point.
- [ ] Assert, per fixture, that evaluation over `[-2*nb, nm + 2*nf)` yields the expected verdict;
      and for the discriminating fixture(s), that evaluation over `[-nb, nm + nf)` yields
      *no* violation while evaluation over `[-2*nb, nm + 2*nf)` yields one, with the offending
      position reported and asserted to lie in the outer band.
- [ ] Add a test asserting every fixture parses as the wire format: `target` present with `time`
      present, formula tags drawn from the six-tag vocabulary, every label a list of formulas,
      `back` and `fwd` non-empty, no atom carrying a fresh index.

**Timing**: 2 hours

**Depends on**: none

**Verification Tier**: local

**Scope Hypothesis**: the discriminating fixture is constructible at the back seam, at some
position in `[-2*nb, -nb)`, for both local coherence and fulfilment, at small segment lengths
(`nb, nm, nf <= 3`) over a closure of at most four formulas. Confirm mechanically rather than by
argument: the implementation must print the offending position and assert both its membership in
the outer band and the absence of any violation inside `[-nb, nm + nf)`. If the fulfilment-side
seam proves impossible (fulfilment violations may be genuinely period-invariant, in which case
only the coherence-side seam discriminates), record that finding in the fixture `README.md` with
the evidence and ship the coherence-side fixture alone — do not ship a fixture that fails to
discriminate.

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/tests/fixtures/certificates/README.md` - new
- `code/src/model_checker/theory_lib/bimodal/tests/fixtures/certificates/*.json` - new fixtures
  plus `expected_verdicts.json`
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_certificate_fixtures.py` - new

**Verification**:
- `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/unit/test_certificate_fixtures.py -v`
  is green.
- The discriminating assertion is genuinely two-sided: the test fails if the window parameter is
  changed to the one-period bound (confirm by temporarily changing it and observing the failure).
- `grep -rn "from model_checker" code/src/model_checker/theory_lib/bimodal/tests/unit/test_certificate_fixtures.py`
  shows no import of the bimodal semantic package.

---

### Phase 4: Differential the corpus against the Lean certificate checker [NOT STARTED]

**Goal**: Where BimodalLogic and `lake` are present, every fixture's expected verdict is
adjudicated by `lake exe check_certificate`; where they are not, the test skips cleanly with a
named reason.

**Tasks**:
- [ ] Write
      `code/src/model_checker/theory_lib/bimodal/tests/integration/test_certificate_lean_agreement.py`:
      resolve the BimodalLogic checkout (environment variable first, then `~/Projects/BimodalLogic`),
      resolve `lake`, and skip with an explicit reason when either is missing.
- [ ] Probe the binary once, under a hard timeout, before the fixture loop; on timeout or build
      failure, skip the whole module with the recorded reason rather than failing.
- [ ] For each fixture, pipe its JSON to `lake exe check_certificate` on stdin, parse the single
      output line, and assert agreement with `expected_verdicts.json` on `status` and, where
      recorded, on `condition`.
- [ ] Assert the two error-path rows: a certificate with `target` removed and one with
      `target.time` removed both produce `error`, never `rejected`.
- [ ] Record the BimodalLogic commit the agreement was observed against in the module docstring.
- [ ] If the binary adjudicates any fixture differently from Phase 3's evaluator, treat the
      fixture or the evaluator as the defect — the Lean predicates are the contract — and fix the
      repository side, recording what was wrong.

**Timing**: 1 hour

**Depends on**: 3

**Verification Tier**: local

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/tests/integration/test_certificate_lean_agreement.py` - new

**Verification**:
- `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/integration/test_certificate_lean_agreement.py -v`
  is either green with the commit recorded, or cleanly skipped with a reason naming what was
  missing — never errored, and never hanging.
- The module's timeout bound is explicit in the source, not implicit in the harness.

---

### Phase 5: Amend the certificate-redesign plan with the theorem's hard constraints [NOT STARTED]

**Goal**: The redesign plan carries the corrected windows, the corrected state-sharing rationale,
and the new obligations, while it is still `[NOT STARTED]` and before the phases written against
the wrong bound are dispatched.

**Tasks**:
- [ ] Rewrite decision D7 in
      `specs/184_refactor_bimodal_theory_tests_green_and_paper_lean_aligned/plans/01_witness-family-certificate-redesign.md`:
      the proved collapse window for local coherence and for fulfilment is `[-2*nb, nm + 2*nf)`,
      the window for box faithfulness is the narrower `[-nb, nm + nf)`, the two are **not** the
      same window, and the reason two periods are needed is that the clause at `t` reads `t-1`
      and `t+1`. Cite the Lean collapse lemmas by name and file:line. Keep D7's own warning that
      a wrong bound is the most likely silent soundness bug, now discharged rather than pending.
- [ ] Correct D9's rationale: the blocker to lasso state-sharing is that determinism makes the
      world histories exactly the orbits, hence makes the Box case of the truth lemma go through
      — not Limit and Saturation. The decision itself (design for sharing, do not implement it)
      stands.
- [ ] Add an amendment block immediately after the decisions section recording the source of
      these amendments (this task's report path, which is inside `specs/**` and may be cited
      there), the date, and a one-line index of every phase touched below.
- [ ] Phase 2 (translation): add the truth-preservation obligation — the round-trip against the
      Lean binary cannot test the sentence-to-formula translation, because both sides consume the
      already-translated formula. Add a property test comparing the theory's own truth evaluation
      against a direct evaluator for the translated formula at every point of a small hand-built
      discrete-time model, and note that the existing brute-force adjudicator covers the tense
      half only, having no box case.
- [ ] Phase 3 (datatypes): add the forward-compatibility note's corrected rationale, matching D9.
- [ ] Phase 4 (re-checker): replace the window reference with the corrected one; add the
      window-discriminating fixture as an acceptance criterion, pointing at the fixture corpus
      this task creates as the source of the fixture.
- [ ] Phase 5 (round-trip): add the three-way differential (re-checker, Lean binary, and whether
      the encoding reports SAT) at the smallest segment lengths over a closure of at most four
      formulas, with its three named failure localizations; and add this task's fixture corpus to
      the round-trip's fixture set.
- [ ] Phase 8 (fulfilment and box-faithfulness generators): replace the window reference with the
      corrected one, and record that box faithfulness uses the narrower window while fulfilment
      does not.
- [ ] Phases 9, 12 and 16: add the frame-class standing test — the two discrete-time-only axiom
      instances must report no certificate at every configured length and must render
      inconclusive, never as validity; a rendering that says valid on either is a reportable
      defect.
- [ ] Phase 12 (re-check hook): recast the hook's role — it is not a safety net but the mechanism
      discharging the soundness obligation that whatever the search reports satisfies the
      certificate conditions.
- [ ] Phase 16/17 (examples): record that the source of truth for the modal-future axiom's
      expectation is the two Lean theorems (its validity at the unrestricted frame class, and
      that no certificate at any lengths refutes it), and that the current exclusion comment is
      to be deleted rather than softened.
- [ ] Phase 22 (documentation): add a task to carry the theorem statement, the four lemmas and
      the Lean citation table into the theory documentation, noting that the adequacy document
      this task creates is the source.
- [ ] Touch no phase status marker and no plan-level status field.

**Timing**: 1.5 hours

**Depends on**: 2

**Verification Tier**: prose

**Scope Hypothesis**: exactly nine phases of the redesign plan are touched (2, 3, 4, 5, 8, 9, 12,
16, 22, with 17 folded into the 16 edit) plus decisions D7 and D9. Confirm at implementation time
by diffing the plan and listing the touched headings; if a phase's text turns out not to reference
the window at all, record that and leave it untouched rather than inventing an edit.

**Files to modify**:
- `specs/184_refactor_bimodal_theory_tests_green_and_paper_lean_aligned/plans/01_witness-family-certificate-redesign.md` - amend

**Verification**:
- `bash .claude/scripts/validate-artifact.sh specs/184_refactor_bimodal_theory_tests_green_and_paper_lean_aligned/plans/01_witness-family-certificate-redesign.md`
  passes.
- `grep -n "2\*nb\|2 \* nb\|2·nb" <plan>` finds the corrected window in D7, in Phase 4 and in
  Phase 8.
- `grep -c "^### Phase" <plan>` still returns 24, and
  `grep -c "\[NOT STARTED\]" <plan>` is unchanged from before the edit.

---

### Phase 6: Wire the document in, correct the false exclusion claim, and verify [NOT STARTED]

**Goal**: The adequacy document is reachable from the theory's documentation index, the one false
claim about the paper's semantics in the test suite is corrected in prose, and the whole bimodal
suite plus the new tests are green.

**Tasks**:
- [ ] Add `ADEQUACY.md` to `code/src/model_checker/theory_lib/bimodal/docs/README.md`'s
      navigation, with a one-line description naming what it states and what it does not claim.
- [ ] Add a pointer from `code/src/model_checker/theory_lib/bimodal/README.md` to the adequacy
      document.
- [ ] Correct the exclusion comment in
      `code/src/model_checker/theory_lib/bimodal/tests/unit/test_bimodal.py`: the claim that the
      modal-future axiom "is NOT a theorem under current bimodal semantics" is false with respect
      to the paper's semantics. Replace it with a statement that the axiom is valid in the paper's
      semantics (citing the Lean theorem by name), that the reported countermodel is an artifact
      of the bounded-window encoding's boundary vacuity, and that the exclusion stands only until
      the encoding is replaced. Correct the trailing inline comment on the exclusion-set entry the
      same way.
- [ ] Change nothing else in that file: the exclusion-set membership, the settings and the
      expectation stay exactly as they are.
- [ ] Run the full bimodal test suite and confirm the collected-test set and outcomes are
      unchanged apart from the two new modules.
- [ ] Run the task-reference lint over the repository and confirm the new documentation and tests
      introduce no task-number reference outside `specs/**`.

**Timing**: 1 hour

**Depends on**: 2, 4, 5

**Verification Tier**: local

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/docs/README.md` - add navigation entry
- `code/src/model_checker/theory_lib/bimodal/README.md` - add pointer
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_bimodal.py` - comment text only

**Verification**:
- `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/ -q` collects the
  same example-driven tests as before the change (compare collected counts against a pre-edit
  run) and is green or skipped, with no new failures.
- `git diff code/src/model_checker/theory_lib/bimodal/tests/unit/test_bimodal.py` shows changes
  confined to comment lines.
- `bash .claude/scripts/check-task-references.sh` reports no new violations.
- Every relative link added to the two README files resolves to an existing file.

## Testing & Validation

- [ ] The fixture corpus is green under the self-contained evaluator, and the discriminating
      assertion demonstrably fails when the window is narrowed to one period.
- [ ] The Lean differential is green with a recorded commit, or cleanly skipped with a named
      reason.
- [ ] The full bimodal suite is unchanged apart from the two new modules.
- [ ] The amended redesign plan validates and retains all 24 phases at their original statuses.
- [ ] Every Lean name cited in the adequacy document resolves in the Lean development.
- [ ] No task-number reference is introduced outside `specs/**`.

## Artifacts & Outputs

- `code/src/model_checker/theory_lib/bimodal/docs/ADEQUACY.md` — the statements, the proof of the
  soundness direction, the Lean citation table, the transcription audit, the re-check windows and
  protocol, and the open status of the adequacy direction.
- `code/src/model_checker/theory_lib/bimodal/tests/fixtures/certificates/` — the checker-independent
  fixture corpus with expected verdicts and its README.
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_certificate_fixtures.py` and
  `.../tests/integration/test_certificate_lean_agreement.py` — the two new test modules.
- An amended certificate-redesign plan carrying the corrected windows and the new obligations.
- Corrected documentation navigation and a corrected exclusion comment.

## Rollback/Contingency

Every phase is additive apart from Phase 5's plan amendment and Phase 6's comment correction, so
rollback is per-file `git revert` of the phase's commit with no cross-phase coupling.

- If Phase 3's discriminating fixture cannot be built at either seam, the corpus still ships its
  three non-discriminating fixtures, the finding is recorded in the fixture README and in the
  adequacy document's periodicity section, and Phase 5's D7 amendment proceeds regardless — the
  window correction rests on the Lean collapse lemmas, not on the fixture.
- If Phase 4's binary is unavailable, the corpus's expected verdicts remain those computed by
  Phase 3's evaluator and the document records that the differential is pending; nothing
  downstream blocks.
- If Phase 5's amendment conflicts with a concurrent edit to the redesign plan, re-apply the
  amendment against the current file rather than overwriting it, and record the conflict.
