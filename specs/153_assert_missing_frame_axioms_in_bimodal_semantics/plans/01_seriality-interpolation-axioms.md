# Implementation Plan: Assert Seriality and Interpolation in BimodalSemantics

- **Task**: 153 - Assert missing frame axioms in bimodal semantics
- **Status**: [IMPLEMENTING]
- **Effort**: 9 hours
- **Dependencies**: 152 (audit ledger + regression baseline)
- **Research Inputs**: `specs/153_assert_missing_frame_axioms_in_bimodal_semantics/reports/01_seriality-interpolation-encoding.md`
- **Artifacts**: plans/01_seriality-interpolation-axioms.md (this file)
- **Standards**: plan-format.md; status-markers.md; artifact-management.md; tasks.md
- **Type**: z3
- **Lean Intent**: false

## Overview

Bring `BimodalSemantics`'s frame class up to the JPL paper's `def:frame` by asserting the two
axioms that are not already free — *Seriality* and *Interpolation* (the missing right-to-left half
of *Compositionality*) — using the Skolemized encodings the research report validated empirically,
then record the resulting frame-class ledger in `ARCHITECTURE.md` and correct the now-stale
three-axiom docstring in `build_frame_constraints`. *Limit* and *Spherical* need no Z3 assertion:
both were re-verified free at the sort level (`WorldStateSort = BitVecSort(N)` is finite;
`build_nullity_identity_constraint` is unguarded). Definition of done: both constraints asserted
and unit-tested, the full 52-example regression baseline re-run with every verdict flip explained
individually, the full bimodal suite green, and Deliverables 3 and 4 written into
`ARCHITECTURE.md`.

### Research Integration

The report at `reports/01_seriality-interpolation-encoding.md` supplies four findings this plan
builds on directly:

1. **Encoding is settled by measurement, not preference.** A literal nested `ForAll`/`Exists`
   reading of Interpolation regresses `BM_TH_3` and `BM_TH_4` (both at M=2) from a decided
   0.03-0.10s `match` to a 10s MBQI timeout (`inconclusive`). The Skolemized reading preserves
   baseline verdict and timing on all six prototype examples (0.15s / 0.23s). Phase 4 therefore
   mandates the Skolemized form; the nested form is ruled out by data, and re-introducing it would
   be a regression against this task's own verification bar.
2. **Both encodings have in-tree precedent.** `capped_skolem_abundance_constraint` (`core.py:1447`)
   and `depth_bounded_skolem_abundance_constraint` (`core.py:1530`) already eliminate an
   existential with a Skolem function inside one top-level `ForAll`. Seriality and Interpolation
   are structurally identical, so this introduces no novel technique.
3. **Ready-to-transcribe table.** Report Section 4.2 supplies the frame-class table content with
   per-row citations; Section 5 supplies the duration-domain footnote text for Deliverable 4;
   Section 4.3 identifies `ARCHITECTURE.md`'s surrounding sections as illustrative pseudocode that
   does not match `core.py`'s real method names, so the new subsection must be written as factual
   reference rather than matching its neighbours' style.
4. **Test shape already exists.** `test_frame_constraints.py` (`TestNullityIdentity`/`TestConverse`/
   `TestForwardComp`) and `test_frame_class_mapping.py` (`TestConversePostHoc`/
   `TestForwardCompPostHoc`) establish the exact per-axiom solver-level and post-hoc-extraction test
   patterns the new axioms' tests mirror.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

`specs/ROADMAP.md` was not supplied in the delegation context and contains no item matching this
task's frame-class work (its bimodal entries concern packaging, CI path filters, and missing
notebooks). No roadmap phases are included and ROADMAP.md is not modified by this plan.

## Goals & Non-Goals

**Goals**:

- Assert Seriality via a new `build_seriality_constraint`, Skolemized over two witness functions
  (`serial_succ`, `serial_pred`), guarded by `x >= 0` and `is_valid_duration(x)`.
- Assert Interpolation via a new `build_interpolation_constraint`, Skolemized over one witness
  function, guarded by the same `is_valid_duration(d1)`/`(d2)`/`(d1 + d2)` triple
  `build_forward_comp_constraint` already uses.
- Wire both into `build_frame_constraints`'s returned list alongside items 7-9, preserving the
  documented constraint ordering rationale (frame axioms before abundance).
- Unit-test both at the solver level (`test_frame_constraints.py`) and post-hoc against extracted
  countermodels (`test_frame_class_mapping.py`), following the existing per-axiom patterns.
- Correct `build_frame_constraints`'s "TaskFrame Axioms (items 7-9)" docstring so exactly one
  account of the frame class exists in `core.py`.
- Add a `### Frame-Class Axioms` subsection to `ARCHITECTURE.md` carrying the asserted/free ledger
  with citations (Deliverable 3) and the duration-domain-guard footnote (Deliverable 4).
- Re-run the full 52-example regression baseline and explain every verdict flip individually.

**Non-Goals**:

- **The definitional-reachability redefinition of `task_rel` is measured but not implemented in
  this task.** See the scope call below — Phase 2 produces the measurement the task's own text
  demands ("record the measurement so the question is not reopened blind"); the redesign itself,
  if the measurement favours it, is spawned as a separate task rather than expanded into this one.
- Re-enabling or re-adjudicating the disabled `task_restriction` constraint. Report Section 7
  confirms the new axioms do not subsume it; it remains an independent gap.
- Fixing `oracle/bimodal_logic/provider.py`'s frame-axiom docstring table, which is outside
  `file_scope` and will go stale when `core.py`'s docstring changes. Flagged in Phase 7, not fixed.
- Resolving the duration-domain gap (bounded window `(-M, M)` vs. the paper's unbounded group
  `\Z`). Deliverable 4 asks for it to be **recorded**, not resolved.
- Fixing the pervasive `truth_value_at() missing 'eval_time'` interpretation error present on every
  recorded baseline run. It does not affect any verdict (verdicts read from `z3_model_status`) and
  is out of the audit's scope by its own README.

### Scope call: the definitional-reachability alternative

The task text asks that redefining `task_rel(w, d, v)` as `d`-step reachability of a unit relation
`R` be evaluated first, and calls it "strongly preferred if it measures acceptably". Research
evaluated it qualitatively only and did not benchmark it. This plan takes an explicit position
rather than silently dropping or silently assuming it:

- **Phase 2 measures it**, time-boxed, against the same six-example prototype harness the report
  used, in the backend-neutral unrolled-disjunction form (Z3's `TransitiveClosure` is ruled out
  independently: it has no precedent anywhere in `code/src/model_checker/`, it answers reachability
  rather than reachability-in-exactly-`d`-steps so it cannot carry a duration-indexed relation, and
  it is a Z3-specific API family that `z3_shim.py`'s `z3`/`cvc5.pythonic` migration would have to
  work around).
- **A "go" measurement does not expand this task.** The redefinition changes what
  `build_frame_constraints` items 7-9 *are* — `nullity_identity`, `converse`, and `forward_comp`
  become derived theorems rather than assertions, with their existing tests needing re-derivation —
  which is a materially larger surface than the additive change this task's deliverables describe.
  If Phase 2 measures favourably, the implementer records the numbers, notes the recommendation in
  the summary, and the redesign is raised as a follow-on task.
- **Rationale for this call**: the Skolemized direct fix already clears the task's own stated bar
  (zero measured regressions on all six prototype examples), so the redefinition's payoff is
  soundness elegance rather than a blocked deliverable; and the task's fallback instruction is
  explicitly conditional. If the user prefers the redefinition be carried into this task rather
  than spawned, that is a scope decision for them to make on seeing Phase 2's numbers.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Nested `ForAll`/`Exists` encoding reintroduced by an implementer reading the task text literally | H | M | Phase 4 mandates the Skolemized form and cites the measured `BM_TH_3`/`BM_TH_4` regression; Phase 3's tests are written against the Skolemized builders by name |
| The two new axioms make `frame_constraints` jointly UNSAT, silently turning every example into a vacuous "no countermodel" | H | L | Phase 3 includes an explicit joint-satisfiability test before any per-axiom test; the existing `test_all_constraints_consistent` is a second net; Phase 7's 52-example diff would show a mass flip |
| Full 52-example run wall time and host flakiness (`BM_CM_1`'s documented heavy tail, median ~7-8s with draws to 47.78s) misread as a regression | M | M | Baseline README's caveats are authoritative; treat `BM_CM_1` timing as a recorded data point, never a re-adjudication of its `unstable` marker |
| `BM_TH_1`/`BM_TH_2` are `inconclusive-at-90s` in the recorded baseline, so they can neither confirm nor deny a regression | M | H | Phase 7 states this explicitly per the report's Section 3.3; an unchanged timeout there is reported as "no signal", never as "no regression" |
| Phase 2's time-box overruns and the prototype becomes an open-ended redesign | M | M | Hard 1.5h box with pre-stated go/no-go criteria; expiry is itself a recorded no-go outcome, and Phases 3-7 are written against the validated fallback so nothing downstream blocks on it |
| The task's "four ASSERTED axioms" table-row language matches no consistent reading (see Phase 6) | M | H | Phase 6 resolves it explicitly to a 7-row table (5 asserted, 2 free) with a note stating why, rather than forcing a count that misrepresents the content |
| `oracle/bimodal_logic/provider.py` silently diverges once `core.py`'s docstring changes | M | H | Flagged in Phase 7 and in the implementation summary as an out-of-`file_scope` follow-up |

## Implementation Phases

**Dependency Analysis**:

| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4 | 3 |
| 5 | 5, 6 | 4 |
| 6 | 7 | 5, 6 |

Phases within the same wave can execute in parallel.

---

### Phase 1: Regression harness and pre-change reference run [COMPLETED]

**Goal**: Stand up a re-runnable 52-example harness under this task's own `baselines/` directory
and capture a pre-change reference run on this host, so Phase 7's post-change diff has both the
recorded 152 baseline and a same-host "before" to compare against.

**Tasks**:

- [ ] Create `specs/153_assert_missing_frame_axioms_in_bimodal_semantics/baselines/` and copy
      `specs/152_audit_bimodal_frame_class_and_verdict_dependence/baselines/01_abundance-removal-script.py`
      into it as `01_frame-axiom-regression-script.py`.
- [ ] Adapt the copy so its two arms are **baseline (unmodified `build_frame_constraints`)** and
      **with-new-axioms (process-local monkeypatched constraint list)** rather than the original's
      baseline/no-abundance arms. Keep the incremental-write behaviour and the per-example
      transcript line.
- [ ] Preserve the harness invariants the 152 README documents: in-process via
      `model_checker.utils.testing.run_enhanced_test`, `isolated_z3_context()` per run, each
      example's own `examples.py` settings, and **`core.py` on disk is never edited by the script**.
- [ ] Run the baseline arm only against the current unmodified tree; write
      `01_pre-change-verdicts.json`.
- [ ] Diff `01_pre-change-verdicts.json` against
      `specs/152_.../baselines/01_abundance-removal-verdicts.json`'s `baseline` side and record any
      host-level divergence in a short `README.md` in this task's `baselines/` directory.

**Timing**: 1 hour (dominated by the ~105s run plus the `BM_TH_1`/`BM_TH_2` 30s-each timeouts).

**Depends on**: none

**Verification Tier**: local

**Scope Hypothesis**: This phase assumes the harness covers **52 examples** (`countermodel_examples
∪ theorem_examples`, aliased `test_example_range`) and that the abundance-dependent surface is
exactly the **4 cells** `BM_TH_1`-`BM_TH_4`. Confirm at implementation time by reading the example
count the script actually enumerates and the key count in the produced JSON; if either differs from
the 152 README's figures, record the actual number and investigate before proceeding.

**Files to modify**:

- `specs/153_assert_missing_frame_axioms_in_bimodal_semantics/baselines/01_frame-axiom-regression-script.py` - new, adapted harness
- `specs/153_assert_missing_frame_axioms_in_bimodal_semantics/baselines/01_pre-change-verdicts.json` - new, pre-change reference
- `specs/153_assert_missing_frame_axioms_in_bimodal_semantics/baselines/README.md` - new, invocation and divergence notes

**Verification**:

- The script runs to completion from the repo root with `PYTHONPATH=code/src` and produces a JSON
  with one entry per enumerated example.
- `git status` confirms no modification to `code/src/model_checker/theory_lib/bimodal/semantic/core.py`.
- The pre-change verdicts for `BM_TH_3`/`BM_TH_4` are `match`, matching the 152 recorded baseline.

---

### Phase 2: Time-boxed measurement of the definitional-reachability alternative [COMPLETED]

**Goal**: Produce the honest before/after measurement the task's Deliverable 2 demands for the
"define `task_rel` as bounded reachability of a unit relation `R`" alternative, so the question is
closed with data rather than reopened blind. This is a decision gate, not a redesign.

**Tasks**:

- [ ] Write a process-local prototype (scratchpad or this task's `baselines/`, never editing
      `core.py`) that replaces `task_rel(w, d, v)` at its call sites with a Python-level macro
      expanding to the finite disjunction over unrolled `d`-length compositions of a free binary
      relation `R`, for each concrete `d` in the bounded window `(-M, M)` — `2M-1` cases. Do **not**
      use `z3.TransitiveClosure` (no in-tree precedent; wrong shape for a duration-indexed relation;
      Z3-specific against `z3_shim.py`'s `cvc5.pythonic` migration).
- [ ] Run it against the same six-example prototype subset the report used (`BM_TH_1`-`BM_TH_4`,
      `EX_CM_1`, `EX_TH_1`) with each example's own settings.
- [ ] Record verdict and wall time per example beside the report's Section 3.2 table (baseline and
      Skolemized columns) in `baselines/02_reachability-prototype-measurement.md`.
- [ ] Apply the go/no-go criteria and record the outcome with its reason:
      **go** requires all three of (a) `BM_TH_3` and `BM_TH_4` still decided `match`, (b) their wall
      times within roughly the same order as the Skolemized encoding's 0.15s/0.23s, (c) the
      encoding expressible without any Z3-specific API. **No-go** if any criterion fails, or if the
      1.5h box expires — an expired box is a recorded no-go, not a silent skip.
- [ ] On a **no-go** (the expected outcome), proceed to Phase 3 against the Skolemized encoding.
      On a **go**, still proceed to Phase 3 against the Skolemized encoding, and record in the
      measurement file and the eventual summary that a follow-on task should carry the redefinition
      — per this plan's scope call, a favourable measurement does not expand this task mid-flight.

**Timing**: 1.5 hours (hard time-box).

**Depends on**: 1

**Verification Tier**: local

**Scope Hypothesis**: This phase assumes the unrolled-disjunction form needs **`2M-1` concrete
duration cases** and that the six-example subset is a sufficient decision surface (it is the same
subset the report's Section 3.2 numbers come from, so the comparison is apples-to-apples). Confirm
the case count against `is_valid_duration`'s actual bounds at implementation time; if the prototype
cannot be expressed at all in this form, that is itself a recorded no-go with reason.

**Files to modify**:

- `specs/153_assert_missing_frame_axioms_in_bimodal_semantics/baselines/02_reachability-prototype-measurement.md` - new, the recorded measurement and go/no-go decision

**Verification**:

- The measurement file contains a per-example row for all six examples with verdict and wall time,
  or an explicit statement of which examples could not be run and why.
- The go/no-go outcome is stated in one sentence with its governing criterion named.
- `git status` confirms `core.py` is unmodified.

---

### Phase 3: Failing tests for Seriality and Interpolation (RED) [COMPLETED]

**Goal**: Write the tests before the implementation, per the project's mandatory TDD requirement.
All new tests fail at the end of this phase because the constraint builders do not yet exist.

**Tasks**:

- [ ] Add a joint-satisfiability test asserting `semantics.frame_constraints` is `sat` with the new
      axioms present — this must be the first new test, since a jointly-UNSAT frame would make every
      other test pass vacuously.
- [ ] Add `TestSeriality` to `test_frame_constraints.py`, mirroring the `TestConverse` shape:
      a positive case (a successor and a predecessor exist for a concrete `w` at a valid non-negative
      duration, satisfiable) and a negative case (asserting no successor exists for some `(w, x)`
      inside the guard is unsatisfiable).
- [ ] Add `TestInterpolation` to `test_frame_constraints.py`, mirroring `TestForwardComp`:
      given `task_rel(w, d1 + d2, v)` under the duration guards, asserting that no intermediate `u`
      relates both halves is unsatisfiable; and the corresponding positive satisfiable case.
- [ ] Add `TestSerialityPostHoc` and `TestInterpolationPostHoc` to `test_frame_class_mapping.py`,
      mirroring `TestConversePostHoc`/`TestForwardCompPostHoc`: enumerate the extracted model's
      `task_rel` pairs via the existing `extract_task_rel_pairs` helper and check the axiom holds
      over the extracted relation, reporting violations in the same `violations[:5]` style.
- [ ] Confirm all new tests fail for the right reason (missing builder method / unenforced axiom),
      not an import or fixture error.

**Timing**: 1.5 hours

**Depends on**: 2

**Verification Tier**: local

**Scope Hypothesis**: This phase asserts **4 new test classes** across **2 test files**, plus one
joint-satisfiability test. Confirm at implementation time by running
`pytest code/src/model_checker/theory_lib/bimodal/tests/unit/test_frame_constraints.py
code/src/model_checker/theory_lib/bimodal/tests/unit/test_frame_class_mapping.py -v` and counting
collected classes; if the post-hoc fixture (`solved_model`) cannot express one of the two post-hoc
checks against the extracted relation, record which and why rather than dropping it silently.

**Files to modify**:

- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_frame_constraints.py` - add `TestSeriality`, `TestInterpolation`, joint-satisfiability test; update module docstring's "three new frame constraint builder methods" enumeration
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_frame_class_mapping.py` - add `TestSerialityPostHoc`, `TestInterpolationPostHoc`

**Verification**:

- The two test files collect without error and every new test fails (RED).
- Each failure message names the missing builder or the unenforced axiom, not a collection error.
- Pre-existing tests in both files still pass.

---

### Phase 4: Implement and wire the two Skolemized constraints (GREEN) [COMPLETED]

**Deviation (recorded, not silently absorbed)**: the "Run the full bimodal unit suite to catch
collateral breakage" verification item surfaced a genuine, fully-characterized regression outside
its stated exclusions (`KNOWN_TIMEOUT_EXAMPLES`, `BM_CM_1`): `BM_CM_4` (a countermodel example,
N=2, M=2, not M>=3) goes from a clean 4.07s decided `match` (pre-Phase-4, and consistent with the
task 152 baseline's 18.26s) to `inconclusive` at its own 120s `max_time` budget with **both** new
axioms present. Isolation (both axioms tested individually against the same example) shows neither
Seriality alone (~9.27s, still decided `match`) nor Interpolation alone (~6.33s, still decided
`match`) is individually responsible -- the cost is superlinear in their *combination*, consistent
with cross-instantiation between the two new Skolem witness functions under MBQI. One mitigation
(an explicit single-term pattern anchoring Interpolation to its premise's ground `task_rel` term,
mirroring `forward_comp`'s existing `MultiPattern` convention) was tried and did not recover a
decided result (still `inconclusive` at 40s on the smaller probe budget). This is a **cost**
regression (`inconclusive`, not a decided flip to `unsat`) -- Seriality and Interpolation have not
been shown to eliminate `BM_CM_4`'s countermodel, only to make it undecided within budget. See
Phase 7 for the full-baseline accounting of this finding and the implementation summary for the
recorded remedy options (including this plan's own rollback section, which anticipated exactly
this failure mode and names "land Seriality alone, defer Interpolation" as the safe fallback --
not applied here without the user's decision, since it would silently narrow the shipped scope).

**Goal**: Add `build_seriality_constraint` and `build_interpolation_constraint` to `core.py` in the
Skolemized form the research measured, wire both into `build_frame_constraints`, and turn Phase 3's
tests green.

**Tasks**:

- [x] Add `build_seriality_constraint` near the other frame-axiom builders (after
      `build_forward_comp_constraint`, `core.py:344`). Two Skolem functions `serial_succ`/
      `serial_pred` over `(WorldStateSort, TimeSort) -> WorldStateSort`, one top-level `ForAll([w, x])`,
      guard `z3.And(x >= 0, self.is_valid_duration(x))`, body
      `z3.And(task_rel(w, x, serial_succ(w, x)), task_rel(serial_pred(w, x), x, w))`. **No nested
      `Exists`.**
- [x] Add `build_interpolation_constraint` immediately after it. One Skolem function
      `interp_witness` over `(WorldStateSort, IntSort, IntSort, WorldStateSort) -> WorldStateSort`,
      one top-level `ForAll([w, v, d1, d2])`, guards `is_valid_duration(d1)`, `is_valid_duration(d2)`,
      `is_valid_duration(d1 + d2)` plus the premise `task_rel(w, d1 + d2, v)`, body
      `z3.And(task_rel(w, d1, u), task_rel(u, d2, v))` with `u = interp_witness(w, d1, d2, v)`.
      **No nested `Exists`** — the nested reading is a measured regression on `BM_TH_3`/`BM_TH_4`.
- [x] Give both builders docstrings matching the existing house style: statement of the axiom, the
      "ProofChecker Alignment" paragraph citing the BimodalLogic predicate (`TaskFrame.Serial`,
      `TaskFrame.Interpolates`), and a `Returns:` block.
- [x] Call both from `build_frame_constraints` and insert them into the returned list in the frame-
      axiom block after `forward_comp` and before `*skolem_abundance`, preserving the list's
      documented MBQI-ordering rationale (`core.py:841`-`844`).
- [x] Run the two Phase 3 test files; confirm GREEN.
- [x] Run the full bimodal unit suite to catch collateral breakage.

**Timing**: 1.5 hours

**Depends on**: 3

**Verification Tier**: full

**Scope Hypothesis**: This phase asserts **2 new builder methods** and **2 new entries** in
`build_frame_constraints`'s returned list, taking it from the docstring's stated 11 constraints to
13. Confirm at implementation time by `len(semantics.frame_constraints)` before and after (note
`*skolem_abundance` contributes a variable count for M>=3, so compare the delta, not the absolute);
record the actual before/after numbers for use in Phase 5's docstring correction.

**Files to modify**:

- `code/src/model_checker/theory_lib/bimodal/semantic/core.py` - add both builders; call and insert both in `build_frame_constraints`

**Verification**:

- `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/unit/test_frame_constraints.py code/src/model_checker/theory_lib/bimodal/tests/unit/test_frame_class_mapping.py -v` is fully green.
- `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/ -v` is green apart from the suite's own documented exclusions (`KNOWN_TIMEOUT_EXAMPLES` at `test_bimodal.py:44`, the `unstable`-marked `BM_CM_1`).
- Neither new builder's source contains `z3.Exists`.

---

### Phase 5: Correct the `build_frame_constraints` docstring and the stale three-axiom test naming [COMPLETED]

**Goal**: Leave exactly one account of the frame class in `core.py`, and remove the now-false
"three TaskFrame axioms" language from the declaration-consistency tests.

**Tasks**:

- [x] Rewrite the "**TaskFrame Axioms (items 7-9)**" block in `build_frame_constraints`'s docstring
      (`core.py:554`-`560`) to enumerate the asserted axioms including Seriality and Interpolation,
      with their new item numbers, and to state that *Limit* and *Spherical* are discharged at the
      sort level and deliberately not asserted.
- [x] Update the docstring's total-constraint count and the numbered summary lists further down the
      same docstring (the "This method constructs 11 constraints total" line and the "7-9. Frame
      axioms" line) so the two enumerations inside one docstring do not contradict each other.
      Use the actual counts recorded by Phase 4's scope confirmation.
- [x] Update the `supported_frame_classes = frozenset({"Base"})` justification sentence to reflect
      the widened axiom set, and add a one-line pointer to `ARCHITECTURE.md`'s new
      `### Frame-Class Axioms` subsection as the fuller account.
- [x] Update the "task_restriction (DISABLED)" note's closing sentence, which currently says the
      post-hoc suite "validates the three TaskFrame axioms".
- [x] Rename `TestFrameClassDeclarationConsistency.test_three_taskframe_axioms_present_in_frame_constraints`
      and correct its docstring and the class docstring's "the three TaskFrame axioms" phrasing.
- [x] Correct `test_frame_constraints.py`'s module docstring, which enumerates "three new frame
      constraint builder methods" (already extended in Phase 3 — verify it was, and finish it here
      if not).

**Timing**: 45 minutes

**Depends on**: 4

**Verification Tier**: local

**Files to modify**:

- `code/src/model_checker/theory_lib/bimodal/semantic/core.py` - docstring only, no executable change
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_frame_class_mapping.py` - test rename plus docstring corrections

**Verification**:

- `grep -n "three TaskFrame\|three new frame\|items 7-9" ` over `core.py` and both test files
  returns no stale occurrence.
- `git diff` on `core.py` for this phase shows changes confined to docstring/comment lines.
- The two test files remain green.

---

### Phase 6: ARCHITECTURE.md frame-class ledger (Deliverables 3 and 4) [NOT STARTED]

**Goal**: Record the asserted/free frame-class split with per-row citations, plus the
duration-domain honesty note, as a factual reference subsection in `ARCHITECTURE.md`.

**Tasks**:

- [ ] Add a new `### Frame-Class Axioms` subsection directly after `### Constraint Generation`
      (`ARCHITECTURE.md:318`-`354`). Open it with a one-sentence note that, unlike the illustrative
      pseudocode above it, this subsection is a factual reference to `build_frame_constraints` in
      `code/src/model_checker/theory_lib/bimodal/semantic/core.py`, naming the real method names.
- [ ] Transcribe the report's Section 4.2 table: columns *Constraint*, *Status*, *Paper `def:frame`
      axiom?*, *Z3 encoding site*, *Citation*; rows `nullity_identity`, `converse`, `forward_comp`,
      `Interpolation`, `Seriality` (asserted) and `Limit`, `Spherical` (free).
- [ ] Resolve the task text's "four ASSERTED axioms" language explicitly. Neither available reading
      yields four: per **Z3 constraint row** the split is **5 asserted / 2 free** (the report's own
      Section 4.1 arithmetic reaches "four asserted" only by omitting Seriality from its own Section
      4.2 table); per **paper axiom** it is 2 asserted (*Compositionality*, *Seriality*) / 2 free
      (*Limit*, *Spherical*). Carry the 7-row constraint-level table and add a short note stating
      both counts and why they differ, rather than forcing a number that misdescribes the table.
- [ ] Add the Deliverable 4 footnote below the table: all asserted rows are guarded by
      `is_valid_duration`, restricting them to the bounded window `(-M, M)`, whereas the paper's
      axioms are unconditional over `\Z`; `is_valid_duration` is a guard, not a sort restriction
      (`task_rel`'s duration argument remains Z3 `Int`), so *Limit*/*Spherical* freeness is
      unaffected; the embedding question is recorded as an open gap, not resolved here, and is
      load-bearing for the follow-on certification work.
- [ ] Verify no existing `ARCHITECTURE.md` heading needs a Table of Contents entry change — the TOC
      lists `##`-level sections only, and this is a `###` subsection under an already-listed parent.
      Confirm rather than assume.

**Timing**: 1 hour

**Depends on**: 4

**Verification Tier**: prose

**Scope Hypothesis**: This phase asserts a table of **7 data rows** (5 asserted, 2 free) and that
**no TOC edit** is required. Confirm the row count against the report's Section 4.2 table as
transcribed, and confirm the TOC assumption by re-reading `ARCHITECTURE.md:7`-`17` before deciding
not to edit it.

**Files to modify**:

- `code/src/model_checker/theory_lib/bimodal/docs/ARCHITECTURE.md` - new `### Frame-Class Axioms` subsection

**Verification**:

- Every changed hunk lies inside `ARCHITECTURE.md` prose; no code file is touched by this phase.
- Each of the 7 rows carries a non-empty citation, and each asserted row names a real `core.py`
  method that exists post-Phase-4.
- The `### Frame-Class Axioms` heading renders under `## Model Construction` in the document
  outline (`grep -n "^#\{1,4\} "`).

---

### Phase 7: Full regression run, flip accounting, and final gate [NOT STARTED]

**Goal**: Re-run the full 52-example baseline against the new constraint set, explain every verdict
flip individually per the 152 comparison procedure, and confirm the full bimodal suite is green.

**Tasks**:

- [ ] Run `01_frame-axiom-regression-script.py`'s with-new-axioms arm against the post-Phase-4 tree;
      write `03_post-change-verdicts.json`.
- [ ] Diff `check_result` and `z3_model_status` per example against **both**
      `specs/152_.../baselines/01_abundance-removal-verdicts.json`'s `baseline` side (the recorded
      reference the procedure names) and Phase 1's `01_pre-change-verdicts.json` (the same-host
      control).
- [ ] Explain every flip individually in writing — never absorb one silently. A flip is not
      automatically a regression: narrowing the frame class can legitimately turn a SAT countermodel
      into an UNSAT. State the reason per flip.
- [ ] Handle the four cells that matter explicitly: `BM_TH_3`/`BM_TH_4` are expected to stay
      `match` per the report's Section 3.2; `BM_TH_1`/`BM_TH_2` are recorded
      **`inconclusive-at-90s`** in the 152 baseline, so an unchanged timeout there is **no signal**
      and must be reported as such, never as evidence of no regression.
- [ ] Do not re-adjudicate `BM_CM_1`'s `unstable` marker or `TN_CM_2`'s documented timeout; record
      this run's timings as data points against the README's stated criteria.
- [ ] Run the full bimodal test suite and the broader project suite:
      `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/ -v` and
      `PYTHONPATH=code/src pytest code/tests/ -v`.
- [ ] Record the flip accounting and the Phase 2 measurement outcome in the implementation summary.
- [ ] Flag, without fixing, that `oracle/bimodal_logic/provider.py:17`-`70` carries a frame-axiom
      table quoting `core.py`'s superseded three-axiom claim and is now stale — outside
      `file_scope`, needing a follow-on task.

**Timing**: 1.5 hours

**Depends on**: 5, 6

**Verification Tier**: full

**Scope Hypothesis**: This phase asserts a **52-example** run and that flips requiring individual
explanation are concentrated in the **4 cells** `BM_TH_1`-`BM_TH_4`. Confirm by counting entries in
`03_post-change-verdicts.json` and enumerating every differing key in the diff — a flip outside
those four is not covered by the abundance-dependence analysis and signals a different problem
class, so it must be investigated on its own terms rather than explained by frame-class narrowing.

**Files to modify**:

- `specs/153_assert_missing_frame_axioms_in_bimodal_semantics/baselines/03_post-change-verdicts.json` - new, post-change results
- `specs/153_assert_missing_frame_axioms_in_bimodal_semantics/baselines/README.md` - append the diff procedure used and the flip accounting

**Verification**:

- Every key present in both verdict files has been compared, and every differing key has a written
  explanation.
- Full bimodal suite green apart from the suite's own documented exclusions.
- `code/tests/` suite shows no new failures attributable to this change.

---

## Testing & Validation

- [ ] `TestSeriality` and `TestInterpolation` (solver-level) pass in `test_frame_constraints.py`.
- [ ] `TestSerialityPostHoc` and `TestInterpolationPostHoc` (extracted-model) pass in
      `test_frame_class_mapping.py`.
- [ ] The joint-satisfiability test confirms `frame_constraints` is `sat` with both new axioms —
      guarding against a vacuously-UNSAT frame.
- [ ] Pre-existing `TestNullityIdentity`, `TestConverse`, `TestForwardComp`,
      `TestConstraintInteractions`, and all post-hoc classes still pass.
- [ ] `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/ -v` green apart
      from documented exclusions.
- [ ] `PYTHONPATH=code/src pytest code/tests/ -v` shows no new failures.
- [ ] Full 52-example regression diff complete with every flip explained individually.
- [ ] Neither new builder uses `z3.Exists`.
- [ ] No stale "three TaskFrame axioms" phrasing remains in `core.py` or the bimodal tests.

## Artifacts & Outputs

- `specs/153_assert_missing_frame_axioms_in_bimodal_semantics/plans/01_seriality-interpolation-axioms.md` (this file)
- `specs/153_assert_missing_frame_axioms_in_bimodal_semantics/baselines/01_frame-axiom-regression-script.py`
- `specs/153_assert_missing_frame_axioms_in_bimodal_semantics/baselines/01_pre-change-verdicts.json`
- `specs/153_assert_missing_frame_axioms_in_bimodal_semantics/baselines/02_reachability-prototype-measurement.md`
- `specs/153_assert_missing_frame_axioms_in_bimodal_semantics/baselines/03_post-change-verdicts.json`
- `specs/153_assert_missing_frame_axioms_in_bimodal_semantics/baselines/README.md`
- `specs/153_assert_missing_frame_axioms_in_bimodal_semantics/summaries/01_seriality-interpolation-axioms-summary.md`
- Modified: `code/src/model_checker/theory_lib/bimodal/semantic/core.py`
- Modified: `code/src/model_checker/theory_lib/bimodal/docs/ARCHITECTURE.md`
- Modified: `code/src/model_checker/theory_lib/bimodal/tests/unit/test_frame_constraints.py`
- Modified: `code/src/model_checker/theory_lib/bimodal/tests/unit/test_frame_class_mapping.py`

## Rollback/Contingency

- All phases commit per green sub-step, so any phase can be reverted individually with
  `git revert` of its commit without disturbing earlier work.
- **If Phase 4 makes `frame_constraints` jointly UNSAT**: revert the Phase 4 commit, then re-add the
  two constraints one at a time, running the joint-satisfiability test after each, to isolate which
  axiom conflicts with the existing set (the over-strong iff-form `nullity_identity` is the most
  likely interaction partner).
- **If Phase 7's regression run shows unexplained flips outside `BM_TH_1`-`BM_TH_4`**: do not land.
  Those cells are outside the abundance-dependence analysis and signal a different problem class.
  Mark the phase `[BLOCKED]`, record the flips, and investigate before proceeding.
- **If Phase 7 shows a regression traceable to the new axioms** and no encoding change recovers it:
  the minimal safe fallback is to land Seriality alone (measured clean, structurally simpler) and
  defer Interpolation to a follow-on task, recording the measurement — the two constraints are
  independent additions and neither depends on the other.
- The regression scripts are process-local and never edit `core.py`, so no rollback of the
  `baselines/` artifacts is required for correctness; they are evidence, retained either way.
