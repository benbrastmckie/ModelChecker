# Implementation Plan: Task #195

- **Task**: 195 - research_encoder_spec_proof_routes
- **Status**: [IMPLEMENTING]
- **Effort**: 6.5 hours
- **Dependencies**: 192 (A2_GAP.md, complete), 193/194/201/202 (complete; their edits are the
  baseline this plan builds on)
- **Research Inputs**: `specs/195_research_encoder_spec_proof_routes/reports/01_encoder-spec-proof-routes.md`
- **Artifacts**: plans/01_encoder-spec-proof-routes.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: formal
- **Lean Intent**: false

## Overview

The task's own deliverable — a report evaluating routes to *proving* rather than testing A2, with a
recommendation and a staged path — is complete and landed. This plan lands the report's durable
conclusions in the two documents that carry the A2 story (`A2_GAP.md`, `ADEQUACY.md`) and takes the
two cheap "free wins" the report identified inside this task's declared file scope. It is a
documentation-and-one-test plan by design: the report explicitly recommends *against* attempting
routes (a), (b) or (c) now, and the engineering recommendations it does make (the per-candidate
differential strengthening, the divisor-period search question, A3 bound realization, the
round-trip ledger) have already been spun out as separate tasks and must not be re-implemented
here.

### Research Integration

Five conclusions from the report drive the six phases below:

1. `A2_GAP.md` section 10's route table is missing three routes the report evaluated: the
   **verified SMT-LIB emitter** (the cheaper variant of route (a), which deletes the Python
   generator rather than verifying it), **translation validation** (absent from the table
   entirely — the table's own route (b) is a *different* route, direct verification of Python),
   and **consuming a verified bounded enumerator** (the report's recommended rigor route, which
   makes A2 unnecessary for the claim A2 exists to support rather than discharging it).
2. `A2_GAP.md` section 8's "a **decision**, not a sample" claim is true of the *enumeration* but
   not of the *comparison*: leg (i)/(iii) agreement is an aggregate one-bit test
   (`(accepted > 0) == z3_model_status`), while A2 is a per-candidate claim.
3. `ADEQUACY.md` section 7.1's condition (iii) is satisfiable in principle today (section 6
   supplies both the certificate export and the independent re-checker), and the report enumerates
   what demonstrating it concretely requires of this repository — (iii-a) through (iii-e), of which
   only (iii-a) is blocking. None of that prerequisite structure is recorded.
4. `max_witnesses` is a precondition of both A2 and A3 (a cap below the number of boxed subformulas
   *forces* lasso sharing and trades completeness), and `ADEQUACY.md` does not mention
   `max_witnesses` anywhere.
5. Free win, measured in the report's Appendix A.2: `TestA0FrameClassStandingTest` checks one grid
   point while section 7.2 requires "no certificate at every configured length"; both instances
   report genuine UNSAT at all 11 swept grid points.

Deliberately **not** in this plan, because other tasks own them: the per-candidate leg (i)/(iii)
comparison (Stage 1 of the report), the divisor-period search coverage decision (Stage 2a's
code half), the closure set-level differential and the `family -> assignment` round-trip inverse
(Stage 2b/2c — they need a new `lake exe` and new production code outside this task's file scope),
the external BimodalLogic ask (Stage 3, another repository), and the verified emitter (Stage 4).
Phase 2 records each of these as a named, durable open obligation instead of implementing it.

### Prior Plan Reference

No prior plan for this task. Effort calibration is taken from the four completed sibling
documentation tasks in the same document family (each 3-6 phases of prose edits plus a grep-based
consistency gate, landing in a few hours), which is the shape this plan follows.

### Roadmap Alignment

No `roadmap_path` was supplied in this dispatch; no ROADMAP.md was consulted.

## Goals & Non-Goals

**Goals**:

- Record the three missing routes in `A2_GAP.md` section 10's table, with honest cost and status,
  so the route inventory matches the routes actually evaluated.
- Record the report's recommendation and staged path, and the routes explicitly declined (routes
  (a)/(b)/(c) now; Z3 UNSAT-proof reconstruction permanently), where a future reader of the A2
  story will find them.
- Correct `A2_GAP.md` section 8's overstatement about what the standing differential's *comparison*
  establishes, without weakening what its *enumeration* genuinely establishes.
- Make `ADEQUACY.md` section 7.1's condition (iii) actionable: state what demonstrating it requires
  of this repository, in dependency order, marking which prerequisite is blocking.
- Record `max_witnesses` as a stated precondition of A2 and A3 in `ADEQUACY.md`.
- Strengthen `TestA0FrameClassStandingTest` from one grid point to the measured swept grid, with
  genuine-UNSAT (not inconclusive) assertions.

**Non-Goals**:

- Implementing any of routes (a), (b), (c) or (d), or any part of report Stages 1, 3 or 4.
- Changing the encoder, the registry, the search, or the certificate wire format.
- Re-deciding the divisor-period/non-monotonicity question, or re-correcting the search-bound
  documentation — both already landed, and the coverage-fix decision belongs to a separate task.
- Adding the two recommended `.claude/context/` domain notes. `.claude/**` is a disposable deploy
  artifact (`rules/source-store-deploy-boundary.md`); those notes must be authored in the source
  store under a `/meta` task, not here.
- Creating or editing follow-on task entries; Phase 2 records obligations in the documents, it does
  not touch `specs/state.json`.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Concurrent siblings (research phases for the divisor-period and per-candidate tasks) touch the same bimodal docs this cycle | M | M | Re-read every target file immediately before editing; stage only this task's own hunks with an explicit file list, never a directory or glob `git add`; if a foreign commit or foreign uncommitted modification appears, check `git log` and STOP and report rather than proceeding |
| New route rows contradict, rather than extend, the section 10 rows that sibling tasks already closed out (routes (d) and (e) are marked "done") | M | M | Add rows with new letters after (f); leave every existing row's text untouched; the new honest-ranking sentences must classify the new routes by section 2's link types, not re-rank the old ones |
| Section 8's correction is read as retracting the enumeration's strength | M | M | Phrase as a scope distinction (enumeration is exhaustive; comparison is aggregate), keep the existing "decision, not a sample" sentence about the enumeration, and name the per-candidate strengthening as the open obligation rather than a defect |
| The swept-grid A0 test inflates unit-test runtime | L | L | The report measured 0.002-0.006s per solve at these grid points; measure the parametrized test's wall clock in Phase 5 and record it. If any grid point exceeds ~2s, drop that point and record why |
| A grid point in the report's Appendix A.2 list does not reproduce (the report's prose renders one formula differently from the suite's own string) | M | M | Take both formula strings verbatim from the current `test_structure.py` bodies, never from the report's prose; run the sweep before asserting it, and record the observed verdicts in Phase 5's notes |
| Documentation drifts from the plan's claims because a cited line number moved | L | M | Cite section headings and symbol names in prose; use line numbers only where the surrounding text already does, and re-verify each with a grep in Phase 6 |

## Implementation Phases

**Dependency Analysis**:

| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 3, 5 | -- |
| 2 | 2, 4 | 1 (for 2), 3 (for 4) |
| 3 | 6 | 1, 2, 3, 4, 5 |

Phases within the same wave can execute in parallel. Phases 1/2 and 3/4 are serialized within
their own file only to avoid conflicting edits to the same document.

---

### Phase 1: A2_GAP.md section 10 — add the three missing routes [COMPLETED]

**Goal**: Section 10's route table lists every route the research evaluated, each classified by
which of section 2's three link types it creates (or by which obligation it makes unnecessary),
with honest cost and status.

**Tasks**:

- [x] Re-read `docs/A2_GAP.md` section 10 immediately before editing (concurrent siblings). *(completed)*
- [x] Add a row **(g) Verified SMT-LIB emitter**: specify the generators in Lean over
      `LabelledLasso`/closure data, prove an encoding-adequacy theorem in both directions (an
      assignment satisfies the emitted clause set iff the decoded family satisfies (C1)-(C4) over
      the proved windows), have Lean print SMT-LIB2 that Python feeds to Z3 unchanged. What it
      buys: deletes the Python generator instead of verifying it; no verified-extraction pipeline
      needed (Lean has none). Residual trust: Lean's compiled runtime (already trusted by
      `lake exe check_certificate`), an audited printer, Z3's parser. Cost: ~4-8 weeks Lean side
      plus ~1-2 weeks Python side, and it must name the three integration costs the file hand-off
      loses — the four `assert_tracked` groups exist for unsat-core extraction
      (`models/structure.py`'s `_setup_solver`), `iterate.py` adds per-iteration difference and
      orbit-exclusion clauses, and `semantic/symmetry.py`'s group action works on live
      `WitnessRegistry` variables.
- [x] Add a row **(h) Translation validation**: per-run certification that the emitted clause set
      matches a verified specification. State plainly that it presupposes (g)'s verified generator
      *plus* a canonical form on both sides (a total order on variables; a normal form for
      `And`/`Or`/`Implies`/`==`/`AtMost`; a canonical variable naming that survives
      `WitnessRegistry`'s `lab_{lasso}_{slot}_{repr}` spelling), so it is strictly more expensive
      than (g). What it buys that (g) does not: it is the only route that establishes the property
      **for the code that actually runs**, and it preserves the incremental pipeline features
      (unsat cores, `iterate`, orbit exclusion) that a file hand-off loses. Note explicitly that
      this is a *different* route from the table's existing (b) ("direct verification"). *(completed)*
- [x] Add a row **(i) Consume a verified bounded enumerator**: a candidate list over closure `C`
      and a segment bound, its `mem_...` completeness lemma, and a decision of bounded absence
      inside Lean from the four landed `Decidable` instances. What it buys: it does not discharge
      A2, it makes A2 **unnecessary** for the claim A2 exists to support — the encoder and Z3 drop
      out of the claim entirely, and no Z3 UNSAT proof is needed. Record the three honest limits:
      only the *first* half is A1-gated (bounded absence needs the candidate list plus its
      completeness lemma, with no `fmp` hypothesis, so the non-`fmp` half is consumable ahead of
      the compression result); feasibility is the binding constraint (the upstream enumeration
      describes itself as "astronomically impractical... a decidability construction, not an
      algorithm", so this is viable as a **test oracle at feasible grid points**, not as a
      production oracle); and a verdict from a compiled Lean executable is compiled-Lean-trusted
      evidence, strictly better than Python-encoder-plus-Z3 but not kernel-checked. *(completed)*
- [x] Note in row (i) the space mismatch that any consumption must reconcile: the upstream
      enumeration ranges over segment lengths `<= n` while this search fixes lengths exactly
      `(nb, nm, nf)` — the same exact-period fact section 7.1 and `SETTINGS.md` now record, seen
      from the other side. *(completed)*
- [x] Extend the "Honest ranking" paragraph with the new routes: (g) and (h) satisfy section 2's
      category argument on its own terms (they create the missing link) and are substantial and
      unstarted; (i) satisfies it by removing the obligation rather than discharging it, and is the
      cheapest available increase in rigor. Leave the existing sentences about routes (a)-(f)
      unchanged. *(completed)*

**Timing**: 1.25 hours

**Depends on**: none

**Verification Tier**: prose

**Scope Hypothesis**: exactly three new table rows, lettered (g), (h), (i), plus additions to the
one "Honest ranking" paragraph — no existing row edited. Confirm at implementation time by
diffing: the change should be additive within section 10 only.

**Files to modify**:

- `code/src/model_checker/theory_lib/bimodal/docs/A2_GAP.md` - section 10: three new route rows and
  an extended honest-ranking paragraph

**Verification**:

- `grep -n 'Verified SMT-LIB emitter\|Translation validation\|verified bounded enumerator' docs/A2_GAP.md`
  returns the three new rows.
- `git diff` shows no deletions inside section 10's existing rows (additions only).
- Each new row states which of section 2's three link types it creates, or that it removes the
  obligation; no row claims a proof this repository does not have.

---

### Phase 2: A2_GAP.md sections 8, 10, 11 — the aggregate-vs-per-candidate limit, the recommendation, and the staged path [NOT STARTED]

**Goal**: Section 8's account of what the standing differential establishes is exact about the
*comparison* as well as the enumeration; section 10 ends with the report's recommendation and
staged path, including the routes explicitly declined; section 11 points at the report.

**Tasks**:

- [ ] Re-read `docs/A2_GAP.md` sections 8, 10 and 11 immediately before editing.
- [ ] In section 8, add a third exact limit: the leg (i)/(iii) **comparison** is aggregate. The
      test compares `(accepted > 0)` against `structure.z3_model_status`
      (`tests/integration/test_certificate_a2_triangle.py`, `_assert_exhaustive_triangle_agrees`),
      so millions of enumerated candidates collapse into a single existential bit, while A2's
      statement ("exactly the conjunction of (C1)-(C4), no extra constraint") is a **per-candidate**
      claim. An encoder wrong on almost every candidate but right about existence passes. State
      that the existing "decision, not a sample" claim holds of the enumeration and is unaffected,
      and that the per-candidate strengthening — asserting per candidate that every emitted clause
      is true under the candidate's pinned assignment iff the re-checker accepts it — is the named
      open obligation. Reference it by what it does, not by a task number.
- [ ] In the same addition, note that a solver-free pinned evaluator is the affordable form (a Z3
      call per candidate is not) and that this is translation validation in the small, linking it to
      the new route (h) row from Phase 1.
- [ ] Add a short subsection at the end of section 10, **"The recommended route, and what is
      declined"**, recording: (1) routes (a)/(b)/(c)/(g)/(h) are not to be attempted now, because
      each costs months while a discharged A2 buys a hardened never-report-validity rule (section
      7.4 of `ADEQUACY.md`, which already has a runtime fail-fast guard) plus A1-consumability, not
      a stronger headline claim — A0 caps the strongest honest claim at "ℤ-time valid" permanently
      and A3 is vacuous until A1 supplies `f`; (2) route (i) is the rigor route, scoped as a test
      oracle; (3) the immediate local work is the per-candidate strengthening of the existing
      differential, because it decides the A2 biconditional over the region already being
      enumerated at approximately the runtime already being paid; (4) reconstructing Z3 UNSAT proofs
      is declined on principle, not on difficulty — Z3's UNSAT is not in the soundness trust base
      at all (section 9's corollary), so reconstructing it upgrades only the negative report, which
      A0 caps and A1 blocks; (5) if a verified route is ever taken, prefer (g) over route (a)'s
      extraction-to-Python and over route (b)'s direct Python verification, and choose (h) over (g)
      only if the incremental pipeline features must be preserved.
- [ ] In that subsection, name the remaining obligations this repository has not taken, each by a
      durable anchor rather than a task reference: the `family -> assignment` round-trip inverse of
      `extract_certificate`; a set-level closure differential between `semantic/formula.py`'s
      `subformula_closure` and Lean's own `closureOf` (which currently is covered by the Lean leg
      **only for accepted certificates**); and the external ask for the non-`fmp` half of the
      bounded enumerator.
- [ ] Add `ADEQUACY.md` section 7.1's prerequisite list (Phase 3's output) to section 11's see-also,
      and cite this round's research report as the source of the new rows by its topic, not by task
      number.

**Timing**: 1.25 hours

**Depends on**: 1

**Verification Tier**: prose

**Files to modify**:

- `code/src/model_checker/theory_lib/bimodal/docs/A2_GAP.md` - section 8 (third limit), section 10
  (new closing subsection), section 11 (see-also)

**Verification**:

- `grep -n 'aggregate\|per-candidate' docs/A2_GAP.md` shows the new section 8 limit.
- `grep -n 'recommended route' docs/A2_GAP.md` shows the new subsection.
- `bash .claude/scripts/check-task-references.sh` (or a `grep -nE 'task [0-9]+' docs/A2_GAP.md`)
  reports no task-number reference in the edited file.
- Section 8's existing "decision, not a sample" sentence is still present and unqualified about the
  enumeration.

---

### Phase 3: ADEQUACY.md section 7.1 — what demonstrating condition (iii) concretely requires [NOT STARTED]

**Goal**: Section 7.1 states, in dependency order, what this repository must do to demonstrate
condition (iii), and records that section 6's certificate export plus independent re-checker make
the condition satisfiable in principle today.

**Tasks**:

- [ ] Re-read `docs/ADEQUACY.md` section 7.1 immediately before editing; the divisibility wording
      and the two routes to a sufficient condition are already landed there and must not be
      duplicated.
- [ ] Replace the closing sentence's "unbuildable until a certificate export and independent
      re-checker exist here at all (§6 supplies both)" with a positive statement: the two
      prerequisites section 6 supplies are now in place, so condition (iii) is satisfiable in
      principle; what remains is the following concrete work in this repository.
- [ ] Add a short ordered list, **(iii-a)** through **(iii-e)**:
      - **(iii-a) Fix the length space** — either sweep `(back, mid, fwd)` over the grid up to the
        bound (`f^3` individually cheap solves, and the only form under which "the same family
        space" is literally true) or restate A3 in divisor terms. Mark this as the **only blocking**
        prerequisite: without it (iii) is unprovable rather than merely unproved.
      - **(iii-b) State and check the represented space** — a written specification of exactly what
        the encoder's satisfying assignments represent: families over closure `C` with
        `1 + |{Box members}|` lassos when `max_witnesses` is uncapped, labels ⊆ `C`, segment lengths
        exactly `(nb, nm, nf)`, atoms base-only; checked by a `family -> assignment` inverse of
        `extract_certificate` plus a per-candidate agreement test.
      - **(iii-c) Closure agreement** — `semantic/formula.py`'s `subformula_closure` is a
        hand-written mirror of the Lean subformula closure, and both sides' clauses are guarded by
        it; the Lean leg recomputes its own closure from the wire's target, so it covers this
        **for accepted certificates only**. A direct set-level differential over generated formulas
        does not exist and is cheap.
      - **(iii-d) Witness-lasso budget** — the `max_witnesses` precondition (Phase 4's subject),
        cross-referenced rather than restated.
      - **(iii-e) Segment-length parity with the bound's shape** — once A1 lands, check that the
        bound's components map onto `back`/`mid`/`fwd` as the search means them; the upstream bound
        is a single `n` over all three segments while the search takes three independent settings.
- [ ] State that (iii-b) through (iii-d) are independently valuable now and do not wait on A1.
- [ ] Keep every existing citation in 7.1 intact; add no line numbers that have not been verified
      in this dispatch.

**Timing**: 1.25 hours

**Depends on**: none

**Verification Tier**: prose

**Files to modify**:

- `code/src/model_checker/theory_lib/bimodal/docs/ADEQUACY.md` - section 7.1: closing paragraph
  replaced, (iii-a)-(iii-e) list added

**Verification**:

- `grep -n '(iii-a)\|(iii-e)' docs/ADEQUACY.md` shows the new list bounds.
- `grep -n 'unbuildable' docs/ADEQUACY.md` returns nothing in section 7.1.
- The three conditions (i)/(ii)/(iii) themselves are unchanged in wording; only the follow-on
  requirements are new.
- Exactly one prerequisite is marked blocking.

---

### Phase 4: ADEQUACY.md — `max_witnesses` as a stated precondition of A2 and A3 [NOT STARTED]

**Goal**: `ADEQUACY.md` no longer omits the witness-lasso budget: the (ADEQ) statement and the A2
and A3 rows carry the precondition, and section 7.3 states it where the A2 claim is made.

**Tasks**:

- [ ] Re-read `docs/ADEQUACY.md` section 7's (ADEQ) statement, the component table, and section 7.3
      immediately before editing.
- [ ] Add the precondition to the (ADEQ) statement: the search's completeness claim holds only when
      `max_witnesses` is `None` (the default) or at least the number of boxed subformulas in the
      closure. A cap below that *forces* witness-lasso sharing (round-robin reassignment once the
      cap is reached), which trades completeness for a bounded search — as
      `semantic/witness_registry.py`'s own module docstring and `docs/SETTINGS.md`'s Witness Budget
      section both already record. Note that it never affects soundness.
- [ ] Add the same precondition, in one clause, to the A2 and A3 rows of the component table.
- [ ] In section 7.3, state the precondition beside the A2 statement, and note that the A2-triangle
      test runs uncapped so the standing evidence is evidence for the uncapped case.
- [ ] Cross-reference `SETTINGS.md`'s Witness Budget section rather than restating its numbers.
- [ ] Add a one-line pointer from section 7.1's (iii-d) bullet (Phase 3) to whichever of these
      locations carries the full statement, so the precondition is stated once and cited twice.

**Timing**: 1 hour

**Depends on**: 3

**Verification Tier**: prose

**Files to modify**:

- `code/src/model_checker/theory_lib/bimodal/docs/ADEQUACY.md` - section 7 (ADEQ) statement and
  component table; section 7.3

**Verification**:

- `grep -n 'max_witnesses' docs/ADEQUACY.md` returns at least three hits (statement, table,
  section 7.3) where it previously returned none.
- The precondition's wording does not contradict `SETTINGS.md`'s Witness Budget section or
  `witness_registry.py`'s docstring — check all three side by side.
- No claim that a capped search is unsound (it is under-complete, not unsound).

---

### Phase 5: Extend the A0 frame-class standing test to the swept grid [NOT STARTED]

**Goal**: `TestA0FrameClassStandingTest` checks the `prior_UZ` and `z1` instances at every grid
point the research swept, and distinguishes genuine UNSAT from an inconclusive solver run.

**Tasks**:

- [ ] Re-read `tests/unit/test_structure.py`'s `TestA0FrameClassStandingTest` immediately before
      editing, and take both formula strings **verbatim from the current test bodies** (the report's
      prose renders one of them differently; the suite's own strings are the correct source).
- [ ] Before changing the assertions, run the sweep manually over the grid
      `(1,1,1) (2,1,1) (3,1,1) (1,1,2) (2,1,2) (3,1,2) (2,1,3) (3,1,3) (2,2,2) (4,1,4) (1,0,1)`
      for both instances and record each verdict, each `structure.timeout` flag and each runtime.
      Drop any grid point that does not report genuine UNSAT and record why rather than asserting
      it.
- [ ] Parametrize both tests over the confirmed grid with `pytest.mark.parametrize`, keeping one
      test method per instance so a failure names the instance and the grid point.
- [ ] Assert all three facts at each point: `structure.z3_model_status is False`,
      `structure.certificate is None`, **and** `structure.timeout is False`. The last is the new
      substance: `models/structure.py` maps a solver UNKNOWN to `status=False` with `timeout=True`,
      so the existing two assertions alone do not distinguish "no countermodel exists" from "the
      solver gave up" — and section 7.2's claim is the former.
- [ ] Update the class docstring: the deciding test now runs at every configured length in the
      swept grid rather than one modest length, and it asserts non-inconclusiveness. Note that the
      search's non-monotonicity in `back`/`mid`/`fwd` does **not** disturb A0, as (SOUND) predicts
      it cannot — which is what makes the swept grid a useful control and not merely more cases.
- [ ] Record the measured total wall clock for the two parametrized tests in the phase notes.

**Timing**: 1.25 hours

**Depends on**: none

**Verification Tier**: local

**Scope Hypothesis**: 11 grid points, both instances, all reporting genuine UNSAT with
`timeout=False` and sub-10ms runtimes. This is the report's Appendix A.2 measurement, not a fact
about the current tree; confirm it by running the sweep before asserting it, and adjust the grid to
what reproduces.

**Files to modify**:

- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_structure.py` -
  `TestA0FrameClassStandingTest`: parametrized grid, `timeout` assertion, docstring

**Verification**:

- `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/unit/test_structure.py -k A0FrameClass -v`
  passes, showing 22 parametrized cases (2 instances x 11 grid points, or the confirmed subset).
- The same command's reported duration is recorded; if it exceeds a few seconds, the grid is
  trimmed and the reason recorded.
- A deliberate temporary inversion of one assertion fails the corresponding case only (confirms the
  parametrization actually varies the settings), then is reverted.

---

### Phase 6: Cross-document consistency gate and full-suite verification [NOT STARTED]

**Goal**: The edited documents agree with each other and with the code they describe, and the test
suites are green.

**Tasks**:

- [ ] Grep for contradictions introduced by this round: every statement about what the A2-triangle
      test establishes (`A2_GAP.md` sections 8 and 10, `ADEQUACY.md` section 7.3) must agree that
      the enumeration is exhaustive and the comparison is aggregate.
- [ ] Grep for `max_witnesses` across `docs/` and confirm `ADEQUACY.md`, `SETTINGS.md`,
      `USER_GUIDE.md`, `API_REFERENCE.md` and `witness_registry.py`'s docstring make one consistent
      claim (under-complete when capped below the boxed-subformula count; never unsound).
- [ ] Confirm every new cross-reference resolves: each cited section heading exists in the file it
      is cited from, and each cited symbol exists in the module named.
- [ ] Run the task-reference lint over the touched files and confirm no task numbers leaked into
      `code/**` (`bash .claude/scripts/check-task-references.sh`, or a scoped
      `grep -nEi 'task [0-9]+' ` over the four touched files).
- [ ] Run the bimodal suite:
      `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/ -q` and record
      the counts.
- [ ] Run the four-theory gate: `PYTHONPATH=code/src pytest code/tests/ -q` and record the counts.
- [ ] Record all recorded counts and the measured sweep runtimes in the phase notes for the
      summary.

**Timing**: 0.5 hours

**Depends on**: 1, 2, 3, 4, 5

**Verification Tier**: full

**Scope Hypothesis**: the bimodal suite and the four-theory gate are green at counts at least as
high as the sibling tasks' last recorded green runs (bimodal 508 passed; gate 645 passed, 5
skipped). Those figures are a prior-run hypothesis, not a target — record what this run actually
reports, and investigate a decrease rather than adjusting the expectation.

**Files to modify**:

- None (verification only; any fix this phase finds is a correction to the phase that introduced
  it)

**Verification**:

- Both pytest invocations exit 0, with counts recorded.
- The consistency greps produce no contradicting statement.
- The task-reference lint is clean for every file touched in `code/**`.

---

## Testing & Validation

- [ ] `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/unit/test_structure.py -k A0FrameClass -v`
      passes across the full confirmed grid, with `timeout is False` asserted at every point.
- [ ] `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/ -q` green.
- [ ] `PYTHONPATH=code/src pytest code/tests/ -q` green (four-theory gate).
- [ ] No task-number reference in any file touched under `code/**`.
- [ ] `A2_GAP.md` section 10 lists nine routes, each classified by section 2's link types or as
      removing the obligation.
- [ ] `ADEQUACY.md` section 7.1 carries the (iii-a)-(iii-e) prerequisite list with exactly one
      prerequisite marked blocking.
- [ ] `ADEQUACY.md` states the `max_witnesses` precondition in at least the (ADEQ) statement, the
      component table, and section 7.3.

## Artifacts & Outputs

- `code/src/model_checker/theory_lib/bimodal/docs/A2_GAP.md` — three new route rows, extended
  honest ranking, section 8's third limit, a recommendation-and-declined-routes subsection,
  see-also additions.
- `code/src/model_checker/theory_lib/bimodal/docs/ADEQUACY.md` — section 7.1's concrete (iii)
  prerequisite list; the `max_witnesses` precondition in the (ADEQ) statement, the component table
  and section 7.3.
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_structure.py` — swept-grid,
  non-inconclusive A0 standing test.
- `specs/195_research_encoder_spec_proof_routes/summaries/01_encoder-spec-proof-routes-summary.md`
  — implementation summary with the measured sweep verdicts, runtimes and suite counts.

## Rollback/Contingency

Every phase is additive prose in two documents plus one test class, so a phase is reverted by
`git revert` of that phase's commit; commit each phase separately to keep that true. If Phase 5's
sweep does not reproduce the report's Appendix A.2 verdicts, do not force the assertions: trim the
grid to what reproduces, record the divergence as a finding in the summary, and leave the
single-point test in place rather than replacing it with a failing parametrization. If the
consistency gate in Phase 6 finds a contradiction between the new section 8 text and section 7.3's
existing description of the differential, the correction belongs in the phase that introduced the
new text (Phase 2), not in a widening of Phase 6's scope.
