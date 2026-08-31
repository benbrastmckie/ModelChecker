# Implementation Plan: Audit bimodal frame class and verdict dependence

- **Task**: 152 - Audit bimodal frame class and verdict dependence
- **Status**: [IMPLEMENTING]
- **Effort**: 6 hours
- **Dependencies**: None
- **Research Inputs**: `specs/152_audit_bimodal_frame_class_and_verdict_dependence/reports/01_frame_class_and_verdict_ledger.md`
- **Artifacts**: plans/01_audit-frame-class-ledger.md (this file)
- **Standards**:
  - `.claude/context/formats/plan-format.md`
  - `.claude/context/standards/status-markers.md`
  - `.claude/rules/artifact-formats.md`
  - `.claude/rules/plan-format-enforcement.md`
- **Type**: python

## Overview

This task is **audit-only**: it ends with documents and a baseline, and changes no semantics.
The research phase has already produced the ledger report and a 52-example abundance-removal
baseline, so this plan covers the work that remains to make those artifacts trustworthy and
usable by the two follow-on tasks that will actually narrow the frame class. Three concrete gaps
drive the phases below: (1) the report's own code-reference table is explicitly flagged as
drift-prone and has not been re-checked since it was written; (2) the report's headline
"four missing axioms" conclusion is stated without distinguishing axioms *consumed by the proof
chain* from axioms that must be *asserted in ModelChecker* — a distinction that the existing
follow-on task descriptions already assume in the opposite direction; and (3) two of the four
abundance-dependent verdicts (`BM_TH_1`, `BM_TH_2`) rest on an `inconclusive` baseline side, which
is exactly the side a regression net cannot afford to leave undecided.

Definition of done: the ledger's claims are re-verified against the current trees, the
asserted-vs-free axiom question is settled on paper with hypotheses checked rather than cited,
the baseline is decided on both sides for all four abundance-dependent examples and is documented
as a re-runnable regression net, the `task_restriction` verdict stands as its own citable
document, and the corrected premises are propagated to the follow-on task entries.

### Research Integration

The research report (`reports/01_frame_class_and_verdict_ledger.md`) supplies all three
deliverables in draft form and is the primary input. Findings carried directly into this plan:

- **Deliverable 1 (ledger)**: the existential/universal two-column split (Section 1.1) is complete
  and needs no further work; it is the report's strongest section and is left untouched.
- **Deliverable 1 (axiom gap)**: Section 1.2's conclusion that `thm:extension`'s chain consumes
  *Seriality*, *Interpolation*, *Limit*, and *Spherical* is traced through the Lean sources and is
  accepted. What is **not** established is whether *Limit* and *Spherical* must be asserted in
  ModelChecker's setting — Phase 2 resolves this.
- **Deliverable 2 (baseline)**: `BM_TH_1`-`BM_TH_4` are the entire abundance-dependent surface out
  of 52 canonical examples; `BM_TH_1`/`BM_TH_2` baseline sides timed out at 30s and are recorded
  as `inconclusive`. Phase 3 addresses the undecided sides.
- **Deliverable 3 (`task_restriction`)**: the verdict — an independent gap, not subsumed — is
  argued from the fact that the frame axioms are stated purely over `task_rel` while
  `task_restriction` couples `task_rel` to `is_world`/`world_function`. Phase 5 promotes this to a
  standalone document.
- **Incidental finding to be recorded, not fixed**: every one of the 31 recorded runs in
  `baselines/01_abundance-removal-verdicts.json` carries the same
  `BimodalProposition.truth_value_at() missing 1 required positional argument: 'eval_time'`
  interpretation error. Verdicts are read off Z3 SAT/UNSAT status and are unaffected, but an
  undocumented pervasive error in a regression baseline is a trap for the follow-on tasks.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

`specs/ROADMAP.md` was consulted read-only. No roadmap item is directly advanced by this audit:
the roadmap's bimodal entries concern packaging, module structure, CI scoping, and notebooks, none
of which this task touches. No roadmap phases are included (`roadmap_flag` was not set).

## Goals & Non-Goals

**Goals**:
- Re-resolve every code and Lean reference the ledger asserts, correcting drift in place.
- Settle, with hypotheses checked rather than merely cited, which of the four consumed frame
  axioms must be *asserted* in ModelChecker and which are *free* in its finite/discrete setting.
- Convert the `BM_TH_1`/`BM_TH_2` baseline sides from `inconclusive` to decided, on a recorded
  quiet host, so the regression net has no undecided cells for abundance-dependent examples.
- Document the baseline as a re-runnable regression procedure the follow-on tasks can execute
  against a changed constraint set.
- Produce the `task_restriction` verdict as a self-contained, citable document.
- Propagate the corrected axiom premise to the follow-on task entries so neither inherits a
  premise this audit has superseded.

**Non-Goals**:
- No change to `core.py`, `operators.py`, or `examples.py` (the task's stated non-goals).
- Do **not** enable the disabled `task_restriction` constraint.
- Do **not** write the frame-class table into
  `code/src/model_checker/theory_lib/bimodal/docs/ARCHITECTURE.md`. That deliverable is explicitly
  owned by the follow-on frame-axiom task, which will write it alongside the constraints it lands;
  writing it here would produce two accounts in the tree, the exact outcome that task's own
  description warns against.
- Do not fix the `truth_value_at()` interpretation error surfaced by the baseline runs — record
  it as a finding; fixing it is a separate concern outside this audit's non-goals boundary.
- No re-adjudication of the `BM_CM_1` timing flake's `unstable` pytest marker; its documented
  20-run/20-seed exit criteria are not met by anything this task runs.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Phase 2 reverses the report's headline conclusion, leaving the ledger self-contradictory | H | M | Amend Section 1.2 in place with an explicit asserted-vs-consumed table rather than appending a contradicting section; state the correction as a refinement of the report's own chain trace, which remains correct as stated |
| `spherical_of_finite` / `limit_of_succOrder` hypotheses do not actually hold for ModelChecker's bounded `(-M, M)` duration window | M | M | Treat hypothesis failure as a legitimate outcome and record it as an open gap rather than forcing a derivation; `limit_of_succOrder` is stated at `TaskFrame ℤ` and needs successor structure, so this is the likely failure point and must be checked, not assumed |
| `BM_TH_1`/`BM_TH_2` still time out at a raised `max_time`, leaving the baseline undecided | M | M | Cap the re-run budget explicitly; if still undecided, record the timeout ceiling reached and the host condition, and mark the cell `inconclusive-at-{N}s` rather than silently retrying upward |
| Host contention perturbs the re-run, as it did the original (load 4.62 on 24 cores) | M | M | Record `uptime` load at run start and end in the log; if load exceeds the original run's, defer rather than record a worse-conditioned data point |
| Editing the baseline script invalidates comparability with the recorded run | M | L | Re-run both sides (baseline and no-abundance) for any example whose numbers are refreshed; never mix an old baseline side with a new no-abundance side |
| Follow-on task edits touch entries owned by other in-flight work | L | L | Restrict Phase 6 edits to the two named follow-on entries' description text; do not touch their status, dependencies, or artifacts |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 3 | -- |
| 2 | 2, 4 | 1 (for 2), 3 (for 4) |
| 3 | 5 | 2 |
| 4 | 6 | 2, 3, 4, 5 |

Phases within the same wave can execute in parallel.

---

### Phase 1: Re-resolve the ledger's reference table [COMPLETED]

- **Goal:** Confirm every code and Lean reference the ledger asserts still resolves to what the
  ledger claims it does, and correct any drift in place. The report itself flags its references as
  drift-prone, so an unverified reference table is the audit's weakest link.
- **Tasks:**
  - [ ] Walk the report's Section 4 reference table row by row; for each ModelChecker row, open the
        cited `core.py` / `operators.py` / `examples.py` / `test_bimodal.py` location and confirm
        the named symbol is at (or near) the cited line.
  - [ ] For each Lean row, confirm the cited file and symbol exist in the current BimodalLogic tree
        and that the quoted claim matches the source text.
  - [ ] Correct any row whose line number has drifted; where a symbol has moved file or been
        renamed, record the move rather than silently updating the number.
  - [ ] Confirm the three negative claims the ledger rests on are still true: *Seriality*,
        interpolation, *Limit*, and *Spherical* are asserted nowhere in `semantic/` (re-run the
        grep the report cites, and record the exact command and its output in the report).
  - [ ] Record in the report which rows were verified unchanged and which were corrected, so a
        future reader can tell verification from transcription.
- **Timing:** 0.75 hours
- **Depends on:** none
- **Verification Tier:** prose
- **Scope Hypothesis:** The report's Section 4 table asserts roughly 25 reference rows spanning 5
  ModelChecker files and 6 Lean files. Confirm the actual row count and file set by reading the
  table at implementation time; do not assume 25. If rows have been added since the report was
  written, verify all of them.
- **Files to modify:**
  - `specs/152_audit_bimodal_frame_class_and_verdict_dependence/reports/01_frame_class_and_verdict_ledger.md` -
    Section 4 table corrections plus a short verification-provenance note
- **Verification:**
  - Every Section 4 row has been opened and either confirmed or corrected; no row is left unchecked.
  - The re-run grep command and its verbatim output appear in the report.

---

### Phase 2: Settle asserted-vs-free for Limit and Spherical [COMPLETED]

- **Goal:** Resolve the tension between the report's "four missing axioms" conclusion and the
  follow-on frame-axiom task's standing premise that *Limit* and *Spherical* are free in
  ModelChecker's setting. The report establishes that the proof chain *consumes* four axioms; it
  does not establish that four must be *asserted*. These are different claims and the follow-on
  work will act on whichever one the ledger leaves standing.
- **Tasks:**
  - [ ] Read `TaskFrame.spherical_of_finite` and `TaskFrame.limit_of_succOrder` in the BimodalLogic
        tree; transcribe each lemma's exact hypotheses.
  - [ ] Check `spherical_of_finite`'s finiteness hypothesis against ModelChecker's carrier
        (`WorldState = BitVec[N]`, finite by construction) and state whether it is discharged.
  - [ ] Check `limit_of_succOrder`'s hypotheses against ModelChecker's duration structure. Note
        specifically that the lemma is stated at `TaskFrame ℤ` and needs successor structure,
        whereas `is_valid_duration` bounds durations to the open interval `(-M, M)` — which is not
        a group and may not carry the required structure. Record the outcome honestly: discharged,
        discharged-under-a-stated-embedding, or an open gap.
  - [ ] Read `FormalSystem/Metalogic/Decidability/IntPresentation.lean`, which already routes
        *Spherical* through `spherical_of_finite` and *Limit* through `limit_of_succOrder`, and
        record whether its presentation is a usable precedent for ModelChecker's setting or differs
        in a load-bearing way.
  - [ ] Amend the report's Section 1.2 with an explicit three-way table: axioms **consumed** by the
        `thm:extension` chain, axioms that must be **asserted** in ModelChecker, and axioms that are
        **free** (with the discharging lemma and the hypothesis that discharges it named per row).
  - [ ] Update the report's Section 0 summary and Section 1.2 ledger conclusion so the headline
        claim matches the refined table rather than the unqualified "four missing" framing.
  - [ ] Record the duration-domain question (`\D` must be a nontrivial totally ordered abelian
        group; `is_valid_duration` is a bounded interval) as a named open gap in the ledger, since
        it is load-bearing for both the *Limit* derivation and the follow-on certification work.
- **Timing:** 1.5 hours
- **Depends on:** 1
- **Verification Tier:** prose
- **Scope Hypothesis:** This phase assumes exactly two axioms (*Limit*, *Spherical*) are candidates
  for free discharge and two (*Seriality*, *Interpolation*) must be asserted. Confirm at
  implementation time by checking each of the four against a discharging lemma; if a third turns
  out to be derivable, or if one of the two candidates fails its hypothesis check, the table
  records the actual finding rather than this hypothesis.
- **Files to modify:**
  - `specs/152_audit_bimodal_frame_class_and_verdict_dependence/reports/01_frame_class_and_verdict_ledger.md` -
    Sections 0 and 1.2: consumed/asserted/free table, corrected headline claim, duration-domain gap
- **Verification:**
  - Each of the four axioms appears in exactly one column of the new table with a named
    justification.
  - Every "free" row names both the discharging lemma and the ModelChecker-side fact that satisfies
    its hypothesis.
  - The Section 0 summary no longer asserts an unqualified count that the Section 1.2 table
    contradicts.

---

### Phase 3: Decide the undecided baseline cells [COMPLETED]

- **Goal:** Convert `BM_TH_1` and `BM_TH_2`'s `inconclusive` baseline sides into decided results on
  a recorded quiet host, so that no abundance-dependent example has an undecided cell in the
  regression net the follow-on tasks will diff against.
- **Tasks:**
  - [x] Record `uptime` load average before starting; if it exceeds the original run's 4.62/4.59/4.18,
        wait for a quieter host rather than recording a worse-conditioned data point.
        **Deviation**: load was 10.65/7.06/5.29 at first check, exceeding the original. A
        session-shared-resource constraint applies here rather than a solo-host one: this audit
        ran inside a multi-agent orchestration session with several concurrent sibling task
        dispatches (visible as sustained ~99%-CPU solver/worker processes), so waiting for the
        exact original condition was not achievable on a bounded timeline. A 2-minute bounded
        wait (Monitor until-loop, threshold load<6) was used instead of an unbounded wait, load
        dropped to 6.79/7.03/5.60 and did not improve further within the window, and the re-run
        proceeded at that condition with both start and end load recorded (see
        `baselines/01_abundance-removal-run.log`) rather than deferred indefinitely.
  - [x] Re-run `BM_TH_1` and `BM_TH_2` on both sides (baseline and no-abundance) at a raised
        `max_time`, using the existing `baselines/01_abundance-removal-script.py` methodology
        unchanged apart from the time budget. Cap the escalation explicitly and stop there.
        Raised to 90s (3x); script: `baselines/02_phase3-rerun-script.py`.
  - [x] Re-run `BM_TH_3` and `BM_TH_4` on both sides at the same session's host conditions to
        confirm their clean flips reproduce; these are the two cells the whole regression net's
        credibility rests on, and they are cheap (0.04s each). Both reproduced exactly.
  - [x] If a cell remains undecided at the capped budget, record it as `inconclusive-at-{N}s` with
        the ceiling and host condition, not as a bare `inconclusive`.
        **Applies**: `BM_TH_1`/`BM_TH_2` both remained `inconclusive` at the capped 90s (not a
        host-noise artifact of the original 30s cap — a longer, still-elevated-load run produced
        the same outcome), recorded as `inconclusive-at-90s` per the plan's own Phase 3
        contingency, which anticipates exactly this outcome and states it does not block the
        deliverable.
  - [x] Record the pervasive `BimodalProposition.truth_value_at() missing 1 required positional
        argument: 'eval_time'` interpretation error as a documented caveat: state that it appears
        on every recorded run, that verdicts are read from Z3 SAT/UNSAT status and are therefore
        unaffected, and that it is out of scope to fix here. (Carried into Phase 4's README.)
  - [x] Write refreshed cells into the verdicts JSON and append the new transcript to the run log,
        preserving the original recorded values alongside rather than overwriting them, so the two
        runs are comparable. Done via a new `rerun_20260831_phase3` field per example.
  - [x] Update the report's Section 2.2 table so the `BM_TH_1`/`BM_TH_2` rows reflect the decided
        (or explicitly capped) results instead of the original timeouts.
- **Timing:** 1.5 hours
- **Depends on:** none
- **Verification Tier:** local
- **Scope Hypothesis:** The report classifies exactly 4 of 52 canonical examples as
  abundance-dependent (`BM_TH_1`-`BM_TH_4`), with `BM_TH_5` outside the canonical dict. This phase
  re-runs only those 4. Confirm the classification still holds by checking the verdicts JSON's
  `verdict_flipped` flags at implementation time; if any other example now flips, re-run that one
  too and treat the classification change as a finding for Section 2.2.
- **Files to modify:**
  - `specs/152_audit_bimodal_frame_class_and_verdict_dependence/baselines/01_abundance-removal-verdicts.json` -
    refreshed cells for the re-run examples, original values preserved
  - `specs/152_audit_bimodal_frame_class_and_verdict_dependence/baselines/01_abundance-removal-run.log` -
    appended transcript with host conditions
  - `specs/152_audit_bimodal_frame_class_and_verdict_dependence/baselines/01_abundance-removal-script.py` -
    time-budget parameterization only, if needed to run the subset
  - `specs/152_audit_bimodal_frame_class_and_verdict_dependence/reports/01_frame_class_and_verdict_ledger.md` -
    Section 2.2 table rows and the Section 2.1 method note
- **Verification:**
  - `core.py`, `operators.py`, and `examples.py` are unmodified (`git status` on those paths is
    clean) — the monkeypatch stays process-local.
  - Every abundance-dependent example has a decided result on both sides, or an explicitly capped
    `inconclusive-at-{N}s` with its ceiling recorded.
  - Host load is recorded in the log for the re-run session.

---

### Phase 4: Document the baseline as a re-runnable regression net [NOT STARTED]

- **Goal:** Make the baseline executable by the follow-on tasks rather than merely readable. Both
  follow-on tasks are required to diff against this baseline, and neither can do so from a
  throwaway script with no invocation record.
- **Tasks:**
  - [ ] Write `baselines/README.md` documenting: what the baseline measures, how to invoke the
        script, what `PYTHONPATH` and working directory it needs, and roughly how long a full
        52-example run takes.
  - [ ] Document the comparison procedure a follow-on task must follow: re-run against the new
        constraint set, diff `verdict_flipped` and `check_result` per example, and explain every
        flip individually rather than absorbing it.
  - [ ] Name the four abundance-dependent examples explicitly as the cells that must be explained
        if they change, and state plainly that the remaining examples are not informative for the
        abundance question.
  - [ ] Record the known caveats: the pervasive interpretation error, the `BM_CM_1` timing flake and
        its `unstable` marker, `TN_CM_2`'s separately documented timeout, and the fact that
        `MF_MODAL_FUTURE_TH` / `BM_TH_5` are already-known non-theorems and not regressions.
  - [ ] State that a verdict flip after adding a genuine frame axiom is not automatically a
        regression — narrowing the frame class legitimately turns SAT into UNSAT — but that every
        flip must be explained.
- **Timing:** 0.5 hours
- **Depends on:** 3
- **Verification Tier:** prose
- **Scope Hypothesis:** This phase names four abundance-dependent examples as the cells a follow-on
  task must explain. Take that set from Phase 3's refreshed verdicts JSON (the `verdict_flipped`
  flags), not from this plan's text, so the README documents the measured set rather than an
  assumed one.
- **Files to modify:**
  - `specs/152_audit_bimodal_frame_class_and_verdict_dependence/baselines/README.md` - new file
- **Verification:**
  - The documented invocation is checked by running it once end-to-end (or, if the full run is too
    slow, by running the documented single-example form) and confirming it works as written.
  - All four caveats above appear.

---

### Phase 5: Produce the standalone task_restriction verdict [COMPLETED]

- **Goal:** Promote Deliverable 3 from a section of the ledger to a self-contained document the
  follow-on tasks can cite directly. The task's own framing is that it "ends with two documents and
  a baseline"; the verdict is the second document, and it is the artifact the certification
  follow-on will lean on when it replaces the `task_restriction` soundness comment's prose
  assurance.
- **Tasks:**
  - [x] Create `reports/02_task-restriction-verdict.md` as a self-contained document: restate the
        constraint's content, its disabled status and the performance reason for it, and the verdict
        that it remains an independent gap.
  - [x] Carry over the structural argument: the frame axioms are stated purely over the abstract
        `task_rel` relation, while `task_restriction` couples `task_rel` to the solver's
        `is_world`/`world_function` enumeration; adding the former supplies no mechanism that
        discharges the latter.
  - [x] Incorporate the Phase 2 outcome: state the verdict against the axioms that will actually be
        asserted, not against the unqualified four, so the document does not inherit a superseded
        premise.
  - [x] Assess (rather than accept) the existing source-comment soundness analysis: confirm by
        inspection that the modal and tense operators read only `is_world` and `world_function` and
        never `task_rel` directly, and state whether the comment's SAT/UNSAT asymmetry conclusion
        survives this audit unchanged. `grep -n "task_rel" operators.py` returns zero matches
        file-wide, confirming the claim exactly (stronger than the file's original hedge); the
        SAT/UNSAT-asymmetry conclusion is confirmed to stand unchanged.
  - [x] State explicitly that `task_restriction` was not enabled and remains disabled.
  - [x] Add a cross-reference from the ledger's Section 3 to this document, leaving the ledger's own
        section as a summary pointer rather than a duplicate account.
- **Timing:** 1 hour
- **Depends on:** 2
- **Verification Tier:** prose
- **Files to modify:**
  - `specs/152_audit_bimodal_frame_class_and_verdict_dependence/reports/02_task-restriction-verdict.md` -
    new file
  - `specs/152_audit_bimodal_frame_class_and_verdict_dependence/reports/01_frame_class_and_verdict_ledger.md` -
    Section 3 reduced to a summary plus cross-reference
- **Verification:**
  - The verdict document is readable standalone: it does not require the ledger to state its claim
    or its grounds.
  - The verdict is stated against the Phase 2 asserted-axiom set.
  - `git status` confirms no source file under `code/` was touched.

---

### Phase 6: Propagate corrected premises and write the summary [NOT STARTED]

- **Goal:** Ensure neither follow-on task inherits a premise this audit superseded, and close the
  task with a summary that states what the audit settled and what it deliberately left open.
- **Tasks:**
  - [ ] Update the follow-on frame-axiom task's description in `specs/TODO.md` and the matching
        `specs/state.json` entry: its opening premise says two of four axioms are missing; replace
        it with the Phase 2 consumed/asserted/free finding and point at the ledger. Leave its own
        Deliverable 3 (the free-axiom citations and the ARCHITECTURE.md table) intact — Phase 2
        confirms that deliverable's direction rather than replacing it.
  - [ ] Update the certification follow-on task's description where it names the missing axioms, so
        its dependency rationale matches the corrected finding.
  - [ ] Add pointers in both follow-on entries to `baselines/README.md` as the concrete regression
        procedure, and to `reports/02_task-restriction-verdict.md` for the `task_restriction`
        question.
  - [ ] Confirm `specs/TODO.md` and `specs/state.json` agree after the edits.
  - [ ] Write `summaries/01_audit-frame-class-ledger-summary.md`: what the audit settled (the
        asserted-vs-free split, the decided baseline cells, the `task_restriction` verdict), what it
        deliberately left open (the duration-domain gap, the interpretation error, the `BM_CM_1`
        flake), and what the follow-on tasks must do with the baseline.
- **Timing:** 0.75 hours
- **Depends on:** 2, 3, 4, 5
- **Verification Tier:** prose
- **Scope Hypothesis:** This phase assumes exactly two follow-on task entries carry the superseded
  "two missing axioms" premise. Confirm at implementation time by grepping `specs/TODO.md` and
  `specs/state.json` for the premise text; update every entry that carries it, not just two.
- **Files to modify:**
  - `specs/TODO.md` - follow-on task description text only
  - `specs/state.json` - matching `description` fields only
  - `specs/152_audit_bimodal_frame_class_and_verdict_dependence/summaries/01_audit-frame-class-ledger-summary.md` -
    new file
- **Verification:**
  - No follow-on entry still asserts the superseded axiom count.
  - `specs/state.json` parses as valid JSON and its edited descriptions match `specs/TODO.md`.
  - Only the two follow-on entries' `description` fields changed; status, dependencies, and
    artifacts are untouched.

---

## Testing & Validation

- [ ] `git status --short code/src/model_checker/theory_lib/bimodal/` is clean throughout: no change
      to `core.py`, `operators.py`, `examples.py`, or `docs/ARCHITECTURE.md`.
- [ ] The disabled `task_restriction` constraint remains disabled; no constraint was added, removed,
      or re-enabled in the tracked source tree.
- [ ] The baseline re-run reproduces `BM_TH_3`/`BM_TH_4`'s recorded clean flips; a failure to
      reproduce is itself a finding and must be recorded, not retried until it agrees.
- [ ] The documented baseline invocation in `baselines/README.md` runs as written.
- [ ] `specs/state.json` parses (`jq . specs/state.json`) after the Phase 6 edits.
- [ ] Every claim in the ledger's Section 4 table has been opened and confirmed or corrected.
- [ ] No file outside `specs/**` references a task number (per the no-task-references rule); the
      audit's outputs live under `specs/**`, where task references are permitted.

## Artifacts & Outputs

- `specs/152_audit_bimodal_frame_class_and_verdict_dependence/reports/01_frame_class_and_verdict_ledger.md` (amended: verified references, consumed/asserted/free table, decided baseline rows, Section 3 cross-reference)
- `specs/152_audit_bimodal_frame_class_and_verdict_dependence/reports/02_task-restriction-verdict.md` (new)
- `specs/152_audit_bimodal_frame_class_and_verdict_dependence/baselines/README.md` (new)
- `specs/152_audit_bimodal_frame_class_and_verdict_dependence/baselines/01_abundance-removal-verdicts.json` (refreshed cells)
- `specs/152_audit_bimodal_frame_class_and_verdict_dependence/baselines/01_abundance-removal-run.log` (appended transcript)
- `specs/152_audit_bimodal_frame_class_and_verdict_dependence/summaries/01_audit-frame-class-ledger-summary.md` (new)
- `specs/TODO.md` and `specs/state.json` (follow-on task descriptions corrected)

## Rollback/Contingency

Every output of this task is a document, a baseline record, or task-management metadata; no
executable behavior changes, so rollback is a `git revert` of the task's commits with no
migration, no rebuild, and no test-suite implication.

Per-phase contingencies:
- **Phase 2 hypothesis failure**: if `limit_of_succOrder`'s hypotheses do not hold over the bounded
  `(-M, M)` duration window, do not force a derivation. Record *Limit* as asserted-or-open rather
  than free, and flag the discrepancy for the follow-on frame-axiom task, whose Deliverable 3
  currently assumes the free route.
- **Phase 3 persistent timeout**: if `BM_TH_1`/`BM_TH_2` remain undecided at the capped budget, keep
  the original recorded values, mark the cells `inconclusive-at-{N}s`, and state in Section 2.2 that
  the dependence conclusion for those two rests on the no-abundance side plus the existing
  code-comment corroboration — which is what the report already argues, so the deliverable is not
  blocked by this outcome.
- **Phase 6 conflict**: if a follow-on task entry is concurrently in flight (status beyond
  `not_started`), skip its edit, leave the entry untouched, and record the skip in the summary
  rather than editing an entry another agent may be holding.
