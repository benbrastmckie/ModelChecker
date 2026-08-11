# Implementation Plan: Close the Serial-Pass Capacity Decision

- **Task**: 143 - Decide oracle serial pass timeout capacity
- **Status**: [COMPLETED]
- **Effort**: 1.5 hours nominal (+1 hour if the Phase 7 red-triage contingency triggers)
- **Dependencies**: Task 144 (completed, objective not achieved); task 145 (completed, green)
- **Research Inputs**:
  - `specs/143_decide_oracle_serial_pass_timeout_capacity/reports/01_serial-pass-capacity.md`
  - `specs/143_decide_oracle_serial_pass_timeout_capacity/summaries/01_phase4-triage-record.md`
  - `specs/145_decide_oracle_per_formula_solve_capacity/reports/02_capacity-decision-record.md`
  - `specs/145_decide_oracle_per_formula_solve_capacity/baselines/07_full-gate-transcript-run3.txt`
- **Artifacts**: plans/02_close-capacity-decision.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: python
- **Lean Intent**: false

## Overview

This task's substantive scope is **already complete and committed**. Commit `e3b09d4e`
("oracle: raise pass-2 budget to 1800s and re-pin gate collection counts") landed both halves:
`ORACLE_PASS2_TIMEOUT` 900 -> 1800 in `oracle/run-oracle-suite.sh` with the reasoning recorded
inline, and all four `BASELINE_ORACLE_*` pins in `code/scripts/verify-refactor.sh` re-pinned
together. The claim in `summaries/01_phase4-triage-record.md` that the edits were "left
uncommitted" is **stale** — they were committed subsequently.

The one thing that remained open was the blocker: Step 6 of `verify-refactor.sh` could not reach
green. That blocker is now **resolved**. Task 144 exhausted the encoding-level lever (option (b))
empirically — all three cost-reduction candidates were implemented, measured, and rejected. Task
145 then landed a composite per-solve remedy that **did** reach green: its
`baselines/07_full-gate-transcript-run3.txt` ends `[verify-refactor] All checks passed` with
`GATE_EXIT=0`, wall 34m42s, including the exact line this task was blocked on —
`Step 6: OK: gating oracle suite green across both passes`.

This plan therefore covers **closeout only**: ingest a task-143-owned full-gate confirmation run
(already in flight as this plan is written), write the missing capacity-decision summary, and
commit. It is not a re-do. No edit to `code/scripts/verify-refactor.sh`,
`oracle/run-oracle-suite.sh`, or `oracle/bimodal_logic/tests/test_oracle_interface.py` is planned
or expected; all three were verified correct, committed, and clean in the working tree.

### Research Integration

Findings integrated into this revision (all independently re-verified against the tree at HEAD
`65591011` before writing):

- **The blocker is discharged.** Task 145's remedies (`and_box_next` 60000 -> 240000 ms; BM_CM_4
  `max_time` 30 -> 120; BM_CM_1 `max_time` 15 -> 60; ternary `next_A` relocated to `xdist_serial`
  with a 480000 ms leg override; `all_future_neg` relocated to `xdist_serial`; new
  `GATING_RECHECK_SOLVE_TIMEOUT_MS=20000` decoupled from `SELF_SCAN_SOLVE_TIMEOUT_MS=10000`)
  reached green without lowering any floor and without xfailing, skipping, or disabling any test.
- **CORRECTION — the pins in plan v1 are stale.** `code/scripts/verify-refactor.sh:65-68` now
  holds **627 / 609 / 16 / 2**, not the 611/14 that this task originally set. Task 145 superseded
  those values in `6ea94522` by relocating `all_future_neg` and the ternary test into the serial
  pass. Partition: `609 + 16 + 2 = 627`. Verified twice: by direct read of the pins, and by the
  in-flight confirmation run's own Step 3 output. Plan v1's Testing & Validation checklist
  (611/14) is superseded by this plan's.
- **CORRECTION — the headroom figure in plan v1 and in `01_phase4-triage-record.md` is stale.**
  That record claims option (a) carries "roughly 840-950s of headroom", derived from a 14-test
  serial pass. Task 145's relocations moved the serial pass from 14 to 16 tests. The green run
  measured **pass 2 at 1315.36 s against the 1800 s budget — 73.1% of budget, 485 s slack**. The
  capacity decision still holds comfortably (versus the 96.6% / 30 s-slack condition that
  originated this task), but every artifact this plan produces must state the current figure, not
  the superseded one.
- **CORRECTION — plan v1's expected pass-2 "800-870 s band" is stale** for the same reason. The
  current serial population is 16 tests carrying widened per-solve budgets; ~1300 s is the
  calibrated expectation.
- **Green is contention- and seed-sensitive, not guaranteed on any single run.** Task 145's gate
  runs 1 and 2 were red under contention; it records a residual ~1-in-7 divergent tail on the
  ternary `next_A` leg plus a divergent seed-2 residual on BM_CM_1. This is a known, recorded
  property of the tree, and Phase 7 exists to classify it correctly rather than treat a recurrence
  as a new defect.
- **Option (b) is empirically exhausted, not merely deprioritized.** Plan v1 ruled it out of scope
  on effort grounds. Task 144 subsequently and independently established the stronger result: the
  encoding-level lever does not deliver. The summary must record this, since it materially
  strengthens the case for option (a).

### Prior Plan Reference

Supersedes `plans/01_formalize-capacity-decision.md`. That plan's Phases 1-4 are complete and are
preserved in the table below; its Phase 5 was half-executed (the commit landed as `e3b09d4e`; the
summary artifact was never written) and its unfinished half is Phase 8 here.

### Roadmap Alignment

No `roadmap_path` was provided in the delegation context and no roadmap consultation was
requested. No ROADMAP.md alignment recorded.

## Goals & Non-Goals

**Goals**:

- Ingest the result of the task-143-owned full-gate confirmation run and record it as
  task-143-owned provenance.
- If that run is red, triage it honestly against the known-residual set — without weakening
  anything to obtain a green.
- Write the missing summary artifact `summaries/02_capacity-decision-summary.md`, recording the
  capacity decision, the disposition of options (b) and (c), the re-pin provenance and its
  supersession by task 145, the **current** headroom figure, and honest verification status.
- Commit the task artifacts with correct task-scoped staging and mark the task complete.

**Non-Goals**:

- Re-deriving, re-litigating, or re-measuring the 1800 s value. Three research-phase
  measurements, two plan-v1 gate attempts, and task 145's green run all bear on it and all agree
  it is not the binding constraint.
- Any edit to `code/scripts/verify-refactor.sh`, `oracle/run-oracle-suite.sh`, or
  `oracle/bimodal_logic/tests/test_oracle_interface.py`. All three are correct, committed, and
  clean. **If an edit appears necessary, it must be justified explicitly against that finding —
  never assumed.**
- Re-attempting option (b). Task 144 exhausted it.
- Resolving the divergent-tail residuals (ternary `next_A`, BM_CM_1 seed 2). Task 145 recorded
  them plainly as unresolved-by-budget; they are not this task's scope and are not a defect
  introduced here.
- Any change to `ORACLE_PASS1_TIMEOUT`, `BASELINE_FULL_COUNT`, `SELF_SCAN_SOLVE_TIMEOUT_MS`,
  `GATING_RECHECK_SOLVE_TIMEOUT_MS`, `MIN_CONCLUSIVE_GATING_FORMULAS`, or
  `MIN_CONCLUSIVE_SCAN_FORMULAS`.

## The Explicit Prohibition

This constraint governs every phase below and mirrors the discipline already honored by tasks 143,
144, and 145. **To obtain a green run, it is prohibited to:**

- widen any timeout or budget (`ORACLE_PASS1_TIMEOUT`, `ORACLE_PASS2_TIMEOUT`, any per-solve
  `max_time`, any leg override, `SELF_SCAN_SOLVE_TIMEOUT_MS`, `GATING_RECHECK_SOLVE_TIMEOUT_MS`);
- lower any floor (`MIN_CONCLUSIVE_GATING_FORMULAS`, `MIN_CONCLUSIVE_SCAN_FORMULAS`, or any Step
  5c pinned constant);
- xfail, skip, disable, deselect, or otherwise neutralize any test;
- relax the Step 3 partition check, change the suite total, or convert any exact-equality pin to
  a floor or inequality.

A run that cannot go green without one of these moves is reported as such. It is never tuned into
green.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| The confirmation run comes back red on a known contention/seed residual, and is misread as a new defect that reopens the capacity decision | M | M | Phase 7 branch (i) enumerates the known-residual set with its recorded sources. A known-residual red is recorded as such and cited against task 145's green run-3 transcript as corroborating evidence that the tree is green-capable. It does not reopen the capacity decision and does not justify widening anything. |
| Pressure to widen a budget or lower a floor to convert a red into a green | H | L | The Explicit Prohibition section above, restated in Phase 7. A red that needs a weakening to clear is a report, not a fix. |
| The confirmation run is red on a genuine new failure and this is papered over as "just another residual" | H | L | Phase 7 branch (ii) requires positive evidence for the known-residual classification (matching test identity, matching failure mode, `disagreements=0`), not absence of evidence against it. Anything unmatched is a genuine new failure, blocks completion, and is reported. |
| Stale figures (611/14 pins, 840-950 s headroom, 800-870 s band) propagate into the summary from plan v1 or the triage record | M | M | Every corrected figure is stated explicitly in Research Integration and again in Testing & Validation, and Phase 8 requires the summary to name the superseded figure alongside the current one so the correction is legible rather than silent. |
| The long gate run is severed, or its transcript is incomplete when read | M | M | Phase 6 polls for the `GATE_EXIT` tail marker rather than assuming completion, and treats an absent marker as "still running", never as a failure. |
| Staging sweeps in unrelated concurrent-session edits | M | M | Phase 9 stages only the task directory plus `specs/state.json` / `specs/TODO.md`, after reviewing `git status --short` and `git diff --staged`. Never `git add -A`, never `git commit -am`. |

## Preserved Work (Plan v1 Phases 1-5)

Recorded, not re-planned. These are complete; nothing below re-executes them.

| v1 Phase | Outcome | Status |
|----------|---------|--------|
| 1: Validate the existing working-tree edits | Both edits confirmed correct and within constraints; zero corrections needed | [COMPLETED] |
| 2: Fast pre-gate re-confirmation (`--skip-oracle`) | Steps 1-5 green; transcript `baselines/verify-refactor-skip-oracle.txt` | [COMPLETED] |
| 3: Full end-to-end gate run | Two complete runs; both reached Step 6 and both failed there. Transcripts `baselines/oracle-suite-step6-contended-attempt.txt`, `baselines/oracle-suite-step6-quiet-attempt.txt` | [COMPLETED] |
| 4: Contingency triage | Branch (iii) genuine-failure classification recorded in `summaries/01_phase4-triage-record.md`. Correctly refused every weakening. Its "edits left uncommitted" claim is stale — see Phase 8 | [COMPLETED] |
| 5: Commit and summarize | Commit half executed: `e3b09d4e` landed both edits. Summary half never written — carried forward as Phase 8 | [PARTIAL] |

## Implementation Phases

**Dependency Analysis**:

| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 6 | -- |
| 2 | 7 | 6 |
| 3 | 8 | 6, 7 |
| 4 | 9 | 8 |

Phases within the same wave can execute in parallel. This plan is fully sequential. Phase 7 is
**conditional** — execute only if Phase 6 finds the confirmation run red; otherwise mark it
`[COMPLETED]` with the note "not triggered (gate green)" and proceed.

---

### Phase 6: Ingest the Full-Gate Confirmation Run [COMPLETED]

**Goal**: Determine the outcome of the task-143-owned full-gate confirmation run and record it as
task-143-owned provenance.

**Context**: The run was launched before this plan was written, as
`nix develop --command bash code/scripts/verify-refactor.sh`, with its transcript accumulating at
`specs/143_decide_oracle_serial_pass_timeout_capacity/baselines/01_full-gate-confirmation.txt` and
`GATE_EXIT` recorded at the tail. Do **not** launch a second concurrent gate run — two
simultaneous runs would contend with each other and manufacture exactly the contention failures
this task must be able to rule out.

**Tasks**:

- [ ] Check whether the run is still in flight (`ps aux | grep [v]erify-refactor`). If it is,
      poll the transcript until the `GATE_EXIT=` line appears at the tail. An absent `GATE_EXIT`
      marker means "still running" — never treat it as a failure.
- [ ] Read the completed transcript end to end. Record: the final status line, `GATE_EXIT`, wall
      clock, and the load figures at start and end.
- [ ] Confirm Step 3 reports `OK` on all four pins — total 627, gating-parallel 609,
      `xdist_serial` 16, slow 2 — and on the partition line `609 + 16 + 2 = 627`. (The
      already-captured head of the transcript shows all five green; re-confirm against the final
      file.)
- [ ] Classify the outcome into exactly one of the two branches below.
- [ ] **GREEN** (`GATE_EXIT=0` and the transcript ends `[verify-refactor] All checks passed`):
      confirm Step 6 reads `OK: gating oracle suite green across both passes` — the exact line
      this task was blocked on. Record the run as task-143-owned provenance. Mark Phase 7 "not
      triggered" and proceed to Phase 8.
- [ ] **RED** (any other outcome): proceed to Phase 7. Do not re-run, do not adjust anything, and
      do not draw any conclusion about the capacity decision before the triage in Phase 7 is done.
- [ ] If the runner's ephemeral Step 6 oracle transcript (`/tmp/verify-refactor-oracle.txt`) still
      exists, copy it to `baselines/02_oracle-suite-step6-confirmation.txt` — it carries the pass-2
      wall clock, the direct evidence of headroom under the current 16-test serial population. Its
      absence is not a failure; the pass-2 figure of record remains task 145's 1315.36 s.

**Timing**: 0.5 hours (mostly polling; the gate itself runs ~35 minutes on a quiet machine)

**Depends on**: none

**Files to modify**:

- `specs/143_decide_oracle_serial_pass_timeout_capacity/baselines/01_full-gate-confirmation.txt` -
  completed by the in-flight run itself
- `specs/143_decide_oracle_serial_pass_timeout_capacity/baselines/02_oracle-suite-step6-confirmation.txt` -
  new, only if `/tmp/verify-refactor-oracle.txt` survives

**Verification**:

- The transcript contains a `GATE_EXIT=` line (the run finished).
- The outcome is classified as exactly one of GREEN or RED, with the evidence quoted.
- Step 3's five `OK` lines are confirmed present against the final transcript.

---

### Phase 7: Red Triage (Conditional) [COMPLETED]

**Outcome**: not triggered (gate green). Phase 6 classified the task-143-owned confirmation run
as GREEN (`GATE_EXIT=0`, `[verify-refactor] All checks passed`, Step 6 `OK: gating oracle suite
green across both passes`), so this conditional phase's triage branches were never entered. No
file under `oracle/` or `code/` was touched during this closeout.

**Goal**: If Phase 6 found the confirmation run red, classify the failure honestly — distinguishing
a known, already-recorded residual from a genuine new failure — without weakening anything.

Execute **only** if Phase 6 classified the run RED. Apply the same discipline this task already
used in `summaries/01_phase4-triage-record.md`: classify first, act second, and never tune.

**The known-residual set** (all recorded before this plan; a match requires positive evidence, not
merely the absence of a better explanation):

| Residual | Signature | Recorded in |
|----------|-----------|-------------|
| Ternary `next_A` divergent tail | `TestTernarySerializationAll::test_all_sat_task_relation_ternary` exhausting its 480000 ms leg override; ~1-in-7 draws | task 145 decision record; `run-oracle-suite.sh` inline basis |
| BM_CM_1 divergent seed-2 residual | BM_CM_1 divergent on seed 2 after the measured 15 -> 60 s recalibration | task 145 (`8240e634`) |
| Conclusiveness-floor miss under external load | `MIN_CONCLUSIVE_GATING_FORMULAS` miss (e.g. 98-99 of 103) with `timeout_count > 0`, `disagreements=0`, coinciding with high load or a competing build | task 145 run 2; this task's `01_phase4-triage-record.md` |
| Interleaving `some_future` pre-existing tail | Pre-existing tail on the interleaving `some_future` path | task 145 run 1 |

**Tasks**:

- [ ] Extract the exact failing test identities, failure modes, timeout values, `timeout_count`,
      and `disagreements` count from the transcript. Record the load figures at start and end.
- [ ] **Branch (i) — known residual.** Every failure matches a row of the table above on test
      identity **and** failure mode, and `disagreements=0` throughout. Action: record it as a known
      contention/seed-sensitive residual of the already-documented kind, citing task 145's
      `baselines/07_full-gate-transcript-run3.txt` (green, `GATE_EXIT=0`, wall 34m42s) as
      corroborating evidence that the tree is green-capable under the current constants. **This
      does NOT reopen the capacity decision and does NOT justify widening any budget.** Proceed to
      Phase 8, which records the outcome honestly as a residual-red confirmation run rather than
      claiming a green this task did not obtain. At most one re-run is permitted, in a demonstrably
      quieter window, and only if the failure was a load-coincident floor miss; a second red is
      recorded, not re-run again.
- [ ] **Branch (ii) — genuine new failure.** Any failure that does not match a row on test identity
      and failure mode, or any run showing `disagreements > 0`, or any Step 1/2/3/5/7 failure.
      Action: **stop**. This blocks completion. Record the failure with full transcript evidence,
      report it plainly, and leave the task incomplete rather than papering over it. Do not weaken
      anything and do not commit a completion claim.
- [ ] Restate and honor the Explicit Prohibition: no budget widened, no floor lowered, no test
      xfailed/skipped/disabled, and the partition check and total left exactly as they are.
- [ ] Record the branch taken, the positive evidence for the classification, and the action taken.

**Timing**: 1 hour (only if triggered)

**Depends on**: 6

**Files to modify**:

- None. This phase produces a classification, recorded in the Phase 8 summary — not a code change.
  Under no branch does this phase edit `verify-refactor.sh`, `run-oracle-suite.sh`, or
  `test_oracle_interface.py`.

**Verification**:

- The chosen branch is recorded with the positive evidence that justifies it.
- `git status --short` shows no change to any file under `oracle/` or `code/`.
- Under branch (ii), the task is explicitly left incomplete with the failure reported.

---

### Phase 8: Write the Capacity-Decision Summary [COMPLETED]

**Goal**: Write the missing summary artifact — the task's durable decision record.

Currently only `summaries/01_phase4-triage-record.md` exists. This phase adds
`summaries/02_capacity-decision-summary.md`. Task-number references are permitted here: per
`.claude/rules/no-task-references-in-deliverables.md`, `specs/**` artifacts are explicitly
exempt, so citing tasks 144 and 145 is correct.

**Tasks**:

- [ ] Write `specs/143_decide_oracle_serial_pass_timeout_capacity/summaries/02_capacity-decision-summary.md`
      recording all of the following:
- [ ] **The decision**: option (a), `ORACLE_PASS2_TIMEOUT` 900 -> 1800 s at
      `oracle/run-oracle-suite.sh:136`, with the reasoning recorded inline at the constant and in
      `reports/01_serial-pass-capacity.md`. Note that recording the reasoning was the task's
      explicit precondition for option (a) being acceptable at all, and that it was met.
- [ ] **Why option (b) was not taken, and that it was subsequently exhausted.** Plan v1 ruled it
      out of scope on effort grounds. Task 144 then implemented, measured, and rejected all three
      encoding-level cost-reduction candidates — objective not achieved, the lever empirically
      exhausted. This materially strengthens option (a) rather than merely deferring option (b).
- [ ] **Why option (c) (accept-and-monitor) was not taken**: at 96.6% of budget with 30.4 s of
      slack, the pass was already effectively failing; monitoring an exhausted budget is not a
      decision.
- [ ] **Re-pin provenance, and its supersession.** This task re-pinned all four
      `BASELINE_ORACLE_*` values together in `e3b09d4e`. Task 145 **superseded** those values in
      `6ea94522`, relocating `all_future_neg` and the ternary test into the serial pass; the pins
      now read 627 / 609 / 16 / 2 with partition `609 + 16 + 2 = 627`. State the current values as
      current and the task-143-era values as superseded — do not present the older split as live.
- [ ] **The CURRENT headroom figure, explicitly superseding the stale one.** Pass 2 measured
      **1315.36 s against the 1800 s budget = 73.1% of budget, 485 s slack**, on task 145's green
      run 3. State plainly that this supersedes the "roughly 840-950 s of headroom" claim in
      `summaries/01_phase4-triage-record.md`, which was derived from the pre-relocation 14-test
      serial population. Contrast against the 96.6% / 30.4 s condition that originated this task:
      the capacity decision holds comfortably.
- [ ] **Honest verification status.** The blocker is discharged: task 145's
      `baselines/07_full-gate-transcript-run3.txt` reached `[verify-refactor] All checks passed`,
      `GATE_EXIT=0`, wall 34m42s, including `Step 6: OK: gating oracle suite green across both
      passes`. Record this task's own confirmation run and its outcome from Phase 6 — and, if red,
      the Phase 7 classification verbatim rather than a softened version.
- [ ] **Record that green is contention- and seed-sensitive, not guaranteed per run.** Task 145's
      runs 1 and 2 were red under contention; the ~1-in-7 divergent ternary `next_A` tail and the
      BM_CM_1 seed-2 residual are accepted, recorded, unresolved-by-budget conditions. Do not
      overstate the strength of the green.
- [ ] **Record what was refused**: no floor lowered, no budget widened to chase green, nothing
      xfailed/skipped/disabled, partition check and total untouched — across all of tasks 143, 144,
      and 145.
- [ ] Correct the stale claim in `summaries/01_phase4-triage-record.md` that the edits were "left
      uncommitted", by stating in this summary that they were subsequently committed as `e3b09d4e`.
      Do **not** rewrite the earlier triage record — it is an accurate record of its own moment;
      supersede it in the new artifact instead.

**Timing**: 0.75 hours

**Depends on**: 6, 7

**Files to modify**:

- `specs/143_decide_oracle_serial_pass_timeout_capacity/summaries/02_capacity-decision-summary.md` -
  new summary artifact

**Verification**:

- The file exists, is non-empty, and covers every bullet above.
- It states 627 / 609 / 16 / 2 as the current pins and names the task-143-era values as superseded.
- It states 1315.36 s / 1800 s / 73.1% / 485 s slack and explicitly names the 840-950 s claim as
  superseded.
- It cites tasks 144 and 145 by number with their concrete outcomes.
- It states the verification status without overstating it.

---

### Phase 9: Commit and Complete [COMPLETED]

**Outcome**: `git status --short` confirmed zero modifications to any file under `oracle/` or
`code/` before staging. Staged exactly the task directory (`specs/143_.../`) plus `specs/state.json`
and `specs/TODO.md`; `git diff --staged --name-only` was reviewed and contained no unrelated file.
Committed as `a55c50e3` ("task 143: complete implementation", session
`sess_1786483388_83cf84`). Task status set to `completed` via `update-task-status.sh` (blockers
cleared, `completion_summary` recorded). No push, no PR. The pre-existing unrelated
concurrent-session modifications (`specs/142_.../plans/01_*.md`, `specs/events.jsonl`,
`specs/.orchestrator-multi-state.json`) remain uncommitted in the working tree, as required.

**Goal**: Land the closeout artifacts as a properly scoped commit and mark the task complete.

Execute only if Phase 6 was GREEN, or Phase 7 classified branch (i). Under Phase 7 branch (ii),
the task does not complete: commit the artifacts produced so far if any, and report the blocking
failure.

**Tasks**:

- [ ] Run `git status --short` and confirm no file under `oracle/` or `code/` is modified. If any
      is, stop and investigate — this plan authorizes no such edit.
- [ ] Stage **only**: `specs/143_decide_oracle_serial_pass_timeout_capacity/` plus
      `specs/state.json` and `specs/TODO.md` if status postflight updates them. Never `git add -A`
      and never `git commit -am` — the working tree carries unrelated concurrent-session changes
      (`specs/142_.../plans/01_*.md`, `specs/events.jsonl`,
      `specs/.orchestrator-multi-state.json`) that must not be swept in.
- [ ] Review `git diff --staged --name-only` before committing to confirm no unrelated file was
      captured.
- [ ] Commit as `task 143: complete implementation` with the session ID in the body.
- [ ] Update task status to `[COMPLETED]` with a `completion_summary` naming the decision (option
      (a), 900 -> 1800), the re-pin and its supersession, the current headroom figure, and the
      verification basis. Clear the now-discharged `blockers` entries.
- [ ] Do not push and do not create a PR.

**Timing**: 0.25 hours

**Depends on**: 8

**Files to modify**:

- `specs/state.json`, `specs/TODO.md` - status postflight (via `update-task-status.sh`)

**Verification**:

- `git diff --staged --name-only` lists only the task directory and the two state files.
- `git log -1` shows the task-scoped message with the session ID.
- `git status --short` still shows the unrelated concurrent-session files as uncommitted.
- No file under `oracle/` or `code/` appears in the commit.

---

## Testing & Validation

This plan runs no new test command of its own beyond ingesting the already-in-flight gate run.
The checklist below is what that run's transcript is checked against — and supersedes plan v1's,
which carried the stale 611/14 pins and the stale 800-870 s pass-2 band.

- [ ] `baselines/01_full-gate-confirmation.txt` contains a `GATE_EXIT=` tail marker (run finished).
- [ ] Step 3 reports `OK` for oracle total **627**, gating-parallel **609**, `xdist_serial` **16**,
      slow **2**, and the partition line **`609 + 16 + 2 = 627`**.
- [ ] Step 6 reports `OK: gating oracle suite green across both passes` — or, if not, Phase 7
      classifies the red against the known-residual set with positive evidence.
- [ ] Any observed pass-2 wall clock is recorded against the 1800 s budget and against the current
      reference figure of 1315.36 s (73.1% of budget, 485 s slack) — **not** against the superseded
      800-870 s band.
- [ ] `git status --short` shows no modification to `code/scripts/verify-refactor.sh`,
      `oracle/run-oracle-suite.sh`, or `oracle/bimodal_logic/tests/test_oracle_interface.py`.
- [ ] `pass1_timeout` remains 1300; `pass2_timeout` remains 1800; `BASELINE_FULL_COUNT`,
      `SELF_SCAN_SOLVE_TIMEOUT_MS`, `GATING_RECHECK_SOLVE_TIMEOUT_MS`,
      `MIN_CONCLUSIVE_GATING_FORMULAS`, and `MIN_CONCLUSIVE_SCAN_FORMULAS` are untouched.

## Artifacts & Outputs

- `specs/143_decide_oracle_serial_pass_timeout_capacity/plans/02_close-capacity-decision.md`
  (this file)
- `specs/143_decide_oracle_serial_pass_timeout_capacity/baselines/01_full-gate-confirmation.txt`
  (Phase 6 — completed by the in-flight run)
- `specs/143_decide_oracle_serial_pass_timeout_capacity/baselines/02_oracle-suite-step6-confirmation.txt`
  (Phase 6 — conditional on the ephemeral `/tmp` transcript surviving)
- `specs/143_decide_oracle_serial_pass_timeout_capacity/summaries/02_capacity-decision-summary.md`
  (Phase 8)
- Already committed, not re-produced: `e3b09d4e` (`ORACLE_PASS2_TIMEOUT` 900 -> 1800 plus the
  four-value re-pin), subsequently superseded on the pin values by task 145's `6ea94522`.

## Rollback/Contingency

- **There is nothing to roll back.** This plan produces only `specs/**` artifacts. The substantive
  code changes landed in `e3b09d4e` and are further superseded by task 145's committed work; both
  are verified green by task 145's run-3 transcript. Reverting `e3b09d4e` would immediately
  re-fail Step 3 and re-open the capacity condition, and is not a contingency this plan
  contemplates.
- **If Phase 6 is red and Phase 7 lands on branch (ii)** (genuine new failure), the contingency is
  to stop and report — not to tune. The task stays incomplete. The correct follow-on is a new task
  scoped to the specific failure, exactly as this task's own blocker was handled by tasks 144 and
  145.
- **If Phase 7 lands on branch (i)** (known residual), the contingency is to record it plainly in
  the Phase 8 summary and complete on the strength of task 145's green run-3 transcript, stating
  clearly which run is being relied on and why. Do not claim a green this task did not itself
  obtain.
- **Never weaken to force green**: no timeout widening, no floor lowering, no partition-check
  relaxation, no conversion of exact-equality pins to floors, no xfail/skip/disable. A red that
  cannot be explained is a report, not a tuning exercise.
- **Never** run `git checkout --`, `git restore`, `git reset --hard`, or `git clean -fd` — the
  working tree carries unrelated concurrent-session changes. If a snapshot is genuinely required,
  use `bash .claude/scripts/git-snapshot.sh` first.
