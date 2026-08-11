# Implementation Plan: Formalize the Serial-Pass Capacity Decision

- **Task**: 143 - Decide oracle serial pass timeout capacity
- **Status**: [IMPLEMENTING]
- **Effort**: 4 hours (3 hours on the nominal path; +1 hour if the Phase 4 contingency triggers)
- **Dependencies**: None
- **Research Inputs**: `specs/143_decide_oracle_serial_pass_timeout_capacity/reports/01_serial-pass-capacity.md`
- **Artifacts**: plans/01_formalize-capacity-decision.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: python
- **Lean Intent**: false

## Overview

The substantive code changes this task owns **already exist as uncommitted working-tree edits**,
made during the research dispatch: `ORACLE_PASS2_TIMEOUT` raised 900s -> 1800s in
`oracle/run-oracle-suite.sh` (capacity option (a), with the measurement basis recorded inline),
and all four `BASELINE_ORACLE_*` pins in `code/scripts/verify-refactor.sh` re-pinned to the
verified-current `627/611/14/2` (with provenance recorded inline). This plan does **not** redo
that work — it validates it, closes the one verification gap the research phase could not close,
and commits it.

The gap is specific and named in the research report: a full end-to-end `verify-refactor.sh` run
reaching `All checks passed` was never obtained. Steps 1-3 and 5 were confirmed green twice
against the new pins; **Step 6 — the gating oracle suite itself, which is the only thing that
exercises the new 1800s pass-2 timeout for real — was never reached** in any attempt, all of
which were curtailed by severe machine contention (load average 6-11, ~10GB swap in use,
multiple competing agent sessions and an unrelated `lean build`). Closing that gap is the
definition of done for this task.

Scope is deliberately narrow: review, verify end-to-end, commit. No new capacity analysis, no
re-derivation of the 1800s figure, no new measurements beyond what the gate run itself produces.

### Research Integration

Findings from `reports/01_serial-pass-capacity.md` carried directly into this plan:

- **Decision is settled**: option (a) selected; options (b) (speed up the four solves) and (c)
  (accept-and-monitor) considered and rejected with recorded reasoning. This plan does not
  reopen the decision.
- **The task description's 606/590/14/2 figure was stale.** A prior task added 21 fast tests
  (15 in `test_timeout_skip_inventory.py`, 6 from `TestCatalogLabelAdjudication`), so the true
  current state is 627/611/14/2. Phase 1 verifies the pins match the verified-current values,
  **not** the stale ones quoted in the task description.
- **Steps 1, 2, 3, 5 confirmed green twice**; transcript at
  `baselines/verify-refactor-full-gate.txt`.
- **Step 4 stalls were contention, not a hang** — a bounded isolated re-run completed in 175.22s
  (`302 passed`). Neither edited file touches bimodal source or tests. This directly informs the
  Phase 4 triage tree: a Step 4 stall is an environment signal, never a defect signal for this
  task's edits.
- **Three converged pass-2 measurements** (869.58s, 802.98s, 836.37s) set the expectation
  Phase 3 checks its observed wall clock against.
- **`TestGatingConclusiveScan` conclusiveness-floor sensitivity to external CPU load**
  (Finding 3) is a known environmental hazard, explicitly out of scope, and must not be "fixed"
  by touching any floor constant if it recurs.

### Prior Plan Reference

No prior plan. This is the first plan for this task.

### Roadmap Alignment

No `roadmap_path` was provided in the delegation context and no roadmap consultation was
requested. No ROADMAP.md alignment recorded.

## Goals & Non-Goals

**Goals**:

- Validate the two existing uncommitted working-tree edits against the research report's stated
  decisions, without re-making them.
- Confirm the capacity reasoning is recorded where the task requires it (inline in
  `run-oracle-suite.sh`, plus the report) — the task's explicit condition on option (a) being
  acceptable at all.
- Obtain a full end-to-end `verify-refactor.sh` run (no `--skip-oracle`) inside `nix develop`
  reaching `[verify-refactor] All checks passed`, with Step 6 exercising the new 1800s pass-2
  timeout for real.
- Preserve the Step 6 oracle transcript as a durable task baseline (the runner writes it to
  `/tmp/verify-refactor-oracle.txt`, which is ephemeral).
- Commit both edits plus task artifacts with correct task-scoped staging.

**Non-Goals**:

- Re-deriving or re-litigating the 1800s value, or re-running standalone pass-2 measurements
  (three converged measurements already exist).
- Option (b) work — making the four relocated solves faster. Explicitly out of scope per the
  research report.
- Fixing the Finding 3 `TestGatingConclusiveScan` contention sensitivity.
- Any change to `SELF_SCAN_SOLVE_TIMEOUT_MS`, `MIN_CONCLUSIVE_GATING_FORMULAS`, or
  `MIN_CONCLUSIVE_SCAN_FORMULAS`.
- Any relaxation of the Step 3 partition check, the suite total, or the exact-equality semantics
  of the pins.
- Editing `oracle/bimodal_logic/tests/test_oracle_interface.py` (in `file_scope` as an
  anticipated file, but the research phase established no edit there is needed).

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Machine contention prevents the full gate from completing again (the exact failure of the research phase) | H | H | Phase 3 checks `uptime` before launching and runs the gate as a single backgrounded invocation with a generous timeout rather than a foreground call that a tool timeout can sever. Phase 4 triage treats a contention stall as "retry when quieter", never as a reason to weaken anything. |
| A concurrent agent session mutates `verify-refactor.sh` or `run-oracle-suite.sh` mid-plan | H | L | Phase 1 records the exact diff reviewed; Phase 5 re-checks `git diff` immediately before staging and stages only the two named files plus the task directory. |
| Collection counts drift again before the commit lands (another session adds oracle tests) | M | L | Step 3 fails loudly and names the remedy. Phase 4 branch (ii) re-derives the pins **once** from the gate's own Step 3 output as ground truth, never from a previously-recorded figure. |
| Pass 2 exceeds even 1800s under extreme load, producing a misleading TIMED OUT | M | L | The runner reports exit 124/137 distinctly from a normal failure. Phase 4 branch (i) classifies this as environmental and re-runs; the 1800s budget already carries ~930-1000s of slack over every measurement taken. |
| Temptation to "fix" a `TestGatingConclusiveScan` floor miss by lowering the floor | H | L | Explicit prohibition in Phase 4 branch (iii): a floor miss is a budget/performance signal per TESTING_GUIDE.md 8.8, never a license to lower a floor. Stop and report instead. |
| Committing partial/unverified work | M | L | Phase 5 depends on Phase 3 reaching `All checks passed`. If it does not, the task ends `[PARTIAL]` with the edits left uncommitted, exactly as the research phase left them. |

## Implementation Phases

**Dependency Analysis**:

| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4 | 3 |
| 5 | 5 | 3, 4 |

Phases within the same wave can execute in parallel. This plan is fully sequential: each phase
gates the next. Phase 4 is **conditional** — execute only if Phase 3 does not reach
`All checks passed`; otherwise mark it `[COMPLETED]` with a "not triggered" note and proceed.

---

### Phase 1: Validate the Existing Working-Tree Edits [COMPLETED]

**Goal**: Confirm the two uncommitted edits made during research are correct, complete, and
within the task's constraints — by review, not by re-making them.

**Tasks**:

- [ ] Run `git status --short` and `git diff -- oracle/run-oracle-suite.sh code/scripts/verify-refactor.sh`; capture the diff for the record.
- [ ] Confirm `oracle/run-oracle-suite.sh` sets `pass2_timeout="${ORACLE_PASS2_TIMEOUT:-1800}"` (was 900).
- [ ] Confirm `pass1_timeout` is **unchanged** at 1300 — only pass 2 was in scope.
- [ ] Confirm the original "Measured basis" comment block is preserved unedited, with the new "Recalibration" block added alongside it as historical record rather than replacing it.
- [ ] Confirm the Recalibration block records: the 10 -> 14 test population change, the three measurements (869.58s / 802.98s / 836.37s), the ~8% load spread, and the ~2x-of-measured convention that yields 1800s. This is the task's explicit precondition for option (a) being acceptable — the reasoning must be recorded, not just the value changed.
- [ ] Confirm `code/scripts/verify-refactor.sh` pins read exactly `BASELINE_ORACLE_COUNT=627`, `BASELINE_ORACLE_PARALLEL_COUNT=611`, `BASELINE_ORACLE_SERIAL_COUNT=14`, `BASELINE_ORACLE_SLOW_COUNT=2`. Verify the partition arithmetic: `611 + 14 + 2 = 627`.
- [ ] Confirm these are the **verified-current** values, not the task description's stale `606/590/14/2`. The description predates the 21-test addition; do not "correct" the pins back toward it.
- [ ] Confirm the re-pin provenance comment names both causes (the four-test `xdist_serial` relocation and the 21-test addition).
- [ ] **Constraint audit** — confirm the diff does NOT: relax or remove the Step 3 partition check; convert any exact-equality pin to a floor or inequality; change `BASELINE_FULL_COUNT`, `SELF_SCAN_SOLVE_TIMEOUT_MS`, `MIN_CONCLUSIVE_GATING_FORMULAS`, or `MIN_CONCLUSIVE_SCAN_FORMULAS`; or touch any Step 5 guard constant.
- [ ] Confirm no edit was made to `oracle/bimodal_logic/tests/test_oracle_interface.py` and that none is needed.
- [ ] Record any discrepancy found. If an edit is missing or wrong, make the minimal correction here — but the default expectation is zero changes in this phase.

**Timing**: 0.5 hours

**Depends on**: none

**Files to modify**:

- None expected. `oracle/run-oracle-suite.sh` and `code/scripts/verify-refactor.sh` are reviewed, not edited, unless the audit finds a discrepancy.

**Verification**:

- The diff contains exactly two changed files, both in `file_scope`.
- Every constraint-audit bullet above is confirmed negative (no prohibited change present).
- The 1800s value and all four pins match the research report's Decisions section exactly.

---

### Phase 2: Fast Pre-Gate Re-Confirmation [COMPLETED]

**Goal**: Cheaply re-confirm Steps 1-5 are green against the current working tree before
committing 60-90 minutes to the full run — and detect any drift introduced by concurrent
sessions since the research phase.

**Tasks**:

- [ ] Record `uptime` and a snapshot of competing processes (`ps aux --sort=-%cpu | head -15`) for the record.
- [ ] Run inside `nix develop`: `nix develop --command bash code/scripts/verify-refactor.sh --skip-oracle`, teeing output to `specs/143_decide_oracle_serial_pass_timeout_capacity/baselines/verify-refactor-skip-oracle.txt`.
- [ ] Confirm Step 3 reports `OK` on all four pinned values and on the partition check.
- [ ] Confirm Steps 1, 2, 4, 5 report `OK`. Step 4 is unrelated to this task's edits; if it stalls, that is the known contention signal — note it and proceed to Phase 3 rather than treating it as a defect.
- [ ] Confirm the run ends with `[verify-refactor] All checks passed` (Step 6 shows `SKIPPED (--skip-oracle)`, which is expected and is exactly why this phase does not close the verification gap).

**Timing**: 0.5 hours

**Depends on**: 1

**Files to modify**:

- `specs/143_decide_oracle_serial_pass_timeout_capacity/baselines/verify-refactor-skip-oracle.txt` - new transcript artifact

**Verification**:

- Transcript exists, is non-empty, and shows `OK` for oracle total 627, parallel 611, serial 14, slow 2, and the partition line.
- Any Step 3 mismatch here is a hard stop for Phase 3 — route to Phase 4 branch (ii) instead.

---

### Phase 3: Full End-to-End Gate Run [IN PROGRESS]

**Goal**: Close the task's single remaining verification gap — obtain
`[verify-refactor] All checks passed` from a complete run (Steps 1-7, no `--skip-oracle`), with
Step 6 exercising the new 1800s pass-2 timeout against the real 14-test serial population.

**Tasks**:

- [ ] Check `uptime` immediately before launching. Load average consistently at or below ~4 is the preferred window. If load is above ~8, wait for it to ease before launching rather than launching into a run likely to be curtailed — the research phase lost two attempts exactly this way.
- [ ] Record pre-run `uptime` and competing-process snapshot in the transcript.
- [ ] Launch the full gate as a **backgrounded, generously-timed** invocation so a tool timeout cannot sever it mid-Step-4 (the specific failure mode that killed the research phase's attempts): `nix develop --command bash code/scripts/verify-refactor.sh` with output teed to `specs/143_decide_oracle_serial_pass_timeout_capacity/baselines/verify-refactor-full-gate.txt` (overwriting the prior partial transcript).
- [ ] Poll for completion rather than blocking the whole allotment in a single foreground call.
- [ ] On completion, confirm the final line is `[verify-refactor] All checks passed`.
- [ ] Confirm Step 6 reports `OK: gating oracle suite green across both passes`.
- [ ] **Preserve the Step 6 evidence**: the runner writes the oracle suite's own output to the ephemeral `/tmp/verify-refactor-oracle.txt`. Copy it to `specs/143_decide_oracle_serial_pass_timeout_capacity/baselines/oracle-suite-step6.txt` before it is lost — this file contains the pass-2 wall clock, which is the only direct evidence the 1800s budget was exercised end-to-end.
- [ ] Extract the observed pass-2 wall clock and record it against the three prior measurements (869.58s / 802.98s / 836.37s) and against the 1800s budget. A figure in or near the 800-870s band confirms the research report's convergence finding and the headroom claim.
- [ ] Record post-run `uptime`.
- [ ] If the run does **not** reach `All checks passed`, do not retry blindly — proceed to Phase 4.

**Timing**: 2 hours (mostly wall-clock waiting; the gate itself runs ~35-60 minutes on a quiet
machine, longer under load)

**Depends on**: 2

**Files to modify**:

- `specs/143_decide_oracle_serial_pass_timeout_capacity/baselines/verify-refactor-full-gate.txt` - overwritten with the complete run
- `specs/143_decide_oracle_serial_pass_timeout_capacity/baselines/oracle-suite-step6.txt` - new, preserved Step 6 transcript

**Verification**:

- `verify-refactor-full-gate.txt` ends with `[verify-refactor] All checks passed`.
- Step 6 line reads `OK`, not `SKIPPED` and not `fail`.
- `oracle-suite-step6.txt` exists, is non-empty, and contains a pass-2 completion line with a
  wall clock below 1800s.

---

### Phase 4: Contingency Triage [IN PROGRESS]

**Goal**: If Phase 3 did not reach `All checks passed`, classify the failure correctly and take
the correct action — without weakening any budget, floor, or pin to force a green run.

Execute this phase **only** if Phase 3 failed or was curtailed. If Phase 3 succeeded, mark this
phase `[COMPLETED]` with the note "not triggered" and proceed to Phase 5.

**Tasks**:

- [ ] Classify the failure into exactly one branch below before taking any action.
- [ ] **Branch (i) — environmental contention** (Step 4 stall, pass-2 exit 124/137, a
      `TestGatingConclusiveScan` conclusiveness-floor miss, or any failure coinciding with high
      `uptime` load / competing processes). Action: record `uptime` and the competing processes,
      wait for a quieter window, and re-run Phase 3. The research report establishes the
      precedent — a Step 4 stall re-ran cleanly in 175.22s in isolation. **Prohibited**: widening
      any timeout, lowering `MIN_CONCLUSIVE_GATING_FORMULAS` / `MIN_CONCLUSIVE_SCAN_FORMULAS`, or
      lowering any floor to make a contended run pass. Cap retries at two; if a quiet window is
      not obtainable, stop and mark the task `[PARTIAL]` with the edits left uncommitted.
- [ ] **Branch (ii) — collection-count drift** (Step 3 fails because another change altered the
      oracle test population since the research phase). Action: re-derive all four values **once**
      from the gate's own Step 3 collection commands as ground truth — never from a
      previously-recorded figure — re-pin all four together, verify the partition invariant still
      holds, then re-run Phase 3. **Prohibited**: relaxing the partition check, converting any pin
      to a floor, or changing the pins to make an unexplained count pass. If the new counts cannot
      be explained by a specific identified change, treat as branch (iii).
- [ ] **Branch (iii) — genuine failure** (a real test failure, a regression, or a Step 5 guard
      violation traceable to this task's edits or to an unexplained change). Action: **stop**. Do
      not weaken anything. Record the failure with full transcript evidence, mark the task
      `[BLOCKED]` or `[PARTIAL]` with the diagnosis, and leave the two edits uncommitted for a
      follow-up dispatch.
- [ ] Record the branch taken, the evidence for the classification, and the action taken.

**Timing**: 1 hour (only if triggered)

**Depends on**: 3

**Files to modify**:

- `code/scripts/verify-refactor.sh` - only under branch (ii), and only to re-pin all four `BASELINE_ORACLE_*` values together
- Baseline transcripts under `specs/143_decide_oracle_serial_pass_timeout_capacity/baselines/` - additional retry evidence

**Verification**:

- The chosen branch is recorded with the evidence that justifies it.
- No prohibited change was made: `git diff` still shows the partition check intact, all pins as
  exact equalities, and no change to `SELF_SCAN_SOLVE_TIMEOUT_MS` or either
  `MIN_CONCLUSIVE_*` constant.
- Either Phase 3 has been re-run to `All checks passed`, or the task is explicitly marked
  `[PARTIAL]` / `[BLOCKED]` with the edits left uncommitted.

---

### Phase 5: Commit and Summarize [NOT STARTED]

**Goal**: Land the capacity decision and the re-pin as a properly scoped, fully verified commit,
with an implementation summary recording what was confirmed.

Execute only if Phase 3 (possibly via a Phase 4 retry) reached `All checks passed`.

**Tasks**:

- [ ] Re-check `git status --short` and `git diff` immediately before staging, to catch anything a concurrent session changed during the long gate run.
- [ ] Write `specs/143_decide_oracle_serial_pass_timeout_capacity/summaries/01_formalize-capacity-decision-summary.md` recording: the decision (option (a), 1800s) and where its reasoning lives; the re-pin to 627/611/14/2 and both causes; the observed Step 6 pass-2 wall clock versus the three prior measurements and the 1800s budget; and explicit confirmation that the previously-open Step 6 gap is now closed.
- [ ] Stage **only**: `oracle/run-oracle-suite.sh`, `code/scripts/verify-refactor.sh`, and `specs/143_decide_oracle_serial_pass_timeout_capacity/` (plus `specs/state.json` and `specs/TODO.md` if status postflight updates them). Never `git add -A` and never `git commit -am` — the working tree contains unrelated concurrent-session changes (`specs/142_.../plans/01_*.md`, `specs/events.jsonl`, `specs/.orchestrator-multi-state.json`) that must not be swept in.
- [ ] Review `git diff --staged` before committing to confirm no unrelated file was captured.
- [ ] Commit as `task 143: complete implementation` with `Session: sess_1786394927_a65984_143` in the body.
- [ ] Do not push and do not create a PR.

**Timing**: 0.5 hours

**Depends on**: 3, 4

**Files to modify**:

- `specs/143_decide_oracle_serial_pass_timeout_capacity/summaries/01_formalize-capacity-decision-summary.md` - new summary artifact

**Verification**:

- `git diff --staged --name-only` lists only the files enumerated above.
- `git log -1` shows the task-scoped message with the session ID.
- `git status --short` still shows the unrelated concurrent-session files as uncommitted.

---

## Testing & Validation

- [ ] `nix develop --command bash code/scripts/verify-refactor.sh --skip-oracle` ends with `All checks passed` (Phase 2).
- [ ] `nix develop --command bash code/scripts/verify-refactor.sh` (full, no skip) ends with `[verify-refactor] All checks passed` (Phase 3) — the definition of done.
- [ ] Step 3 reports `OK` for oracle total 627, gating-parallel 611, xdist_serial 14, slow 2, and the partition line `611 + 14 + 2 = 627`.
- [ ] Step 6 reports `OK: gating oracle suite green across both passes` — the first end-to-end exercise of the 1800s pass-2 timeout.
- [ ] Observed pass-2 wall clock is recorded and falls comfortably below 1800s (expected 800-870s band).
- [ ] `git diff` confirms the Step 3 partition check, the exact-equality pin semantics, `SELF_SCAN_SOLVE_TIMEOUT_MS`, `MIN_CONCLUSIVE_GATING_FORMULAS`, and `MIN_CONCLUSIVE_SCAN_FORMULAS` are all untouched.
- [ ] `pass1_timeout` remains 1300.

## Artifacts & Outputs

- `specs/143_decide_oracle_serial_pass_timeout_capacity/plans/01_formalize-capacity-decision.md` (this file)
- `specs/143_decide_oracle_serial_pass_timeout_capacity/baselines/verify-refactor-skip-oracle.txt` (Phase 2 transcript)
- `specs/143_decide_oracle_serial_pass_timeout_capacity/baselines/verify-refactor-full-gate.txt` (Phase 3 complete-run transcript, overwrites the prior partial)
- `specs/143_decide_oracle_serial_pass_timeout_capacity/baselines/oracle-suite-step6.txt` (Phase 3 preserved Step 6 oracle transcript — the pass-2 wall-clock evidence)
- `specs/143_decide_oracle_serial_pass_timeout_capacity/summaries/01_formalize-capacity-decision-summary.md` (Phase 5)
- Committed: `oracle/run-oracle-suite.sh` (1800s + Recalibration comment), `code/scripts/verify-refactor.sh` (627/611/14/2 + provenance comment)

## Rollback/Contingency

Phase 4 is the in-plan contingency for a failing gate. Beyond it:

- **The edits are uncommitted until Phase 5.** The natural rollback at any point before the
  commit is to leave them uncommitted — exactly the state the research phase left them in. No
  revert is needed and none should be performed, since the working-tree edits are the task's
  substantive output.
- **Never** run `git checkout --`, `git restore`, `git reset --hard`, or `git clean -fd` against
  these files. The working tree is dirty with concurrent-session changes and these edits are not
  recoverable from git history. If a snapshot is genuinely required, use
  `bash .claude/scripts/git-snapshot.sh` first.
- **If the commit lands and a later regression is traced to it**: revert the single commit. The
  1800s -> 900s and 627/611/14/2 -> 606/594/10/2 restoration is fully contained in it. Note that
  reverting the pins would immediately re-fail Step 3, since the collection counts are genuinely
  627/611/14/2 — a revert of the pin change is only correct alongside a revert of whatever
  changed the test population.
- **Never weaken to force green**: no timeout widening beyond the recorded 1800s decision, no
  floor lowering, no partition-check relaxation, no conversion of exact-equality pins to floors.
  A failing gate that cannot be explained is a `[BLOCKED]` outcome, not a tuning exercise.
