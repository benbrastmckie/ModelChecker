# Implementation Plan: Close the oracle gating conclusive-population diagnosis

- **Task**: 180 - Diagnose oracle conclusive-population shortfall (`unstable-watch`, 2026-08-27 -> 2026-09-01)
- **Status**: [IMPLEMENTING]
- **Effort**: 3.5 hours
- **Dependencies**: None
- **Research Inputs**: `specs/180_diagnose_oracle_conclusive_population_shortfall/reports/01_gating-conclusive-shortfall-diagnosis.md`
- **Artifacts**: plans/01_close-diagnosis-record-gaps.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md, no-task-references-in-deliverables.md
- **Type**: python
- **Lean Intent**: false

## Overview

The diagnosis is complete and is this task's primary deliverable; it is already written to
`reports/01_gating-conclusive-shortfall-diagnosis.md`. What remains is not investigation but
**record-keeping and one bounded observability fix**: the marker's own source-site entry-criteria
comment block (which TESTING_GUIDE.md section 8.9 designates as the source of truth for this
quarantine, explicitly *not* duplicated in the guide) currently contains a materially false
sub-claim and does not record either the newly-closed axiom avenue or the classifier/stale-checkout
finding. Closing this task means bringing that record into agreement with the diagnosis, wiring the
one piece of observability whose absence is the stated reason the diagnosis could not answer its own
question (a), and allocating the discriminating follow-up as a real task.

This plan deliberately does **not** plan the remediation. No budget constant, no floor, no
assertion, no marker, and no semantics change anywhere in it.

### Research Integration

Findings carried forward verbatim, not re-derived:

- All six `unstable-watch` failures (33091941820, 33193518591, 33250263772, 33306220265,
  33386925098, 33494135668) ran against `origin/master` frozen at `98d3ad8d`. `f9cc081e`
  (Skolemized Seriality/Interpolation) is not an ancestor of `98d3ad8d`, so the axioms were
  structurally absent from every process that produced those failures. **Scoped to those six runs
  only — explicitly not a claim about HEAD.**
- The `DISAGREEMENT_SIGNATURE` laundering-guard bug (bare substring `"Self-comparison produced"`)
  forced `classify()` to return `NEW` on every one of the six. Fixed in `cfb9cb4a`, which postdates
  `98d3ad8d` and so has never executed in CI. Under the fixed classifier all six are `TIMING`.
- Actual per-run spread: 96-98/103 conclusive, 5-7 timeouts, 749.10-898.78s — **not** the "identical
  96/103, 7-timeout" figure the source comment's "(3b)" paragraph currently asserts.
- Completed local run at axiom-bearing `HEAD=9ce3b4ad`: `conclusive=93/103, timeout_count=10,
  disagreements=0`, 951.21s, on a host with load ~5.9 -> ~4.8 on 24 cores and 7.3GB swap in use.
  Contention and genuine axiom cost both remain live and undiscriminated.
- Per-formula timeout identities are not recoverable from the test's current output because its
  `_generate_differential_report` call site passes none of the
  `progress_path`/`heartbeat_every`/`artifact_dir` instrumentation.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md consulted for this task (`roadmap_flag` not set).

### Scope judgment on the instrumentation gap (stated, per the dispatch's instruction)

**Verdict: in scope, under tight bounds.** The reasoning, so a reviewer can disagree with it
concretely:

1. It is not remediation. Remediation here means making the shortfall smaller or the test pass.
   Opt-in, off-by-default observability moves nothing toward green: the same formulas time out, the
   same floor fails, the same assertion fires with the same message. It changes only whether the
   failure is *legible*.
2. This task asked the question and could not answer it. Report section (a) is a recorded "not
   recoverable". Leaving the instrumentation unwired means the discriminating follow-up allocated in
   Phase 4 will hit the identical wall — the diagnosis would hand its successor the same blindness it
   was itself blocked by.
3. The marker's own record already nominates this as the next round. Criterion (3) ends: *"enabling
   that instrumentation is a possible future round, not attempted here."* This is that round.
4. The pattern already exists in the same file, same helper, same three parameters:
   `test_complexity_5_scan_self_consistent`'s `ORACLE_SCAN_OUT_DIR` wiring (Decision D2). This is a
   precedented one-line call-site change, not a new mechanism.
5. It is verifiable *here*, without a long run: the wiring is provable against the Z3-free
   `_StubOracle` in the existing gating-pass `TestScanInstrumentation` class.

The report's own "(b)" says wiring it "is remediation-shaped work regardless." That judgment was made
inside a dispatch instructed not to start a second multi-hundred-second run, and it conflates *wiring
the instrumentation* with *running the measurement*. This plan takes the first and refuses the second:
no scan is run for timing evidence in any phase.

## Goals & Non-Goals

**Goals**:
- Bring the `GATING_RECHECK_SOLVE_TIMEOUT_MS` entry-criteria record into factual agreement with the
  diagnosis: the closed axiom avenue, the true per-run spread, the classifier/stale-checkout cause of
  the six `NEW` misclassifications, and the axiom-bearing local data point with its caveat.
- Implement TESTING_GUIDE.md 8.9's answer as the report derived it: **do not** rewrite the documented
  signature, **do** annotate that it was last confirmed against pre-axiom code.
- Make per-formula timeout identities recoverable on any future run of the gating test, opt-in and
  off by default.
- Allocate the discriminating follow-up (report items 0a / 1 / 2) as a real, specified task.

**Non-Goals**:
- Any change to bimodal semantics or its frame-class constraints.
- Any change to the oracle soundness core or the unconditional-gating property.
- Any change to `GATING_RECHECK_SOLVE_TIMEOUT_MS` (stays 40000) or
  `MIN_CONCLUSIVE_GATING_FORMULAS` (stays 100).
- De-quarantining or re-quarantining the test.
- Running the gating scan for timing evidence. Two other implementation agents are active on this
  24-core host; any wall clock measured now is worthless as evidence and must not be recorded as if
  it were.
- Remediating the shortfall itself.

## Hard Constraints (binding on every phase)

| # | Constraint | Checked in |
|---|---|---|
| C1 | Do NOT widen `GATING_RECHECK_SOLVE_TIMEOUT_MS` | Phase 5 diff gate |
| C2 | Do NOT lower `MIN_CONCLUSIVE_GATING_FORMULAS` | Phase 5 diff gate |
| C3 | Do NOT weaken, skip, or delete any assertion in `_assert_scan_report` or its call sites | Phase 5 diff gate |
| C4 | Do NOT add, remove, or move `@pytest.mark.unstable` / `@pytest.mark.xdist_serial` | Phase 5 diff gate |
| C5 | Do NOT touch `oracle/bimodal_logic/provider.py`, `translation.py`, `errors.py`, the persisted manifest, or `code/src/model_checker/theory_lib/bimodal/**` | Phase 5 diff gate |
| C6 | New prose in files outside `specs/**` must cite commits, run IDs, and dates — **never task numbers** (`.claude/rules/no-task-references-in-deliverables.md`; a blocking write-time hook enforces this) | Phases 1-4 |
| C7 | No claim may be recorded that the axioms are excluded at HEAD. The exclusion is scoped to the six CI runs at `98d3ad8d` | Phases 1-2 |

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| New comment prose trips the task-reference hook and blocks the write | L | M | C6: write commit SHAs / run IDs / ISO dates only. Draft, then `bash .claude/scripts/check-task-references.sh` before committing |
| The instrumentation wiring changes default behaviour of a `unstable`-marked gating test | H | L | Env var unset => all three params keep their defaults; proven by an extension of `TestScanInstrumentation::test_default_params_produce_no_files`'s technique against the extracted helper |
| Reusing `ORACLE_SCAN_OUT_DIR` makes two tests clobber one another's `report.json`/`SCAN_COMPLETE` | M | M | Use a distinct `ORACLE_GATING_SCAN_OUT_DIR`; add a test asserting the two names are independent |
| Refactoring the existing `slow`-marked D2 call site breaks it undetectably (it cannot be run in this dispatch) | M | M | Do NOT touch that call site. Add the helper and use it at the gating site only; record the deliberate duplication in a comment |
| Correcting "(3b)" is read as reopening the closed `xdist_serial` lead | M | L | Preserve "(3b)"'s existing closure language verbatim; correct only the counts and add the classify-verdict record |
| Scope creep into remediation | H | M | Non-Goals + the Phase 5 diff gate; Phase 4 explicitly forbids creating a shortfall-remediation task |

## Implementation Phases

**Dependency Analysis**:

| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 4 | -- |
| 2 | 2, 3 | 1 |
| 3 | 5 | 1, 2, 3, 4 |

Phases within the same wave can execute in parallel. Phases 2 and 3 both follow Phase 1 because both
touch text Phase 1 rewrites (Phase 2 points at it; Phase 3 amends criterion (3)'s closing sentence).

---

### Phase 1: Correct and extend the marker's entry-criteria record [COMPLETED]

**Goal**: Make the `GATING_RECHECK_SOLVE_TIMEOUT_MS` comment block in
`oracle/bimodal_logic/tests/test_cross_oracle_differential.py` (roughly lines 97-234) agree with the
diagnosis. This block, not TESTING_GUIDE.md, is 8.9's designated source of truth for this quarantine,
so every substantive finding lands here.

**Tasks**:
- [x] Extend criterion **(3) GENUINE FIX ATTEMPTED AND ITS FAILURE RECORDED** with the newly closed
      avenue: the Skolemized Seriality/Interpolation frame axioms (`f9cc081e`, authored
      2026-08-31) are ruled out as a cause of the 2026-08-27 -> 2026-09-01 `unstable-watch`
      failures, because `git merge-base --is-ancestor f9cc081e 98d3ad8d` fails and all six runs
      checked out `98d3ad8d`. State the exclusion's scope explicitly (C7): these six runs only, not
      HEAD. Follow the block's existing convention of recording *why* an avenue is closed so a future
      reader does not re-open it.
- [x] Correct the false claim in **(3b)**. It currently asserts the five listed runs "reproduced the
      identical 96/103 conclusive, 7-timeout, 0-disagreement result". Replace with the real per-run
      figures and add the sixth run:

      | Date (UTC) | Run ID | Conclusive | Timeouts | Duration (s) |
      |---|---|---|---|---|
      | 2026-08-27 | 33091941820 | 98/103 | 5 | 761.61 |
      | 2026-08-28 | 33193518591 | 96/103 | 7 | 824.89 |
      | 2026-08-29 | 33250263772 | 98/103 | 5 | 749.10 |
      | 2026-08-30 | 33306220265 | 96/103 | 7 | 898.78 |
      | 2026-08-31 | 33386925098 | 96/103 | 7 | 808.64 |
      | 2026-09-01 | 33494135668 | 97/103 | 6 | 788.74 |

      Preserve every existing sentence that closes the `xdist_serial` lead — the correction is to the
      counts, not to the conclusion drawn from them.
- [x] Record in **(3b)** why the promotion streak reset on each of those six nights, which nothing in
      the block currently explains: `origin/master` was frozen at `98d3ad8d` for roughly five days, so
      every run executed a classifier whose `DISAGREEMENT_SIGNATURE` was a bare substring
      (`"Self-comparison produced"`). Because `_assert_scan_report`'s two asserts fire in sequence and
      pytest's traceback embeds the first (passing) assert's *unrendered* f-string source when the
      second fails, that substring appears in the failure text of every floor-only failure, laundering
      it into a false disagreement signal and forcing `NEW`. Fixed in `cfb9cb4a` (2026-08-31), which
      is not an ancestor of `98d3ad8d` and has therefore never executed in CI. All six runs classify
      `TIMING` under the fixed classifier. This is a measurement-mechanism artifact, not a behaviour
      change in the test.
- [x] Add the axiom-bearing local data point to the block, with its caveat stated in the same
      sentence rather than in a footnote: at `HEAD=9ce3b4ad` (which does contain `f9cc081e`),
      `agreements=93 disagreements=0 timeout_count=10 conclusive=93/103`, 951.21s — worse on both axes
      than every one of the six CI runs, but measured on a host with load ~5.9 -> ~4.8 across 24 cores
      and 7.3GB of swap in use, i.e. demonstrably not idle. Record both live explanations (axiom cost;
      host contention) without collapsing them, and state the discriminating observation (same HEAD on
      a verifiably idle CI-class runner, or `98d3ad8d` under comparable local contention).
- [x] Add the one sentence the report's (d) calls for: the documented 96/103-class signature was last
      confirmed against **pre-axiom** code, so the first post-axiom real CI run must be checked against
      it explicitly rather than assumed to still hold.
- [x] Verify then correct the stale function reference in criterion **(4)**: it cites
      `compute_promotion_streak`, but `.github/scripts/unstable_watch_classify.py` also defines
      `compute_per_test_promotion_streak`, which TESTING_GUIDE.md 8.9 describes as the function that
      now drives promotion (the legacy per-run streak being retained only as a job-level upper bound).
      Confirm both definitions and 8.9's description before editing; if confirmed, point (4) at the
      per-node-id function. If the confirmation does not hold, leave (4) unchanged and say so.
- [x] Re-read the edited block end to end and confirm no task number was introduced (C6).

**Timing**: 0.75 hours

**Depends on**: none

**Verification Tier**: local

**Scope Hypothesis**: the comment block is asserted to span roughly lines 97-234 of
`oracle/bimodal_logic/tests/test_cross_oracle_differential.py`, with criteria (3), (3b), and (4) at
roughly 187, 208, and 226. Confirm by locating the `GATING_RECHECK_SOLVE_TIMEOUT_MS = 40000`
assignment and reading upward to the preceding non-comment line; do not trust these numbers as fact.

**Files to modify**:
- `oracle/bimodal_logic/tests/test_cross_oracle_differential.py` — comment text only, within the
  `GATING_RECHECK_SOLVE_TIMEOUT_MS` block. No executable line changes in this phase.

**Verification**:
- `git diff -U0 oracle/bimodal_logic/tests/test_cross_oracle_differential.py` shows only comment
  lines (`#`-prefixed) added or changed — zero executable-statement changes.
- `PYTHONPATH=code/src python3 -m pytest oracle/bimodal_logic/tests/test_cross_oracle_differential.py --collect-only -q` succeeds (proves no syntax break).
- `PYTHONPATH=code/src python3 -m pytest oracle/bimodal_logic/tests/test_cross_oracle_differential.py -m "not slow and not unstable" -q` passes.
- `bash .claude/scripts/check-task-references.sh` reports no new violation.
- Grep confirms `GATING_RECHECK_SOLVE_TIMEOUT_MS = 40000` and
  `MIN_CONCLUSIVE_GATING_FORMULAS = 100` are unchanged (C1, C2).

---

### Phase 2: Annotate TESTING_GUIDE.md 8.9's "Currently marked" entry [COMPLETED]

**Goal**: Implement the report's (d) answer in the guide — *the documented signature and the
entry/exit criteria are not rewritten* — while adding the single forward-looking caveat, and keeping
the guide's own "each marker's source-site comment block is the source of truth; neither record is
duplicated here" discipline intact.

**Tasks**:
- [x] In section 8.9's **Currently marked** bullet for
      `TestGatingConclusiveScan::test_known_conclusive_population_self_consistent`, add a short clause
      noting that the recorded signature was last confirmed against pre-axiom code and that the first
      post-axiom real CI run must be checked against it explicitly. Keep it pointer-shaped: the
      numbers live in the source-site block (Phase 1), not here.
- [x] Do **not** alter 8.9's entry criteria, exit criteria, the 20-run default, the standing rule, or
      the deselection wiring paragraph. Confirm by diff that none of these changed.
- [x] Record the standing-rule justification for keeping the quarantine, as a pointer rather than a
      restatement: the marking dates to `25eadae8` (2026-08-25), roughly one week old, well inside
      8.9's two-review-cycle window, and the rule's joint "no active repair work in progress"
      condition is not met — repair work is live and partially landed (`cfb9cb4a`; the closed 2x
      budget-widening avenue; the closed `xdist_serial` avenue; the axiom avenue closed in Phase 1).
      Neither de-quarantining nor re-quarantining is recommended (C4).
- [x] Confirm the classifier lesson from `cfb9cb4a` needs no new guide text: 8.9's "The classifier
      lives in an importable module, not YAML" paragraph already documents the rendered-text /
      bare-substring guard rule and the sequential-assert source-listing mechanism. If it does, record
      that finding in the summary and add nothing. Do not duplicate it.
- [x] Confirm no task number was introduced (C6).

**Timing**: 0.25 hours

**Depends on**: 1

**Verification Tier**: prose

**Files to modify**:
- `code/docs/core/TESTING_GUIDE.md` — section 8.9 "Currently marked" bullet only.

**Verification**:
- `git diff code/docs/core/TESTING_GUIDE.md` is confined to the one bullet; the four entry criteria,
  the exit-criteria paragraph, and the standing-rule paragraph are byte-identical.
- `PYTHONPATH=code/src python3 -m pytest code/tests/ci/test_unstable_deselection_wiring.py code/tests/ci/test_unstable_watch_classifier.py -q` passes.
- `bash .claude/scripts/check-task-references.sh` reports no new violation.

---

### Phase 3: Wire opt-in per-formula instrumentation into the gating test [COMPLETED]

**Goal**: Make the timed-out formulas' identities recoverable on any future run of
`test_known_conclusive_population_self_consistent`, without changing its behaviour when the opt-in is
not requested. This closes the gap that made report section (a) unanswerable.

**Tasks**:
- [x] Add a module-level helper next to the existing instrumentation code, e.g.
      `_resolve_scan_instrumentation(env_var_name)`, returning
      `(artifact_dir, progress_path, heartbeat_every)`: when the named environment variable is unset or
      empty, return `(None, None, 0)` — exactly the three parameter defaults; when set, return
      `(Path(value), Path(value) / "progress.jsonl", 10)`, mirroring
      `test_complexity_5_scan_self_consistent`'s Decision D2 block verbatim in behaviour.
- [x] Wire it into `test_known_conclusive_population_self_consistent`'s
      `_generate_differential_report(...)` call using the env var **`ORACLE_GATING_SCAN_OUT_DIR`** —
      deliberately distinct from `ORACLE_SCAN_OUT_DIR`, so that
      `oracle/run-oracle-exhaustive-scan.sh` (which sets `ORACLE_SCAN_OUT_DIR` before invoking
      `pytest oracle -m slow -s`) can never cause two tests to write the same `report.json` /
      `SCAN_COMPLETE`.
- [x] Leave `test_complexity_5_scan_self_consistent`'s existing D2 block **unchanged**. It is
      `slow`-marked and cannot be exercised in this dispatch, so refactoring it would be an unverified
      change to working code. Record the deliberate duplication in a one-line comment at the helper so
      a future reader does not "clean it up" blindly.
- [x] Add a docstring paragraph to `test_known_conclusive_population_self_consistent` in the same
      shape as D2's: what the env var does, that unset means byte-identical prior behaviour, and that
      it exists so a future observer can identify *which* formulas time out — the question the
      2026-08-27 -> 2026-09-01 investigation could not answer.
- [x] Amend criterion (3)'s closing sentence (edited in Phase 1) from "enabling that instrumentation
      is a possible future round, not attempted here" to record that it is now enabled, opt-in, behind
      `ORACLE_GATING_SCAN_OUT_DIR`, and how to use it. Keep the surrounding "do not assert a same-7
      claim" language intact.
- [x] Add tests in the Z3-free style of `TestScanInstrumentation` (stub oracle, gating pass, fast):
      - unset / empty env var yields `(None, None, 0)`;
      - set env var yields the artifact dir, a `progress.jsonl` under it, and a non-zero heartbeat;
      - `ORACLE_GATING_SCAN_OUT_DIR` and `ORACLE_SCAN_OUT_DIR` resolve independently — setting one
        does not affect resolution of the other;
      - with the env var unset, `_generate_differential_report` driven through the helper's return
        values writes no files (the `test_default_params_produce_no_files` technique).
- [x] Verify no change to the `_assert_scan_report(report, min_conclusive=MIN_CONCLUSIVE_GATING_FORMULAS)`
      call, to `_assert_scan_report` itself, or to either constant (C1, C2, C3).

**Timing**: 1.5 hours

**Depends on**: 1

**Verification Tier**: full

**Scope Hypothesis**: this phase asserts the change is confined to one file, that `os` and `Path` are
already imported (observed at lines 44 and 47), that the D2 pattern sits at roughly lines 2610-2623,
and that the gating call site sits at roughly lines 2457-2468. Confirm each by reading the file before
editing; if the helper turns out to need an import or a second file, stop and record that rather than
widening silently.

**Files to modify**:
- `oracle/bimodal_logic/tests/test_cross_oracle_differential.py` — new helper, one call site, one
  docstring, criterion (3)'s closing sentence, and new tests in/beside `TestScanInstrumentation`.

**Verification**:
- New tests pass:
  `PYTHONPATH=code/src python3 -m pytest oracle/bimodal_logic/tests/test_cross_oracle_differential.py -m "not slow and not unstable" -q`.
- `git diff` shows the gating test's body changed only by threading the three already-existing
  keyword parameters; `_assert_scan_report`'s call is character-identical.
- With `ORACLE_GATING_SCAN_OUT_DIR` unset, the gating test collects and its non-Z3 sibling tests pass
  — no file appears anywhere.
- `grep -c "ORACLE_SCAN_OUT_DIR" oracle/bimodal_logic/tests/test_cross_oracle_differential.py` and
  `oracle/run-oracle-exhaustive-scan.sh` confirm the existing exhaustive wiring is untouched.
- The long gating scan is **not** run. Confirming the wiring end-to-end on a real scan belongs to the
  follow-on task created in Phase 4; this host is contended and any timing observed here would be
  worthless (see Non-Goals).

---

### Phase 4: Allocate the discriminating follow-up as a specified task [COMPLETED]

**Goal**: Turn the report's open items 0a, 1, and 2 into one properly specified task, so the named
follow-up is tracked rather than left in a report section.

**Tasks**:
- [x] Create **one** task, not three. Items 1 (confirm `cfb9cb4a` reaches a real `unstable-watch` run
      and classifies `TIMING`), 2 (re-measure at axiom-bearing HEAD on an uncontended runner), and 0a
      (discriminate axiom cost from host contention) all resolve on the same next observations of the
      same test and would otherwise block on each other. State that consolidation rationale in the
      task description.
- [x] Write the description to be self-contained — a future reader must not need this report to act.
      It must carry: the six run IDs and their real counts; that `origin/master` was frozen at
      `98d3ad8d` and has since caught up; that `cfb9cb4a` has never executed in CI; the local
      `HEAD=9ce3b4ad` data point (93/103, 10 timeouts, 951.21s) with its non-idle-host caveat; the two
      undiscriminated explanations; and the two discriminating observations named in the report (same
      HEAD on a verifiably idle CI-class runner, or `98d3ad8d` under comparable local contention).
- [x] Carry the hard constraints into the new task's description verbatim: do not widen
      `GATING_RECHECK_SOLVE_TIMEOUT_MS`; do not lower `MIN_CONCLUSIVE_GATING_FORMULAS`; do not weaken,
      skip, or delete the assertion; do not de-quarantine or re-quarantine as the primary remedy; do
      not change bimodal semantics or the oracle soundness core.
- [x] Note in the description that `ORACLE_GATING_SCAN_OUT_DIR` (Phase 3) now exists and should be
      used, so the per-formula timeout set is captured on the first observation rather than lost again.
- [x] Do **not** create a task to remediate the shortfall itself. 8.9's escalation trigger has not
      fired: the marking is ~1 week old and active repair work is in progress. Creating a remediation
      task now would pre-empt the observation that decides whether one is warranted.
- [x] Allocate the number safely. Two other implementation agents are active in this session, so take
      the commit/scope lock before touching `specs/state.json`:
      `bash .claude/scripts/task-lock.sh scope-acquire "$session_id"`, then read
      `.next_project_number`, append the `active_projects` entry (`project_number`, `project_name`,
      `status: "not_started"`, `task_type: "python"`, `description`, `topic`, `created`,
      `last_updated`), increment `next_project_number`, release the lock, and run
      `bash .claude/scripts/generate-todo.sh`. Never assign a number by guessing.
- [x] Cross-reference the new task number back into
      `reports/01_gating-conclusive-shortfall-diagnosis.md`'s "What remains open" section (inside
      `specs/**`, so task numbers are permitted there — C6 does not apply).

**Timing**: 0.5 hours

**Depends on**: none

**Verification Tier**: local

**Scope Hypothesis**: `specs/state.json` is asserted to expose `next_project_number` at the top level
and per-task entries keyed `project_number` (observed: `next_project_number` is 183 at plan time, and
entries use `project_number`/`project_name`/`status`/`task_type`). Re-read the file at implementation
time; the number will have moved if a sibling agent allocated one first.

**Files to modify**:
- `specs/state.json` — one appended entry, `next_project_number` incremented.
- `specs/TODO.md` — regenerated, never hand-edited.
- `specs/180_diagnose_oracle_conclusive_population_shortfall/reports/01_gating-conclusive-shortfall-diagnosis.md`
  — one cross-reference line.

**Verification**:
- `jq '.next_project_number' specs/state.json` is exactly one greater than its pre-phase value, and
  `jq '[.active_projects[].project_number] | length'` grew by exactly one.
- `jq -e '.active_projects[] | select(.project_number == <new>) | .description | test("33494135668") and test("cfb9cb4a") and test("9ce3b4ad")' specs/state.json` succeeds.
- The new entry appears in `specs/TODO.md` after regeneration.
- No lock file is left behind (`bash .claude/scripts/task-lock.sh check <new>`).

---

### Phase 5: Closure gate [NOT STARTED]

**Goal**: Prove mechanically that the hard constraints held and that nothing outside the intended
surface changed, then close the task.

**Tasks**:
- [ ] Run the full fast gate:
      `PYTHONPATH=code/src python3 -m pytest oracle/bimodal_logic/tests/ -m "not slow and not unstable" -q`
      and
      `PYTHONPATH=code/src python3 -m pytest code/tests/ci/ -q`.
- [ ] Constraint diff gate over `git diff` for the whole task, asserting each explicitly:
      - `GATING_RECHECK_SOLVE_TIMEOUT_MS = 40000` unchanged (C1);
      - `MIN_CONCLUSIVE_GATING_FORMULAS = 100` unchanged (C2);
      - no line inside `_assert_scan_report` changed, and no `assert` statement anywhere in
        `oracle/` was removed, negated, or given a `pytest.skip`/`xfail` (C3);
      - `@pytest.mark.unstable` and `@pytest.mark.xdist_serial` occurrences are unchanged in count and
        location (C4);
      - `git diff --name-only` lists no file under `oracle/bimodal_logic/` other than
        `tests/test_cross_oracle_differential.py`, and nothing under
        `code/src/model_checker/theory_lib/bimodal/` (C5).
- [ ] `bash .claude/scripts/check-task-references.sh` clean (C6).
- [ ] Re-read the two edited prose regions once as a hostile reader: does any sentence claim the
      axioms are excluded at HEAD? If so, fix it (C7).
- [ ] Write the execution summary to
      `specs/180_diagnose_oracle_conclusive_population_shortfall/summaries/01_close-diagnosis-record-gaps-summary.md`,
      recording the scope judgment on the instrumentation gap and the follow-on task number.

**Timing**: 0.5 hours

**Depends on**: 1, 2, 3, 4

**Verification Tier**: full

**Files to modify**:
- `specs/180_diagnose_oracle_conclusive_population_shortfall/summaries/01_close-diagnosis-record-gaps-summary.md` (new).

**Verification**:
- Both pytest invocations exit 0.
- Every C1-C7 check above produces an explicit pass, recorded in the summary. A constraint that was
  "not checked" is a failed gate, not a silent pass.

---

## Testing & Validation

- [ ] `PYTHONPATH=code/src python3 -m pytest oracle/bimodal_logic/tests/test_cross_oracle_differential.py -m "not slow and not unstable" -q` passes (includes the new instrumentation tests).
- [ ] `PYTHONPATH=code/src python3 -m pytest oracle/bimodal_logic/tests/ -m "not slow and not unstable" -q` passes.
- [ ] `PYTHONPATH=code/src python3 -m pytest code/tests/ci/ -q` passes — in particular
      `test_unstable_deselection_wiring.py` and the 43 `test_unstable_watch_classifier.py` tests.
- [ ] With `ORACLE_GATING_SCAN_OUT_DIR` unset, no instrumentation file is produced anywhere.
- [ ] `bash .claude/scripts/check-task-references.sh` reports no new violation.
- [ ] The C1-C7 diff gate in Phase 5 passes on every item.
- [ ] The `unstable`-marked gating scan is **not** executed for timing evidence at any point.

## Artifacts & Outputs

- `oracle/bimodal_logic/tests/test_cross_oracle_differential.py` — corrected and extended
  entry-criteria record; new `_resolve_scan_instrumentation` helper; opt-in
  `ORACLE_GATING_SCAN_OUT_DIR` wiring at the gating call site; new Z3-free instrumentation tests.
- `code/docs/core/TESTING_GUIDE.md` — one annotated bullet in section 8.9's "Currently marked".
- `specs/state.json`, `specs/TODO.md` — one new follow-on task.
- `specs/180_diagnose_oracle_conclusive_population_shortfall/reports/01_gating-conclusive-shortfall-diagnosis.md`
  — follow-on task cross-reference.
- `specs/180_diagnose_oracle_conclusive_population_shortfall/summaries/01_close-diagnosis-record-gaps-summary.md`
  — execution summary.

## Rollback/Contingency

Every phase is independently revertible and none changes runtime behaviour of any gating assertion.

- Phases 1 and 2 are comment/prose only — `git revert` or `git checkout` of the two files restores the
  prior record exactly. No test outcome depends on them.
- Phase 3 is the only executable change. If its new tests do not go green, or if any doubt arises about
  default-path behaviour, revert the helper and the call-site wiring (`git checkout` the file to the
  post-Phase-1 commit) and record the instrumentation gap as still open in the Phase 4 task's
  description. The task still closes: Phases 1, 2, and 4 are the record-keeping deliverables and do not
  depend on Phase 3.
- Phase 4's state mutation is undone by removing the appended `active_projects` entry, restoring
  `next_project_number`, and re-running `generate-todo.sh` under the scope lock.
- If any hard constraint C1-C7 is found violated at the Phase 5 gate, revert the offending phase rather
  than adjusting the constraint. No constraint in this plan is negotiable at implementation time.
