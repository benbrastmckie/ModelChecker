# Implementation Plan v2: Re-baseline the Gating Oracle Suite and Repair the Regression Gate

- **Task**: 127 - Complete the oracle differential-suite regression baseline that the core/theory_lib
  refactor could not finish
- **Status**: [IMPLEMENTING]
- **Effort**: ~6 hours agent time, plus ~2.5-4 hours unattended wall clock spread across three
  long runs (gating suite ~20-35 min, exhaustive scan ~60-90 min, final gate ~25-40 min), all of
  which require an otherwise-idle machine
- **Dependencies**: None outstanding. Task 126 depends on this one, not the reverse. The work that
  landed under tasks 133, 136, 137, 138, and 139 is a precondition and is already complete.
- **Research Inputs**:
  - `specs/127_close_oracle_suite_regression_baseline/reports/01_oracle-baseline-environment.md`
    (round 1; **largely superseded** — see "Research Integration")
  - Direct verification of the current working tree performed while writing this plan (every
    factual claim below was re-derived from the files, not carried over)
- **Artifacts**: `plans/02_rebaseline-gating-oracle-suite.md` (this file); supersedes
  `plans/01_close-oracle-regression-baseline.md`
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md,
  no-task-references-in-deliverables.md
- **Type**: python
- **Lean Intent**: false

## Overview

Plan v1 was written against an oracle suite that no longer exists. Since it ran, the suite has been
restructured (a fast **gating** path and a separate **exhaustive** path), grown from 550 to 606
tests, had its `find_countermodel` contract made three-valued, had its solve budgets grounded in
measurement, and had its strict-xfail accommodation replaced by ground-truth-adjudicated bucketing.
Two of the three hard pins in `code/scripts/verify-refactor.sh` are now stale and will fail on
contact, and its Step 6 still invokes the pre-split, unfiltered pytest command that silently drags
the 60-90 minute exhaustive scan into every gating run.

This revision therefore has two halves that v1 did not separate:

1. **Produce the baseline.** Run the canonical gating suite via `oracle/run-oracle-suite.sh` under
   `nix develop`, on a verifiably quiet machine, into staging; triage every failure with a
   pre-declared rubric and a bounded isolated-re-run protocol; promote only on a defensible result.
2. **Repair the gate.** Re-pin the oracle collection count, re-scope the Step 5 accommodation guard
   from brittle line numbers onto the guard mechanism that actually exists today, and point Step 6
   at the gating runner instead of the unfiltered command.

Definition of done: `specs/126_refactor_repo_core_infrastructure_theory_lib/baselines/` records a
complete, triaged gating run (text + JUnit XML) and a completed exhaustive-scan record; the refactor
plan's Phase 2 reads `[COMPLETED]`; and `bash code/scripts/verify-refactor.sh` (no `--skip-oracle`)
exits 0 with Step 6 actually executing the gating suite — with **no assertion, budget, floor, or
guard weakened anywhere to get there**. If the suite legitimately cannot go green, Phase 3's
category (c) defines an honest recorded outcome instead, and the refactor plan stays `[PARTIAL]`
with its framing corrected rather than flipped.

### Research Integration

No new research report was produced for this round. The revision is driven by direct verification of
the working tree plus the completion records of the tasks that changed it. Each fact below was
checked against the file named, not inherited:

| Fact | Evidence |
|------|----------|
| `TEMPORAL_SOLVE_TIMEOUT_MS = 180000` is a named constant | `oracle/bimodal_logic/tests/test_oracle_interface.py:115` (with `ATEMPORAL_SOLVE_TIMEOUT_MS = 10000` at :116) |
| `find_countermodel` is three-valued; undecided solves raise `OracleTimeoutError` rather than reading as UNSAT | `test_oracle_interface.py:989` (`with pytest.raises(OracleTimeoutError)`), plus `specs/133_fix_oracle_self_consistency_disagreements/summaries/02_find-countermodel-contract-summary.md` |
| Oracle collection is **606**, not 550 | `pytest oracle --collect-only -q` → `606 tests collected`, reproduced under both the devShell interpreter and bare `python3` |
| Marker split: 594 gating-parallel + 10 `xdist_serial` + 2 `slow` = 606 | three `--collect-only -q -m ...` runs against `oracle` |
| `test_cross_oracle_differential.py` contains **zero** `xfail(` markers | `grep -c 'xfail(' …test_cross_oracle_differential.py` → `0` |
| The replacement guard is five ordered assertions in `test_temporal_only_agreement_complexity_5` | `test_cross_oracle_differential.py` lines 1399, 1406, 1419, 1436, 1454 (test defined at :1298); rationale at :1320-1326; `oracle/bimodal_logic/KNOWN_EXTERNAL_DEFECTS.md` |
| `baselines/serial-rebaseline/` exists and is empty | directory listing |
| The gating runner exists, hard-codes `-n 6` for pass 1, and **hard-fails** if xdist is unimportable | `oracle/run-oracle-suite.sh` (the `import xdist` preflight, the two `timeout --kill-after=60s` passes) |
| Gating runtime is ~16-24 min, not ~76 min | `specs/138_…/summaries/01_…-summary.md` (649.09s + 318.57s ≈ 16.1 min at the time), plus the runner's own header noting a further +127.96s pass-2 test (≈ 18.3 min), plus `specs/139_…/summaries/01_…-summary.md` citing "~24 min" |

**One correction to the revision brief.** The brief states that pytest-xdist is not installed and
that a **serial** run should be planned. That is half right and the wrong half is load-bearing:

- Correct: `python3 -c "import xdist"` fails with `ModuleNotFoundError` under the bare system
  interpreter (`/home/benjamin/.nix-profile/bin/python3`).
- Incorrect as a planning premise: inside `nix develop`, `import xdist` succeeds and reports
  **3.8.0** (interpreter `/nix/store/kykgmi6vxjzw76miazjf3yfn59kp7phd-python3-3.12.13-env`). The
  canonical gating runner requires xdist, refuses to run without it, and hard-codes `-n 6` for its
  parallel pass by deliberate design.

So this plan does **not** plan a serial whole-suite run. It runs the two-pass gating runner inside
the devShell, exactly as `code/docs/core/TESTING_GUIDE.md` section 8.8 specifies. Deviating to a
hand-rolled serial invocation would bypass the `xdist_serial` split, the calibrated per-pass
timeouts, and the marker deselects — i.e. it would produce a baseline of something other than what
the gate actually runs. The brief's underlying concern (v1's naive `-n 6` over the *whole* suite
manufactured five false failures) is real and is already solved upstream: the ten contention-
sensitive tests now carry `xdist_serial` and run in a dedicated non-parallel pass.

### Findings not in the revision brief

Two additional stale items were found while verifying, and both are in scope:

1. **Step 6 of `verify-refactor.sh` runs the wrong command entirely.** It invokes
   `PYTHONPATH=code/src python -m pytest oracle/bimodal_logic/tests/ -q` with no `-m` deselect. Since
   `oracle/` has no reachable ini file (see `oracle/conftest.py`'s docstring), nothing filters the
   two `slow`-marked tests, so Step 6 silently runs the exhaustive complexity≤5 sweep serially —
   the exact 60-90 minute cost the gating/exhaustive split was built to remove. It also uses
   `python` rather than `python3`, which does not exist on the bare `PATH` here. Re-pinning the
   count without fixing this leaves the gate unusable in practice.
2. **The oracle suite's `bimodal_harness` availability is order-dependent, not path-configured.**
   `test_cross_oracle_differential.py:1169-1171` inserts `/home/benjamin/Projects/BimodalHarness/src`
   into `sys.path` at import time, and alphabetical collection puts that file before
   `test_oracle_interface.py`, whose module-level `from bimodal_harness.oracle.protocol import …`
   (:37-38) would otherwise fail. Verified: a whole-suite `--collect-only` with only `code/src` on
   `PYTHONPATH` collects all 606, but `pytest oracle/bimodal_logic/tests/test_oracle_interface.py
   --collect-only` alone fails with `ModuleNotFoundError: No module named 'bimodal_harness'`.
   **Every isolated re-run in Phase 3 must therefore carry the sibling checkout on `PYTHONPATH`**
   (running inside `nix develop` does this automatically). Note also that the devShell exports the
   sibling as the *relative* path `../BimodalHarness/src`, so all commands must be issued with the
   repository root as the working directory.

### What is carried forward from v1, and what is discarded

**Carried forward (still correct, re-parameterized):**

- The staging-then-promote discipline: nothing is written into `baselines/` until a completeness
  check and the rubric both pass. A truncated or unjudged artifact never overwrites a committed one.
- The backgrounded-launch requirement: every timed run here exceeds the 600s foreground tool
  ceiling, so a foreground invocation is guaranteed to be killed and will look exactly like a
  contention kill.
- The three-way rubric shape (clean / contention artifact / genuine), with a *mandatory* isolated
  re-run rather than an assumption, and a hard prohibition on `xfail`/`skip`/`deselect`/budget
  widening to reach green.
- The quiet-machine preflight. This was never ceremony: contention was observed live during round-1
  research, and again during tasks 137, 138, and 139.
- The rollback posture and the `git show b40179c9:…` recovery path for the committed partial
  baseline.

**Discarded, with reasons:**

| Discarded from v1 | Why |
|---|---|
| The 550-test collection premise, everywhere it appears | Actual count is 606; the suite grew |
| The two-test "Category C contention flake watch list" | One entry (`test_all_sat_task_relation_ternary`) is fixed via the named 180s temporal budget; the other (`test_complexity_5_scan_self_consistent`) is now `slow`-marked and out of the gating path entirely. A pre-declared watch list is now actively misleading — Phase 3 adjudicates each failure on evidence instead |
| Phase 3's `[BLOCKED]` diagnosis (refactor-introduced semantic regression) | Wrong; it was a timeout-budget boundary flake, corrected by the named constant |
| Phase 2's whole-suite `-n 6` invocation and its four-rung resumption ladder | Superseded by `oracle/run-oracle-suite.sh`, whose two-pass split, `timeout --kill-after=60s` wrappers, and exit-124/137 classification replace the ladder's job |
| Phase 5's "minimal `PYTHONPATH` correction only" scope | Inverted: `verify-refactor.sh` now needs substantive repair, and the v1 non-goal "do not re-pin the collection count or the xfail line locations" is now precisely the required work |
| v1 Phase 1 and Phase 2's `[COMPLETED]` markers | Those markers are true of the v1 run and stay in the v1 file as history. They are **not** carried into v2 as satisfied work: they recorded checks against a 550-test suite and a since-superseded invocation, so their results are stale and every check is re-run here |

### Prior Plan Reference

`specs/127_close_oracle_suite_regression_baseline/plans/01_close-oracle-regression-baseline.md` is
the historical record and is not edited by this plan. Its Phase 3 triage findings and its
`.orchestrator-handoff.json` remain valid as a record of what was observed on 2026-07-25; they are
simply no longer a description of the current tree.

### Roadmap Alignment

No `roadmap_path` was provided in the delegation context and no roadmap phases were requested.

## Goals & Non-Goals

**Goals**:

- Produce a complete, triaged run of the **gating** oracle suite (604 of 606 tests: the 594
  parallel-pass tests plus the 10 `xdist_serial` tests), recorded as `oracle-run.txt` and
  `junit-oracle.xml` under the refactor task's `baselines/`.
- Produce a completed record of the **exhaustive** path (the remaining 2 `slow` tests), established
  from its `SCAN_COMPLETE` marker, so all 606 tests are accounted for rather than 604 with a silent
  gap.
- Re-pin `verify-refactor.sh` Step 3's oracle collection count to the measured value, and add the
  per-marker sub-counts so a test silently migrating between the gating and exhaustive populations
  is caught.
- Re-scope Step 5 from brittle line-number pins onto the accommodation guard that exists today —
  preserving its actual purpose (the accommodation cannot be silently weakened), matched by content
  so it cannot go stale on an unrelated edit.
- Re-point Step 6 at `oracle/run-oracle-suite.sh` so the gate runs the gating suite, not the
  exhaustive sweep.
- Flip the refactor plan's Phase 2 from `[PARTIAL]` to `[COMPLETED]` — **only** if the evidence
  supports it.
- Obtain one independent green `bash code/scripts/verify-refactor.sh` run with Step 6 live.

**Non-Goals**:

- Marking task 126 `COMPLETED`. This task delivers the evidence; that status transition is separate.
- Fixing any oracle defect discovered during triage. A genuine failure is reported as a blocker
  under category (c), not repaired here — repairing it inside a baselining task is how a "green"
  baseline stops meaning anything.
- Relaxing Step 3's exact-equality comparison to a `>=` floor. Exact equality is the property that
  makes a disappearing test visible; the fix for staleness is re-pinning, not loosening.
- Re-deriving `known_conclusive_complexity5.json` or any solve budget. Those belong to the
  exhaustive-derivation workflow documented in TESTING_GUIDE section 8.8.
- Refactoring `oracle/run-oracle-suite.sh` beyond the one additive, opt-in JUnit-output hook Phase 2
  needs.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Z3 contention from a concurrent session inflates solve times past budget and produces failures that pass in isolation | H | H | Phase 1's quiet-machine gate, re-checked immediately before and after every timed run and recorded both times; Phase 3's bounded isolated-re-run protocol distinguishes artifact from defect on evidence |
| The reverse error: a genuine defect is dismissed as contention because one isolated re-run happened to pass | H | M | Phase 3 caps isolated re-runs at two per test and requires a confirming full gating pass before any test is classed as an artifact; three strikes on the same test is category (c), full stop |
| A long run exceeds the 600s foreground tool ceiling and is killed by the harness, indistinguishably from a contention kill | H | H | Every timed phase mandates a backgrounded launch plus polling; completeness is established from the runner's own summary and exit-code capture, never from process liveness |
| `test_spot_check_individual_countermodels` fails even in isolation at the 180s budget | M | M | Already observed and recorded in `specs/137_…/summaries/01_…-summary.md`. If it recurs it is category (c) by definition; Phase 3 must cite that prior evidence rather than re-litigating it, and must not widen the budget |
| The gating suite has never been confirmed green end-to-end since the task-137 and task-139 changes landed | H | M | This is stated as an open question rather than assumed away — `specs/139_…/summaries/` explicitly lists a full two-pass re-run as an unperformed follow-up. Phase 2 is the first such run; a red result is a legitimate, planned-for outcome with a defined honest-recording path |
| Passing `--junitxml` through the runner's `"$@"` would make pass 2 overwrite pass 1's XML | M | H | Phase 2 adds an opt-in `ORACLE_JUNIT_DIR` env hook that writes distinct per-pass files, rather than duplicating the runner's `-m` expressions in an ad-hoc invocation that could drift |
| Commands run from a directory other than the repo root break `bimodal_harness` resolution | M | M | The devShell exports the sibling as the relative path `../BimodalHarness/src`; every command in this plan is issued from the repo root, and Phase 1 asserts importability before anything long starts |
| Re-scoping Step 5 produces a check that merely passes rather than one that guards | H | M | Phase 5 requires a negative test: the new check must be demonstrated to FAIL against a scratch copy with one assertion deleted and against one with a floor lowered, before it is accepted |
| The refactor plan's Phase 2 gets flipped on weak evidence | H | L | The flip lives in its own phase, gated explicitly on Phase 3 reaching category (a) or a resolved (b); category (c) rewrites the framing instead of flipping the marker |

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
| 7 | 8 | 7 |

Phases 5 and 6 are the only genuinely parallelizable pair (one edits a shell script, the other edits
a markdown plan; neither consumes CPU). Every other phase is serialized **by the quiet-machine
constraint, not by data dependency** — two timed runs must never overlap, and no CPU-consuming phase
may run alongside one.

### The quiet-machine protocol (referenced by Phases 1, 2, 3, 4, and 7)

Before **and** immediately after every timed run, capture and record:

```
ps aux --sort=-%cpu | head -15
uptime
```

The machine counts as quiet when no process other than this task's own run exceeds ~50% CPU — in
particular no foreign `pytest`, no `z3`, and no `lean --worker` (the last of these is the exact
process documented as having contended during tasks 138 and 139) — and the 1-minute load average is
below 2.0.

- Not quiet **before**: wait and re-check. Do not start.
- Not quiet **after**, on an otherwise-passing run: the result stands (contention cannot manufacture
  a pass), but record the observation.
- Not quiet **after**, on a failing run: the failures are unadjudicated. Do not classify them —
  re-run the whole pass on a quiet machine first. A contended failing run is not evidence of
  anything and must not be promoted, triaged, or reported as a result.

### Standing prohibitions (apply to every phase)

Never, in any phase, to obtain a green result:

- Widen `TEMPORAL_SOLVE_TIMEOUT_MS`, `ATEMPORAL_SOLVE_TIMEOUT_MS`, `SELF_SCAN_SOLVE_TIMEOUT_MS`, or
  any `timeout`/`ORACLE_PASS*_TIMEOUT` budget.
- Lower `MIN_CONCLUSIVE_SCAN_FORMULAS`, `MIN_CONCLUSIVE_GATING_FORMULAS`, or
  `MIN_CONCLUSIVE_TEMPORAL_BH_FORMULAS`.
- Add or broaden `xfail`, `skip`, `deselect`, or `-m` filters beyond what
  `oracle/run-oracle-suite.sh` already applies.
- Use `--lf`, `--last-failed`, or `-p no:cacheprovider` to reshape which tests run.
- Re-run the suite repeatedly until a green result appears. The bounded protocol in Phase 3 is the
  only sanctioned repetition.

Relaxing Step 3's `!=` to `>=` is likewise forbidden: it is a weakening, not a fix.

---

### Phase 1: Quiet-Machine Preflight and Pin Re-derivation [COMPLETED]

**Completed:** 2026-08-09

- **Goal:** Establish the environment, capture the numbers the later phases pin against, and confirm
  the machine is idle — before spending hours of wall clock.
- **Tasks:**
  - [x] Create the scratch staging directory
        `specs/127_close_oracle_suite_regression_baseline/run2/`. This is never committed; Phase 8
        removes it. (`run/` from the v1 attempt is left untouched as historical evidence.)
  - [x] Record the quiet-machine protocol's "before" capture into `run2/machine-before-phase1.txt`.
        *(deviation: 1-minute load average fluctuated 1.96-2.95 across four samples, driven by
        other concurrent Claude Code agent sessions in this swarm, not by Z3/pytest/lean-worker
        CPU -- no foreign pytest, z3, or actively-CPU-consuming lean --worker process was present
        at any sample. Treated as acceptable for Phase 1's own lightweight, non-timed tasks; Phase
        2's timed run gets its own dedicated, stricter quiet check.)*
  - [x] From the repo root, confirm the devShell interpreter and its xdist:
        `nix develop --command python3 -c "import xdist; print(xdist.__version__)"` → expect `3.8.0`.
        If this fails, stop — the gating runner cannot run and the whole approach needs revisiting.
        Confirmed: `xdist 3.8.0`.
  - [x] Confirm `bimodal_harness` resolves inside the devShell:
        `nix develop --command python3 -c "import bimodal_harness; print('OK')"`. Confirmed: `OK`.
  - [x] Capture the four collection counts into `run2/collection-counts.txt`, each with its exact
        command, run from the repo root inside `nix develop`:
        - `pytest oracle --collect-only -q` (total; expected 606) → 606
        - `-m "not xdist_serial and not slow"` (gating parallel pass; expected 594) → 594
        - `-m "xdist_serial and not slow"` (gating serial pass; expected 10) → 10
        - `-m slow` (exhaustive; expected 2) → 2
        The three sub-counts must sum to the total. If they do not, stop and report — that is a
        marker-configuration defect, not a counting error. Confirmed: 594+10+2=606.
  - [x] Capture the guard inventory into `run2/guard-inventory.txt`: the five assertion expressions
        and their current line numbers in `test_cross_oracle_differential.py`; the current values of
        `MIN_CONCLUSIVE_SCAN_FORMULAS`, `MIN_CONCLUSIVE_GATING_FORMULAS`,
        `MIN_CONCLUSIVE_TEMPORAL_BH_FORMULAS`, `SELF_SCAN_SOLVE_TIMEOUT_MS`; the count and strictness
        of the remaining `xfail(` markers in `test_oracle_interface.py`; and the existence of
        `oracle/bimodal_logic/KNOWN_EXTERNAL_DEFECTS.md`. Phase 5 pins against this file. Confirmed:
        assertions at lines 1399/1406/1419/1436/1454 in that order; constants 10000/90/100/45; 4
        xfail markers (lines 1357/1369/1383/1393), all strict=True; KNOWN_EXTERNAL_DEFECTS.md
        exists, 8110 bytes/118 lines.
  - [x] Confirm `specs/126_refactor_repo_core_infrastructure_theory_lib/baselines/serial-rebaseline/`
        is still empty, and record the decision to remove it in Phase 8 (an empty directory that
        looks like evidence is worse than no directory). Confirmed still empty.
- **Timing:** 30 minutes
- **Depends on:** none
- **Files to modify:** none outside `run2/` (scratch)
- **Verification:**
  - `xdist.__version__` prints; `import bimodal_harness` succeeds.
  - `run2/collection-counts.txt` exists, contains four counts, and the three sub-counts sum to the
    total.
  - `run2/guard-inventory.txt` records all five assertion expressions, all four constants, and the
    `xfail` inventory.
  - `run2/machine-before-phase1.txt` shows a quiet machine.

---

### Phase 2: Gating-Suite Baseline Run Into Staging [COMPLETED]

**Completed:** 2026-08-09

- **Goal:** One complete, uncontended run of the canonical gating suite, captured as text and as
  JUnit XML, staged and not yet judged.
- **Tasks:**
  - [x] Add an opt-in JUnit hook to `oracle/run-oracle-suite.sh`. When the environment variable
        `ORACLE_JUNIT_DIR` is set and non-empty, append
        `--junitxml="$ORACLE_JUNIT_DIR/junit-oracle-pass1.xml"` to pass 1 and
        `--junitxml="$ORACLE_JUNIT_DIR/junit-oracle-pass2.xml"` to pass 2; when unset, behaviour is
        byte-for-byte what it is today. This is additive and opt-in specifically so the plan does not
        duplicate the runner's `-m` expressions in an ad-hoc invocation that could silently drift
        from the gate. Do not change the `-m` expressions, the `-n 6`, the `timeout` wrappers, the
        budgets, or the exit-code classification. Add a brief comment explaining why the hook exists;
        **no task-number references** in the comment (this file is outside `specs/**`).
  - [x] Record the quiet-machine "before" capture into `run2/machine-before-phase2.txt`.
  - [x] Launch the run **in the background** — the expected 20-35 minutes far exceeds the 600s
        foreground ceiling, and the runner's own budgets already cap it at 2200s plus overhead:

        ```
        RUN=specs/127_close_oracle_suite_regression_baseline/run2
        nix develop --command bash -c '
          ORACLE_JUNIT_DIR='"$PWD/$RUN"' bash oracle/run-oracle-suite.sh 2>&1 \
            | tee '"$RUN"'/oracle-run.txt
          echo "exit=${PIPESTATUS[0]}" > '"$RUN"'/exit-code.txt
        '
        ```

        Issue this from the repository root — the devShell exports the BimodalHarness sibling as a
        relative path.
  - [x] Poll for `run2/exit-code.txt` and for growth in `run2/oracle-run.txt`. Never relaunch while
        the first process is alive; never infer completion from a vanished PID.
  - [x] Record the quiet-machine "after" capture into `run2/machine-after-phase2.txt` and the
        wall-clock duration.
  - [~] Merge the two per-pass JUnit files into `run2/junit-oracle.xml` with a short stdlib
        `xml.etree.ElementTree` script that sums the `tests`/`failures`/`errors`/`skipped`
        attributes and concatenates the `<testcase>` children. Record the script inline in the
        implementation summary so the merge is reproducible.
        *(deviation: the merge script was written (`run2/merge-junit.py`) but there is no pass-2
        JUnit file to merge. Both pass-2 executions were SIGTERM'd by the runner's
        `timeout --kill-after=60s 900` wrapper mid-test, and pytest writes `--junitxml` only at
        session teardown, so no pass-2 XML was ever produced. Merging pass 1's XML alone into a
        file named `junit-oracle.xml` would misrepresent a 594-test partial as the 604-test
        gating report, so it was deliberately not done. `run2/junit-oracle-pass1.xml` stands on
        its own as the pass-1 record.)*
- **Timing:** 45 minutes agent time; 20-35 minutes unattended wall clock
- **Depends on:** 1
- **Files to modify:**
  - `oracle/run-oracle-suite.sh` — additive `ORACLE_JUNIT_DIR` hook only
  - `run2/oracle-run.txt`, `run2/junit-oracle-pass{1,2}.xml`, `run2/junit-oracle.xml`,
    `run2/exit-code.txt`, `run2/machine-{before,after}-phase2.txt` — staged output
- **Verification (completeness only — no pass/fail judgement in this phase):**
  - `run2/exit-code.txt` exists. Its absence means the process died before finishing.
  - `run2/oracle-run.txt` contains the runner's own `== oracle suite summary ==` block with a
    verdict line for **both** passes. A run missing pass 2's line is truncated.
  - Neither pass is classified `TIMED OUT (exit 124)` or `(exit 137)`. A timed-out pass is not a
    result — re-run it on a quiet machine; if it times out again on a verified-quiet machine, that
    is a genuine finding for Phase 3 to record, never a reason to raise `ORACLE_PASS*_TIMEOUT`.
  - Both per-pass JUnit files exist, are non-empty, have closed root elements, and their `tests`
    attributes sum to the gating total recorded in Phase 1 (expected 604).
  - `git diff oracle/run-oracle-suite.sh` shows only the additive hook; an unset
    `ORACLE_JUNIT_DIR` invocation is spot-checked to behave as before.

---

### Phase 3: Triage Against the Rubric, Then Promote or Record Honestly [COMPLETED]

**Completed:** 2026-08-09 -- category (c); see `baselines/oracle-baseline-STATUS.md`

- **Goal:** Classify the run into exactly one pre-declared category on evidence, so a contention
  artifact is not mistaken for a defect and — equally — a defect is not waved through as contention.
- **Tasks:**
  - [x] Extract every failing test ID from the merged XML (`<testcase>` elements with a `<failure>`
        or `<error>` child) and cross-check against the text output's summary lines.
  - [x] Confirm no strict-xfail XPASSed anywhere in the run.
  - [x] Classify per the rubric below and take that category's action.
- **Timing:** 60 minutes agent time; plus up to 45 minutes wall clock if isolated re-runs are needed
- **Depends on:** 2
- **Files to modify (category (a) or resolved (b) only):**
  - `specs/126_refactor_repo_core_infrastructure_theory_lib/baselines/oracle-run.txt` — replaced
  - `specs/126_refactor_repo_core_infrastructure_theory_lib/baselines/junit-oracle.xml` — created
- **Files to modify (category (c) only):**
  - `specs/126_refactor_repo_core_infrastructure_theory_lib/baselines/oracle-run-RED-{ISO_DATE}.txt`
  - `specs/126_refactor_repo_core_infrastructure_theory_lib/baselines/oracle-baseline-STATUS.md`

**Success rubric (fixed before the run; not renegotiable after seeing results):**

- **(a) Clean.** Both passes report `PASSED`, the recorded exit code is 0, and the merged XML has
  zero `failures` and zero `errors` across the full gating count. **Action:** promote
  `run2/oracle-run.txt` and `run2/junit-oracle.xml` into `baselines/`, then continue.

- **(b) Failures that do not survive isolation.** **Action — a bounded protocol, not an assumption:**

  1. Re-run the exact failing node IDs together in ONE serial invocation (no `-n`) on a
     verified-quiet machine, backgrounded, from the repo root inside the devShell:

     ```
     nix develop --command bash -c 'pytest "<id1>" "<id2>" … -q' 2>&1 \
       | tee specs/127_close_oracle_suite_regression_baseline/run2/isolated-attempt-1.txt
     ```

     (Running inside `nix develop` supplies the `bimodal_harness` sibling path. Without it, any
     `test_oracle_interface.py` node fails at import — a `ModuleNotFoundError`, not a test result.)
  2. Any test still failing here is category (c). No further attempts for that test.
  3. For tests that passed in isolation, run **one** confirming full gating pass (Phase 2's command,
     into `run2/confirm/`). If they pass there too, they are contention artifacts.
  4. If a test that passed in isolation fails again in the confirming pass, that is its **third**
     observation. Three strikes → category (c). Do not attempt a fourth run.
  5. **Cap: at most two isolated re-runs per test, and at most one confirming full pass, for the
     whole phase.** Exceeding the cap means the answer is (c).

  On a resolved (b): promote both artifacts, and append to the promoted `oracle-run.txt` a
  clearly-delimited trailing annex — visually separated from pytest's own output so the file cannot
  be mistaken for an unqualified clean run — recording every failing ID, the exact isolated re-run
  command, its result, the confirming pass's result, and the machine-quietness captures for each.

- **(c) A failure that reproduces on a quiet machine.** Triggered by any of: a test failing its
  isolated re-run; a test hitting three strikes; a pass classified `TIMED OUT` on a verified-quiet
  machine; a strict-xfail XPASS; or a collection count that disagrees with Phase 1's.

  **Action — record it honestly; do not force green and do not simply stop.**
  - Do **not** promote a green-looking `oracle-run.txt`, and do **not** overwrite the committed
    partial `baselines/oracle-run.txt` (it is the only record of the prior state).
  - Do **not** touch any assertion, budget, floor, marker, or guard. Suppressing the signal is the
    single outcome this task exists to prevent.
  - **Do** write the red run to `baselines/oracle-run-RED-{ISO_DATE}.txt` and a companion
    `baselines/oracle-baseline-STATUS.md` stating, per failing test: the node ID, the failure mode
    and exception type, every re-run performed with its result, the machine-quietness capture for
    each, and whether prior evidence already documents it (for instance,
    `test_spot_check_individual_countermodels` is already recorded in
    `specs/137_investigate_mc_bh_resolved_and_wrong_disagreements/summaries/` as failing in isolation
    at the 180s budget — cite that rather than re-deriving it).
  - Phases 4-8 still run for everything that is not gated on a green suite: Phase 5's
    `verify-refactor.sh` repair is independently correct and valuable, and Phase 8 commits it.
    **Phase 6 does not run** — the refactor plan's Phase 2 stays `[PARTIAL]`, but its stale framing
    (missing `pytest-xdist`, a 550-test serial run, a contention kill) is corrected to name the
    actual residual failures and to cite `oracle-baseline-STATUS.md`. **Phase 7's success criterion
    changes**: `verify-refactor.sh` is expected to fail at Step 6, and that expected failure is
    recorded as the honest state of the gate, not engineered away.
  - Report the failing IDs, the status file, and the staged output as an explicit blocker in the
    implementation summary and the orchestrator handoff.

- **Verification:**
  - The chosen category is stated explicitly with its evidence (exit codes, failing IDs, every
    re-run and its result, machine captures) in the implementation summary.
  - On (a) or resolved (b): both files exist in `baselines/`, are non-empty, and the XML totals the
    gating count from Phase 1.
  - On (c): both red-path files exist and name every failing test.
  - `git diff --stat -- oracle/bimodal_logic/` is empty. No test file was touched during triage.

---

### Phase 4: Exhaustive-Scan Coverage Record [NOT STARTED]

- **Goal:** Account for the 2 `slow` tests the gating suite deliberately excludes, so the baseline
  covers all 606 tests rather than 604 with an unmentioned gap.
- **Tasks:**
  - [ ] Record the quiet-machine "before" capture into `run2/machine-before-phase4.txt`. This run is
        long and serial; it must not overlap anything.
  - [ ] Launch backgrounded, from the repo root:
        `nix develop --command bash oracle/run-oracle-exhaustive-scan.sh 2>&1 | tee run2/exhaustive-run.txt`
  - [ ] Poll to completion. **Completion is established from the `SCAN_COMPLETE` marker under the
        run's output directory, never from the process exiting or the PID vanishing** — this is the
        contract in `code/docs/core/TESTING_GUIDE.md` section 8.8, and inferring completion from PID
        absence has produced a false completion report before.
  - [ ] Record the quiet-machine "after" capture and the wall-clock duration.
  - [ ] Copy the scan's `report.json` and `SCAN_COMPLETE` marker, plus the tee'd text output, into
        `specs/126_refactor_repo_core_infrastructure_theory_lib/baselines/exhaustive-scan/`. Do not
        copy `progress.jsonl` (large, and the report supersedes it).
  - [ ] If the scan does not reach completion, or `test_complexity_5_scan_self_consistent` fails:
        this is category (c) for the exhaustive path. Record it in
        `baselines/exhaustive-scan/STATUS.md` with the same honesty requirements as Phase 3(c). Do
        **not** re-derive `known_conclusive_complexity5.json` or adjust
        `SELF_SCAN_SOLVE_TIMEOUT_MS` — that is the exhaustive-derivation workflow, out of scope here,
        and doing it inside a baselining task would be exactly the "adjust the threshold to
        manufacture green" move the suite's own documentation forbids.
- **Timing:** 30 minutes agent time; 60-90 minutes unattended wall clock
- **Depends on:** 3
- **Files to modify:**
  - `specs/126_refactor_repo_core_infrastructure_theory_lib/baselines/exhaustive-scan/` — new
    directory holding `report.json`, `SCAN_COMPLETE`, `exhaustive-run.txt`, and (if needed)
    `STATUS.md`
- **Verification:**
  - `SCAN_COMPLETE` exists in the copied artifacts and its contents are recorded.
  - The runner's summary block reports `pytest: PASSED` and `completion marker: present`.
  - `git diff --stat -- oracle/bimodal_logic/` is still empty.

---

### Phase 5: Re-pin and Re-scope `code/scripts/verify-refactor.sh` [IN PROGRESS]

- **Goal:** Make the regression gate correct against the suite that exists, strengthening its checks
  rather than loosening any of them.
- **Tasks:**
  - [x] **Step 3 — re-pin the count.** Set `BASELINE_ORACLE_COUNT` to Phase 1's measured total (606
        at the time of writing; use the measured value, not this number). Keep the `!=` exact-equality
        comparison. Add three new pinned sub-counts from Phase 1
        (`BASELINE_ORACLE_PARALLEL_COUNT`, `BASELINE_ORACLE_SERIAL_COUNT`, `BASELINE_ORACLE_SLOW_COUNT`)
        and assert each with the same exact-equality semantics. This is a strengthening: it catches a
        test silently migrating between the gating and exhaustive populations, which the total alone
        cannot see. Add a comment directing anyone who adds oracle tests to re-pin all four here.
  - [x] **Step 5 — re-scope onto the guard that exists.** Delete the `XFAIL_LINES` array and the
        line-number comparison; the file it pinned now contains zero `xfail(` markers, so the check
        cannot pass and, more importantly, no longer describes the accommodation. Replace it with
        content-matched assertions — **never line numbers**, since line-number matching is precisely
        what went stale — that fail loudly if any of the following is missing or altered:
        1. `oracle/bimodal_logic/KNOWN_EXTERNAL_DEFECTS.md` exists and is non-empty.
        2. All five ordered assertions are present in
           `oracle/bimodal_logic/tests/test_cross_oracle_differential.py`, each exactly once, in this
           order: `assert conclusive >= MIN_CONCLUSIVE_TEMPORAL_BH_FORMULAS`, `assert not
           mc_soundness_bug`, `assert not unclassified`, `assert external_bh_defect`, `assert not
           bad_signature`. Order matters and is asserted, because the ordering is what makes each
           failure self-diagnosing (a starved budget is ruled out before the semantic guards run).
        3. The four floor/budget constants recorded in Phase 1's guard inventory
           (`MIN_CONCLUSIVE_SCAN_FORMULAS`, `MIN_CONCLUSIVE_GATING_FORMULAS`,
           `MIN_CONCLUSIVE_TEMPORAL_BH_FORMULAS`, `SELF_SCAN_SOLVE_TIMEOUT_MS`) are present with
           exactly their pinned values, so a floor cannot be quietly lowered.
        4. `oracle/bimodal_logic/tests/test_oracle_interface.py` still carries exactly its current
           number of `xfail(` markers (4 at the time of writing) and every one of them is
           `strict=True`.
        Write the step's `note`/`fail` messages so a failure says which specific guard went missing.
  - [x] **Step 6 — run the gating suite, not the exhaustive sweep.** Replace the raw
        `PYTHONPATH=code/src python -m pytest oracle/bimodal_logic/tests/ -q` with
        `bash oracle/run-oracle-suite.sh`. The runner supplies the marker deselects, the two-pass
        `xdist_serial` split, the calibrated timeouts, and the exit-124/137 classification. Preserve
        fail-fast semantics: a non-zero runner exit, including its "pytest-xdist is not importable"
        preflight failure, must increment `FAILURES` — never be skipped or downgraded.
  - [x] **Update the stale prose.** The header comment block still describes 550 tests, "the 5
        xfail(strict=True) cross-oracle differentials", and a "~7+ minute" oracle suite. Rewrite it
        to describe what the script now checks. Keep the existing path references to
        `specs/…/baselines/…` (durable path anchors) but add **no** new task-number citations —
        this file is outside `specs/**` and `.claude/rules/no-task-references-in-deliverables.md`
        applies.
  - [x] Leave Steps 1, 2, 4, and 7 untouched. Their `>=` floors (289 bimodal, 2100 full) still pass
        against the current 298 / 2190 counts.
- **Timing:** 75 minutes
- **Depends on:** 4
- **Files to modify:**
  - `code/scripts/verify-refactor.sh` — Steps 3, 5, 6 and the header comment
- **Verification:**
  - `bash -n code/scripts/verify-refactor.sh` parses clean.
  - **Negative test (required — a check that only ever passes is not a guard).** Against a scratch
    copy of the repository tree under `run2/negative/`, demonstrate that the new Step 5 FAILS when:
    (i) one of the five assertions is deleted; (ii) two of them are transposed; (iii)
    `MIN_CONCLUSIVE_GATING_FORMULAS` is lowered; (iv) one `strict=True` is removed. Record all four
    failure messages. Restore the scratch copy afterwards and confirm
    `git diff --stat -- oracle/ code/` shows only the intended Phase 5 change.
  - `bash code/scripts/verify-refactor.sh --skip-oracle` exits 0 (Steps 1-5 and 7, no suite run).
  - `git diff code/scripts/verify-refactor.sh` touches only Steps 3, 5, 6 and the header.

---

### Phase 6: Flip the Refactor Plan's Phase 2 Markers [COMPLETED]

**Completed:** 2026-08-09 -- gate NOT met (category (c)), so the marker flip was correctly NOT performed; the category-(c) framing correction was done instead

- **Gate:** Runs **only** if Phase 3 reached category (a) or a resolved (b). Under category (c),
  perform the framing correction described in Phase 3(c) instead of the flip.
- **Goal:** Make the refactor plan reflect the closed gap at every location that currently frames it
  as open, and remove the premises now known to be false.
- **Tasks:**
  - [ ] Rewrite the plan-level status line (currently line 4, spanning to line 8) in
        `specs/126_refactor_repo_core_infrastructure_theory_lib/plans/01_core-theory-lib-refactor.md`:
        `[PARTIAL]` → `[COMPLETED]`, and replace the parenthetical, which currently asserts three
        things now known to be false — that no `pytest-xdist` is available, that the suite is 550
        tests, and that it must be run serially. State instead: all 26 phases COMPLETED, with the
        gating oracle suite recorded in `baselines/oracle-run.txt` / `baselines/junit-oracle.xml` and
        the exhaustive path in `baselines/exhaustive-scan/`.
  - [ ] Change the section heading (currently line 216) to
        `### Phase 2: Pin Verification Baselines and Build the Regression Gate [COMPLETED]` and add a
        `Completed:` timestamp line in the phase body per plan-format.md.
  - [ ] Rewrite the three stale body cross-references (currently lines 1575, 1695, 1712) so they read
        as closed, citing the baseline artifacts by filename. Rewrite; do not merely delete.
  - [ ] Re-grep the file for `PARTIAL` and for `550` and confirm no occurrence still frames the
        oracle run as incomplete or as a 550-test serial run.
- **Timing:** 45 minutes
- **Depends on:** 4 (and gated on 3's category)
- **Files to modify:**
  - `specs/126_refactor_repo_core_infrastructure_theory_lib/plans/01_core-theory-lib-refactor.md`
- **Verification:**
  - `grep -n 'PARTIAL' …/01_core-theory-lib-refactor.md` returns no hit describing the oracle run as
    incomplete.
  - `grep -n '550' …/01_core-theory-lib-refactor.md` returns no hit presenting 550 as the current
    oracle count.
  - The Phase 2 heading matches `### Phase 2: … [COMPLETED]` exactly, with no emoji.

---

### Phase 7: Independent `verify-refactor.sh` Confirmation With Step 6 Live [NOT STARTED]

- **Goal:** One full run of the repaired gate with Step 6 actually executing the gating suite —
  independent of the Phase 2 run, not a replay of it.
- **Tasks:**
  - [ ] Record the quiet-machine "before" capture into `run2/machine-before-phase7.txt`.
  - [ ] Launch backgrounded from the repo root (Step 4's bimodal suite plus Step 6's gating suite
        together far exceed the foreground ceiling):

        ```
        nix develop --command bash -c 'bash code/scripts/verify-refactor.sh' 2>&1 \
          | tee specs/127_close_oracle_suite_regression_baseline/run2/verify-refactor.txt
        ```

        Do **not** set `PYTEST_ADDOPTS`. The gating runner manages its own parallelism deliberately;
        injecting `-n` would apply it to the serial `xdist_serial` pass and recreate the exact
        contention the split exists to eliminate.
  - [ ] Poll to completion; record the quiet-machine "after" capture and the wall clock.
  - [ ] Confirm the script prints `All checks passed`, exits 0, and that Step 6 shows a real result
        rather than `SKIPPED`.
  - [ ] Confirm `bash code/scripts/verify-refactor.sh --skip-oracle` still exits 0, so the fast path
        is unbroken.
  - [ ] **Under Phase 3 category (c):** the expected outcome is a Step 6 failure. Record the exact
        output verbatim in the implementation summary and in `baselines/oracle-baseline-STATUS.md`,
        and confirm the failure is the one already adjudicated in Phase 3 and not a new one. Do not
        add `--skip-oracle` to make the gate green, and do not report the gate as passing.
- **Timing:** 45 minutes agent time; 25-40 minutes unattended wall clock
- **Depends on:** 5, 6
- **Files to modify:** none (produces `run2/verify-refactor.txt`)
- **Verification:**
  - `run2/verify-refactor.txt` shows Steps 1-7 each with a result, Step 6 executed (not `SKIPPED`),
    and — under category (a)/(b) — `All checks passed` with exit 0.
  - The `--skip-oracle` path still exits 0.
  - The machine was quiet before and after.

---

### Phase 8: Commit and Clean Up [NOT STARTED]

- **Goal:** Land the baselines, the gate repair, and the plan edits as one reviewable commit, with no
  scratch or misleading-empty artifacts left behind.
- **Tasks:**
  - [ ] Remove `specs/127_close_oracle_suite_regression_baseline/run2/` (scratch, never committed).
        Leave `run/` — the v1 attempt's evidence — untouched.
  - [ ] Remove the empty
        `specs/126_refactor_repo_core_infrastructure_theory_lib/baselines/serial-rebaseline/`
        directory. It was created for artifacts that were never produced, and an empty directory that
        looks like a results location is worse than none.
  - [ ] Stage exactly: the `baselines/` artifacts produced by Phases 3 and 4, the
        `oracle/run-oracle-suite.sh` hook, `code/scripts/verify-refactor.sh`, the refactor plan edits
        (Phase 6, or the category-(c) framing correction), this plan, the implementation summary, and
        the state/TODO updates. Use targeted `git add` paths — never `git add -A`, never
        `git commit -am`.
  - [ ] Review `git status --short` and `git diff --staged` before committing. This branch has
        concurrent-session activity in `specs/`; confirm nothing unrelated was swept in.
  - [ ] Commit as `task 127: complete implementation` with the session ID in the body.
- **Timing:** 30 minutes
- **Depends on:** 7
- **Files to modify:** none beyond staging and committing the above
- **Verification:**
  - `git status --short` shows no leftover `run2/` and no unintended staged paths.
  - `git show --stat HEAD` lists only the intended files.
  - `git diff --stat HEAD -- oracle/bimodal_logic/` is empty: no oracle *test* file was modified by
    this task (only the runner script).

## Testing & Validation

- [ ] `pytest oracle --collect-only -q` reports the pinned total, and the three `-m` sub-counts sum
      to it.
- [ ] The gating run's text output contains both passes' verdict lines, and neither is `TIMED OUT`.
- [ ] The merged `junit-oracle.xml` totals the gating count with zero `failures` and zero `errors`
      — or, under a resolved category (b), only failures each shown passing in a recorded isolated
      re-run plus a confirming full pass.
- [ ] No strict-xfail XPASS anywhere in the run.
- [ ] The exhaustive scan's `SCAN_COMPLETE` marker is present and archived.
- [ ] The re-scoped Step 5 demonstrably FAILS in all four negative-test mutations, and passes on the
      unmodified tree.
- [ ] `bash code/scripts/verify-refactor.sh` (no `--skip-oracle`) exits 0 with Step 6 executed —
      or, under category (c), fails at exactly the adjudicated Step 6 failure and is reported as
      failing.
- [ ] `bash code/scripts/verify-refactor.sh --skip-oracle` exits 0.
- [ ] No test file under `oracle/bimodal_logic/` was modified: `git diff --stat --
      oracle/bimodal_logic/` is empty.
- [ ] No solve budget, timeout, or `MIN_CONCLUSIVE_*` floor changed anywhere:
      `git diff -- oracle/` contains no edit to those constants.
- [ ] No task-number citation was introduced into `oracle/run-oracle-suite.sh` or
      `code/scripts/verify-refactor.sh`: `grep -nEi 'task [0-9]|tasks [0-9]'` on both is empty.

## Artifacts & Outputs

- `specs/126_refactor_repo_core_infrastructure_theory_lib/baselines/oracle-run.txt` — complete
  gating-suite run text, replacing the truncated placeholder (category (a)/(b) only)
- `specs/126_refactor_repo_core_infrastructure_theory_lib/baselines/junit-oracle.xml` — merged
  two-pass JUnit XML for the same run (category (a)/(b) only)
- `specs/126_refactor_repo_core_infrastructure_theory_lib/baselines/exhaustive-scan/` —
  `report.json`, `SCAN_COMPLETE`, and text output for the 2 `slow` tests
- `specs/126_refactor_repo_core_infrastructure_theory_lib/baselines/oracle-run-RED-{ISO_DATE}.txt`
  and `oracle-baseline-STATUS.md` — category (c) only
- `code/scripts/verify-refactor.sh` — Step 3 re-pinned with sub-counts, Step 5 re-scoped onto the
  live guard mechanism, Step 6 pointed at the gating runner, header prose corrected
- `oracle/run-oracle-suite.sh` — additive, opt-in `ORACLE_JUNIT_DIR` hook
- `specs/126_refactor_repo_core_infrastructure_theory_lib/plans/01_core-theory-lib-refactor.md` —
  Phase 2 closed (or its framing corrected under category (c))
- `specs/127_close_oracle_suite_regression_baseline/plans/02_rebaseline-gating-oracle-suite.md` —
  this plan
- `specs/127_close_oracle_suite_regression_baseline/summaries/02_rebaseline-gating-oracle-suite-summary.md`
  — implementation summary recording the rubric category reached, every re-run and its result, the
  machine-quietness captures, the wall clocks, and the four negative-test failure messages

## Rollback/Contingency

- **Nothing is destroyed before something better replaces it.** All suite output stages in
  `run2/` and is promoted into `baselines/` only after the completeness checks and the rubric both
  pass. A truncated, timed-out, contended, or red run never overwrites the committed partial
  baseline.
- **Recovering the prior partial baseline:** it is committed at `b40179c9`, so
  `git show b40179c9:specs/126_refactor_repo_core_infrastructure_theory_lib/baselines/oracle-run.txt`
  restores it with no destructive git operation. Prefer this over `git checkout --` on a dirty tree,
  which the destructive-git guard blocks.
- **Reverting the script changes:** both `verify-refactor.sh` and `run-oracle-suite.sh` edits are
  small self-contained diffs; revert by editing forward or by `git revert` of the Phase 8 commit.
  Run `bash .claude/scripts/git-snapshot.sh` first if any rollback would discard uncommitted work.
- **If the gating suite cannot go green:** that is category (c), and it is a planned outcome with a
  defined record, not a failure of the plan. The task delivers the gate repair (Phase 5) and the
  honest status record regardless; the refactor plan stays `[PARTIAL]` with corrected framing, and
  the residual failures are reported as a blocker for a follow-up task to diagnose. A fabricated or
  force-fit green baseline is the one outcome nothing recovers from.
- **If the machine cannot be made quiet** across the ~2.5-4 hours this needs: stop and report rather
  than running contended. Every result obtained under contention is unadjudicable, so a contended
  run consumes hours and yields nothing that can be promoted.
