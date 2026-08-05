# Implementation Plan: Close the Oracle Suite Regression Baseline

- **Task**: 127 - Complete the oracle differential-suite regression baseline that the core/theory_lib refactor could not finish
- **Status**: [BLOCKED] — Phase 3 triage reached rubric category (c): `test_all_sat_task_relation_ternary`
  fails on the current branch, passed at pre-refactor commit `6cfb7f48`, and is therefore a
  refactor-introduced regression. No baseline was promoted and the refactor plan's Phase 2 markers
  were not flipped. Phases 4-6 are blocked until the regression is fixed and the suite re-triaged.
- **Effort**: 3 hours agent time (plus 35-60 minutes of unattended wall-clock across two long suite runs)
- **Dependencies**: None (task 126 depends on this one, not the reverse)
- **Research Inputs**: `specs/127_close_oracle_suite_regression_baseline/reports/01_oracle-baseline-environment.md`
- **Artifacts**: plans/01_close-oracle-regression-baseline.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: python
- **Lean Intent**: false

## Overview

The 550-test oracle differential suite has never completed a full run in this sandbox, leaving the
core/theory_lib refactor plan's Phase 2 at `[PARTIAL]`. Research established that every named
blocker is already resolved: `pytest-xdist` 3.8.0 is prebuilt in the project's own Nix devShell, the
required `bimodal_harness` sibling checkout is on disk, and a `-n 6` run should finish in 15-25
minutes rather than 45-90. The remaining work is therefore mechanical: secure a contention-free
window, run the suite once under `-n 6` with both text and JUnit output, triage the result against a
pre-declared success rubric, flip the refactor plan's Phase 2 markers, obtain an independent
`verify-refactor.sh` confirmation with Step 6 live, and commit the two baseline artifacts.

Definition of done: `specs/126_refactor_repo_core_infrastructure_theory_lib/baselines/oracle-run.txt`
and `.../junit-oracle.xml` record a complete 550-test run with no genuine failures; the refactor
plan's Phase 2 reads `[COMPLETED]`; and `bash code/scripts/verify-refactor.sh` (no `--skip-oracle`)
exits 0.

### Research Integration

The plan takes these findings as settled and does not re-derive them:

- Use the Nix devPython (`nix develop --command ...`), never the bare system `python3` — `xdist` is
  already present there and no install is needed.
- `PYTHONPATH` must include `/home/benjamin/Projects/BimodalHarness/src` or
  `test_oracle_interface.py` fails at import. `nix develop`'s `shellHook` sets this automatically.
- The two `F`s in the existing partial baseline decode to
  `test_complexity_5_scan_self_consistent` and `test_all_sat_task_relation_ternary`, both already
  documented as Category C contention flakes (pass in isolation). These form the entire known-flake
  watch list; anything else failing is new.

  > **Correction (2026-07-25)**: `test_complexity_5_scan_self_consistent` is not a Category C
  > contention flake. The source disposition document
  > (`specs/122_rootcause_crossoracle_differential_and_establish_t/baselines/oracle-suite-disposition.md`)
  > lists 7 named tests under Category C, and this test is not among them — the label above was
  > introduced by conflation with `test_all_sat_task_relation_ternary`, which genuinely is a
  > Category C entry. The actual diagnosis and fix are recorded in
  > `specs/133_fix_oracle_self_consistency_disagreements/reports/01_oracle-self-consistency.md`:
  > the test's per-formula Z3 solve budget (inherited default 5000ms) sits inside the solve-time
  > band of at least one complexity<=5 formula, so a blown budget is silently read as "no
  > countermodel" and inverts that formula's verdict — a budget-boundary defect, not contention.
  > The original bullet is left in place above for history; do not carry the Category C label for
  > this specific test forward into new documents.
- `verify-refactor.sh` emits no `--junitxml` for any suite, so `junit-oracle.xml` needs its own
  explicit invocation — the script alone will never produce it.
- Baselines belong in `specs/126_refactor_repo_core_infrastructure_theory_lib/baselines/`, not a new
  directory under this task.
- A concurrent pytest process from another session was observed live during research. The
  clear-window check in Phase 1 is not ceremony.

### Prior Plan Reference

No prior plan for this task. The refactor plan being unblocked
(`specs/126_refactor_repo_core_infrastructure_theory_lib/plans/01_core-theory-lib-refactor.md`) is
the edit target of Phase 4, not a template. Its Phase 2 body already records the acceptance evidence
this task must complete, and its effort estimates are not transferable.

### Roadmap Alignment

No `roadmap_path` was provided in the delegation context and no roadmap phases were requested.

## Goals & Non-Goals

**Goals**:

- Produce a complete, non-truncated 550-test oracle run recorded as both `oracle-run.txt` and
  `junit-oracle.xml` in the refactor task's `baselines/` directory.
- Distinguish, by a rubric fixed before the run, a clean pass from a known-flake pass from a genuine
  regression — and stop on the last.
- Flip the refactor plan's Phase 2 status line, section heading, and three stale body
  cross-references from `[PARTIAL]` framing to closed.
- Obtain one independent green `verify-refactor.sh` run with Step 6 actually executing the suite.

**Non-Goals**:

- Marking the core/theory_lib refactor task COMPLETED. This task delivers the evidence; the status
  transition on that task is a separate operation.
- Fixing, re-marking, or suppressing either known contention flake. If they pass in isolation the
  precedent holds and nothing changes in the test files.
  > **Correction (2026-07-25)**: see the corrective note in "Research Integration" above —
  > `test_complexity_5_scan_self_consistent` was misclassified as Category C and has since been
  > fixed as a budget-boundary defect, not left as an accepted flake.
- Refactoring `verify-refactor.sh` beyond the one minimal `PYTHONPATH` correction Phase 5 needs to
  make its Step 6 runnable at all.
- Re-pinning the collection count or the `xfail(strict=True)` line locations. Both are already
  verified clean and are only re-checked as pass/fail gates.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Another session's test process contends for CPU and the run is killed again | H | M | Phase 1 clear-window check; `-n 6` shrinks the exposure window to 15-25 min; Phase 2's retry ladder |
| The run exceeds the Bash tool's 600s maximum timeout and is killed by the harness, not by contention | H | H | Phase 2 mandates a backgrounded launch plus polling — a foreground invocation is guaranteed to fail |
| A truncated retry overwrites a better earlier artifact | M | M | All output goes to a staging directory first; promotion into `baselines/` happens only after the completeness and rubric checks pass |
| The two known flakes fail again and get mistaken for regressions (or vice versa) | M | M | Phase 3's three-way rubric with mandatory isolated re-run of exactly those two test IDs |
| `verify-refactor.sh` Step 6 fails on `ModuleNotFoundError: bimodal_harness` rather than on a real regression | M | H | Phase 5 corrects Step 6's `PYTHONPATH` before running, and runs from inside `nix develop` |
| `PYTEST_ADDOPTS="-n 6"` changes the in-package bimodal suite's flake behavior in Step 4 | L | M | Step 4 already allows one documented retry; if it still fails, re-run `verify-refactor.sh` without `PYTEST_ADDOPTS` and accept the longer serial Step 6 |
| A genuine regression is found and the refactor stays blocked | M | L | Phase 3 category (c) reports it as a blocker with failing test IDs and captured output; no marker is flipped and no red baseline is promoted |

## Implementation Phases

**Dependency Analysis**:

| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4, 5 | 3 |
| 5 | 6 | 4, 5 |

Phases within the same wave can execute in parallel.

---

### Phase 1: Environment and Clear-Window Preflight [COMPLETED]

- **Goal:** Confirm the interpreter, the sibling checkout, and an uncontended machine before
  spending 20 minutes of wall clock.
- **Tasks:**
  - [x] Run `ps aux | grep -E '[p]ytest|[z]3' ` and confirm no test-heavy process from another
        session is active. If one is, wait and re-check rather than starting.
  - [x] Confirm `/home/benjamin/Projects/BimodalHarness/src/bimodal_harness` exists on disk.
  - [x] Confirm the Nix devShell interpreter has `xdist`:
        `nix develop --command python3 -c "import xdist; print(xdist.__version__)"` prints `3.8.0`.
  - [x] Confirm collection is still exactly 550:
        `nix develop --command pytest oracle/bimodal_logic/tests/ --collect-only -q | tail -3`.
  - [x] Create the staging directory `specs/127_close_oracle_suite_regression_baseline/run/`. This
        directory is scratch: it is never committed and is removed in Phase 6.
- **Timing:** 15 minutes
- **Depends on:** none
- **Files to modify:** none (creates the scratch `run/` directory only)
- **Verification:**
  - `xdist.__version__` prints, `550 tests collected` reported, no foreign pytest PID listed.
  - If collection is not exactly 550, stop and report — that is itself a regression signal and
    invalidates the whole baseline exercise.

---

### Phase 2: Full-Suite Run Under `-n 6`, Backgrounded, Into Staging [COMPLETED]

- **Goal:** Get one complete 550-test run captured as both text and JUnit XML, without letting a
  harness timeout or a retry destroy a good artifact.
- **Tasks:**
  - [x] Launch the run **in the background** — the expected 15-25 minute wall clock exceeds the
        Bash tool's 600s maximum, so a foreground call will be killed by the harness and will look
        exactly like the original contention kill. Use `run_in_background: true` (or
        `nohup ... &` with the PID recorded to `run/pytest.pid`):

        ```
        RUN=specs/127_close_oracle_suite_regression_baseline/run
        nix develop --command bash -c '
          PYTHONPATH=code/src:/home/benjamin/Projects/BimodalHarness/src \
          pytest oracle/bimodal_logic/tests/ -n 6 -q \
            --junitxml='"$RUN"'/junit-oracle.xml 2>&1 | tee '"$RUN"'/oracle-run.txt
          echo "exit=${PIPESTATUS[0]}" > '"$RUN"'/exit-code.txt
        '
        ```

  - [x] Poll for completion by watching `run/oracle-run.txt` growth and the appearance of
        `run/exit-code.txt`. Do not re-launch while the first process is alive.
  - [x] Record the wall-clock duration and the recorded exit code.

  **Deviation from plan:** the actual wall clock was 44:33 (2673.06s), roughly double the
  research's 15-25 minute extrapolation, but well inside a single backgrounded call — no retry
  rung was needed. Exit code recorded was `1` (7 failing tests, not a kill): `run/exit-code.txt`
  and `run/oracle-run.txt`'s terminal summary line (`7 failed, 534 passed, 9 xfailed, 24 warnings
  in 2673.06s (0:44:33)`) both confirm completeness, and `run/junit-oracle.xml` aggregates
  `tests="550" failures="7" errors="0"`.
- **Timing:** 30 minutes agent time; 15-25 minutes unattended wall clock
- **Depends on:** 1
- **Files to modify:**
  - `specs/127_close_oracle_suite_regression_baseline/run/oracle-run.txt` — staged text output
  - `specs/127_close_oracle_suite_regression_baseline/run/junit-oracle.xml` — staged JUnit output
  - `specs/127_close_oracle_suite_regression_baseline/run/exit-code.txt` — captured pytest exit code
- **Verification (completeness, before any pass/fail judgement):**
  - `run/exit-code.txt` exists — its absence means the process died before finishing, i.e. a kill.
  - `run/oracle-run.txt` ends in a pytest summary line naming a total and a duration (e.g.
    `545 passed, 5 xfailed in 1147.32s (0:19:07)`) and its progress markers reach `[100%]`. A file
    whose last percentage marker is below 100% is truncated.
  - `run/junit-oracle.xml` is non-empty, its root element is closed, and its aggregate `tests`
    attribute is 550. `xdist` writes this file only at session end, so a zero-byte or absent XML is
    itself proof of a kill.

- **If the run is killed partway (resumption ladder — apply in order, never skip a rung):**
  1. **Never promote a truncated artifact.** Leave the staged files in place, rename the directory
     to `run/attempt-1/`, and record what the text output reached. The committed partial
     `baselines/oracle-run.txt` stays untouched until a complete run exists.
  2. **Rung 1 — retry `-n 6` in a verified clear window.** Re-run Phase 1's `ps aux` check first.
     A single contention kill is expected to be non-reproducible.
  3. **Rung 2 — retry at `-n 4`, then `-n 2`.** Lower parallelism reduces peak CPU and memory and
     is more survivable under partial contention, at the cost of wall clock (roughly 25-40 min at
     `-n 4`).
  4. **Rung 3 — shard by test file.** Run each file under `oracle/bimodal_logic/tests/` separately,
     each with its own `--junitxml=run/junit-oracle-<file>.xml` and its own tee'd text log. Then
     concatenate the text logs into a single `run/oracle-run.txt` with a clearly-delimited header
     per shard naming the file and its command, and merge the per-shard XMLs into one
     `run/junit-oracle.xml` with a short stdlib `xml.etree.ElementTree` script that sums the
     `tests`/`failures`/`errors`/`skipped` attributes and concatenates the `<testcase>` children.
     The merged XML must still total 550 tests, and the sharding must be recorded in the
     implementation summary — a sharded baseline is acceptable evidence but is not silently
     equivalent to a single-session run.
  5. **Do not** reach for `-p no:cacheprovider`, `--lf`, `--deselect`, or marker changes to make the
     run finish. Shrinking the suite to fit is not a baseline.

---

### Phase 3: Triage Against the Success Rubric and Promote [BLOCKED]

- **Goal:** Classify the completed run into exactly one of three pre-declared categories and act
  accordingly, so a flake is not mistaken for a regression and a regression is never papered over.
- **Tasks:**
  - [x] Extract the failing test IDs from `run/junit-oracle.xml` (`<testcase>` elements carrying a
        `<failure>` or `<error>` child) and cross-check them against the text summary.
  - [x] Confirm no strict-xfail XPASSed: the text summary must report no `xpassed` count, and the
        run must not have failed on an `XPASS(strict)` message. (Confirmed: text summary reports
        `9 xfailed`, no `xpassed`.)
  - [x] Classify into category (a), (b), or (c) below and take that category's action. **Result:
        category (c) — genuine regression.** See findings below.
  - [ ] On (a) or a resolved (b): copy `run/oracle-run.txt` and `run/junit-oracle.xml` into
        `specs/126_refactor_repo_core_infrastructure_theory_lib/baselines/`, overwriting the
        placeholder `oracle-run.txt` and creating `junit-oracle.xml`. **Not applicable** — category
        (c) forbids promotion; left unchecked deliberately.

  **Triage findings (per-test isolated re-runs, all serial/no-`-n`):**

  - 5 failures were NOT on the plan's watch list: `test_regression_all_active_examples[BM_CM_1-
    example_case7]`, `test_100_calls_mixed_temporal_depths`, `test_sat_unsat_interleaving_stability`,
    `test_oracle_m_formula_depth1_boundary_safe`, `test_enriched_vs_primitive_sat_agreement[some_past]`.
    Re-run together in one combined serial invocation (`run/isolated-nonwatchlist-combined.txt`):
    **5 passed in 179.26s (2:59)**. All five are `-n 6` parallel-execution artifacts (state-isolation
    and interleaving tests are not xdist-safe) — not regressions.
  - Both watch-list tests were re-run in isolation and **both still failed**, falsifying the plan's
    Category-C contention-flake premise for both:
    - `test_complexity_5_scan_self_consistent` (`run/isolated-complexity5-scan.txt`): 31:31,
      `AssertionError: Self-comparison produced 3 disagreements at complexity<=5` (`assert 3 == 0`).
    - `test_all_sat_task_relation_ternary` (`run/isolated-ternary-sat.txt`): 1:00,
      `AssertionError: Expected SAT for next_A` (`assert None is not None`).
  - **Baseline-commit check** (deviation from the plan's literal text, added to resolve refactor-
    vs-pre-existing attribution — see Plan Deviations below): both watch-list tests re-run together,
    serially, in a read-only `git worktree` at pre-refactor commit `6cfb7f48`
    (`run/baseline-6cfb7f48-watchlist.txt`): **1 failed, 1 passed in 1928.38s (32:08)**.
    - `test_all_sat_task_relation_ternary` **passed** at `6cfb7f48` but fails on the current branch
      → **refactor-introduced regression.** This is the blocking finding.
    - `test_complexity_5_scan_self_consistent` **failed** at `6cfb7f48` too
      (`AssertionError: Self-comparison produced 1 disagreements at complexity<=5`,
      `assert 1 == 0`) → pre-existing, refactor not implicated for this test. The disagreement
      *count* differs between runs (1 at baseline vs. 3 at HEAD, single sample each, on a suite
      already shown to be Z3-timing-sensitive) — this is an **open question**, not evidence of
      further degradation; resolving it would require repeated samples at both commits, which was
      not run.

  **Category (c) action taken:** stopped the plan here per the rubric. No artifacts were promoted
  into `specs/126_refactor_repo_core_infrastructure_theory_lib/baselines/`, no marker was flipped
  in the refactor plan, and no `xfail`/`skip`/`deselect` was added to any test file. Phases 4-6 are
  left `[NOT STARTED]` and must not run until `test_all_sat_task_relation_ternary` is fixed and the
  suite re-triaged.
- **Timing:** 30 minutes agent time; plus up to 5 minutes wall clock if category (b) triggers an
  isolated re-run
- **Depends on:** 2
- **Files to modify:**
  - `specs/126_refactor_repo_core_infrastructure_theory_lib/baselines/oracle-run.txt` — replaced
    with the complete run
  - `specs/126_refactor_repo_core_infrastructure_theory_lib/baselines/junit-oracle.xml` — created

**Success rubric (fixed before the run; do not renegotiate it after seeing results):**

- **(a) Fully clean.** Recorded exit code 0, zero `failures` and zero `errors` in the XML, 550 tests
  accounted for, no XPASS. **Action:** promote both artifacts and proceed to Phase 4.

- **(b) Failures confined to the known contention-flake watch list.** Every failing test ID is a
  member of:
  - `oracle/bimodal_logic/tests/test_cross_oracle_differential.py::TestFullScanReport::test_complexity_5_scan_self_consistent`
  - `oracle/bimodal_logic/tests/test_oracle_interface.py::TestTernarySerializationAll::test_all_sat_task_relation_ternary`

  **Action — mandatory isolated re-run, not an assumption.** Re-run exactly the failing IDs, one at
  a time, serially (no `-n`), from the same devShell:

  ```
  nix develop --command bash -c 'PYTHONPATH=code/src:/home/benjamin/Projects/BimodalHarness/src \
    pytest "<full::test::id>" -q' 2>&1 | tee run/isolated-<short-name>.txt
  ```

  - If every one passes in isolation, the documented Category C precedent holds. Promote the
    artifacts, and append to the promoted `baselines/oracle-run.txt` a clearly-delimited trailing
    note recording: which IDs failed under `-n 6`, the exact isolated re-run command, and its
    passing result. The note must be visibly separate from pytest's own output so the artifact is
    not mistaken for an unqualified clean run. Then proceed to Phase 4.
  - If any one **fails in isolation**, it is no longer a contention flake. Escalate it to
    category (c).

- **(c) Any new failure — a genuine regression. This is a blocker, not a nuisance.** Triggered by
  any of: a failing test ID outside the watch list; a watch-list test that fails in isolation; an
  XPASS on a strict xfail; a collection count other than 550.

  **Action:** stop the plan here.
  - Do **not** promote the artifacts into `baselines/` — the committed partial baseline is better
    evidence than a red complete one, and overwriting it destroys the only record of the prior state.
  - Do **not** flip any marker in the refactor plan (Phase 4 must not run).
  - Do **not** add `xfail`, `skip`, `deselect`, or timeout-loosening markers to make the suite green.
    Suppressing the signal is the one outcome this task exists to prevent.
  - Leave the staged output in `run/` for inspection, and report the failing test IDs, the staged
    output path, and the isolated re-run result as an explicit blocker in the implementation summary
    and the orchestrator handoff.

- **Verification:**
  - The chosen category is stated explicitly, with the evidence (exit code, failing IDs, isolated
    re-run outcomes) recorded in the implementation summary.
  - On (a) or resolved (b): both files exist in `baselines/`, are non-empty, and the XML totals 550.

---

### Phase 4: Flip the Refactor Plan's Phase 2 Markers [NOT STARTED]

- **Goal:** Make the refactor plan reflect the closed gap, at every location that currently frames
  it as open.
- **Tasks:**
  - [ ] Edit the plan-level status line (line 4 onward, spanning through line 8): change `[PARTIAL]`
        to `[COMPLETED]` and rewrite the parenthetical so it no longer says a full oracle run could
        not complete. Replace it with the current fact: all 26 phases COMPLETED, with the full
        550-test oracle run recorded in `baselines/oracle-run.txt` and `baselines/junit-oracle.xml`.
  - [ ] Edit the section heading at line 216: `### Phase 2: Pin Verification Baselines and Build the
        Regression Gate [PARTIAL]` becomes `... [COMPLETED]`, and add a `Completed:` timestamp line
        in the phase body per plan-format.md.
  - [ ] Update the three stale body cross-references at lines 1575, 1695, and 1712 so they read as
        closed rather than open, citing the baseline artifacts by filename. Rewrite them; do not
        merely delete them, and do not introduce a task-number citation (these files live under
        `specs/**` so citations are permitted, but a filename anchor is more durable).
  - [ ] Re-grep the refactor plan for remaining `PARTIAL` occurrences tied to Phase 2 or the oracle
        suite and confirm none survive with stale framing.
- **Timing:** 30 minutes
- **Depends on:** 3
- **Files to modify:**
  - `specs/126_refactor_repo_core_infrastructure_theory_lib/plans/01_core-theory-lib-refactor.md` —
    status line, Phase 2 heading, three body cross-references
- **Verification:**
  - `grep -n 'PARTIAL' specs/126_refactor_repo_core_infrastructure_theory_lib/plans/01_core-theory-lib-refactor.md`
    returns no hit that still describes the oracle run as incomplete.
  - The Phase 2 heading matches `### Phase 2: ... [COMPLETED]` exactly, with no emoji.

---

### Phase 5: Independent `verify-refactor.sh` Confirmation With Step 6 Live [NOT STARTED]

- **Goal:** Get one full green run of the regression gate with Step 6 actually executing the oracle
  suite, and make that path runnable rather than dependent on a hand-set environment.
- **Tasks:**
  - [ ] Apply the minimal `PYTHONPATH` correction to Step 6 of `code/scripts/verify-refactor.sh`: its
        oracle invocation currently uses `PYTHONPATH=code/src` only, which fails on
        `ModuleNotFoundError: No module named 'bimodal_harness'` for anyone running without
        `--skip-oracle` outside `nix develop`. Append the sibling checkout to that invocation's
        `PYTHONPATH` **conditionally on the directory existing**, matching the optional-sibling
        contract `flake.nix`'s `shellHook` already documents. This must not weaken, remove, or
        loosen any existing check — collection-count equality, the `xfail(strict=True)` line
        assertions, and the `FAILURES` accounting all stay exactly as they are.
  - [ ] Run the gate in the background (Step 4's bimodal suite plus Step 6's oracle suite together
        exceed the 600s tool ceiling by a wide margin), from inside the devShell, with `-n 6`
        supplied via `PYTEST_ADDOPTS` so Step 6 does not fall back to a 45-90 minute serial run:

        ```
        nix develop --command bash -c 'PYTEST_ADDOPTS="-n 6" bash code/scripts/verify-refactor.sh' \
          2>&1 | tee specs/127_close_oracle_suite_regression_baseline/run/verify-refactor.txt
        ```

  - [ ] Poll to completion, then confirm the script's own summary reports zero failures and it
        exited 0. Step 6 must print a real result, not `SKIPPED`.
  - [ ] If Step 4 (the in-package bimodal suite) fails under `PYTEST_ADDOPTS="-n 6"` where it passes
        serially, re-run the gate without `PYTEST_ADDOPTS` and accept the longer wall clock rather
        than declaring the gate green on a modified invocation.
- **Timing:** 45 minutes agent time; 20-40 minutes unattended wall clock
- **Depends on:** 3
- **Files to modify:**
  - `code/scripts/verify-refactor.sh` — Step 6 `PYTHONPATH` only, conditional on the sibling
    checkout existing
- **Verification:**
  - `verify-refactor.txt` shows Step 6 executing (not `SKIPPED`) and the script exiting 0 with a
    zero `FAILURES` count.
  - `git diff code/scripts/verify-refactor.sh` touches only the Step 6 `PYTHONPATH` construction.
  - A `--skip-oracle` run still behaves identically (spot-check that the skip branch is unchanged).

---

### Phase 6: Commit and Clean Up Staging [NOT STARTED]

- **Goal:** Land the baselines, the plan edits, and the script correction as one reviewable commit,
  with no scratch files left behind.
- **Tasks:**
  - [ ] Remove `specs/127_close_oracle_suite_regression_baseline/run/` (staging is never committed).
  - [ ] Stage exactly: the two `baselines/` artifacts, the refactor plan edits, the
        `verify-refactor.sh` change, this task's plan and summary, and the state/TODO updates.
        Use targeted `git add` paths — never `git add -A` or `git commit -am`.
  - [ ] Review with `git status --short` and `git diff --staged` before committing; confirm no
        unrelated or concurrent-session edits were swept in.
  - [ ] Commit as `task 127: complete implementation` with the session ID in the body.
- **Timing:** 15 minutes
- **Depends on:** 4, 5
- **Files to modify:** none beyond staging and committing the above
- **Verification:**
  - `git status --short` shows no leftover `run/` directory and no unintended staged paths.
  - `git show --stat HEAD` lists only the intended files.

## Testing & Validation

- [ ] `pytest oracle/bimodal_logic/tests/ --collect-only -q` reports exactly 550 tests.
- [ ] The full suite run reaches `[100%]`, produces a terminal summary line, and records an exit code.
- [ ] `baselines/junit-oracle.xml` aggregates to 550 tests with zero `failures` and zero `errors`
      (or, under resolved category (b), the only failures are the two watch-list IDs, each shown
      passing in an isolated re-run whose output is recorded).
- [ ] No strict-xfail XPASS anywhere in the run.
- [ ] The five `xfail(strict=True)` lines in `test_cross_oracle_differential.py` remain at 767, 942,
      1020, 1133, 1431 (asserted by `verify-refactor.sh` Step 5).
- [ ] `bash code/scripts/verify-refactor.sh` (no `--skip-oracle`) exits 0 with Step 6 executed.
- [ ] `bash code/scripts/verify-refactor.sh --skip-oracle` still exits 0 (the skip path is unchanged).
- [ ] No test file under `oracle/` was modified: `git diff --stat oracle/` is empty.

## Artifacts & Outputs

- `specs/126_refactor_repo_core_infrastructure_theory_lib/baselines/oracle-run.txt` — complete
  550-test run text output, replacing the truncated placeholder
- `specs/126_refactor_repo_core_infrastructure_theory_lib/baselines/junit-oracle.xml` — new JUnit XML
  for the same run
- `specs/126_refactor_repo_core_infrastructure_theory_lib/plans/01_core-theory-lib-refactor.md` —
  Phase 2 flipped to `[COMPLETED]`, status line and three cross-references updated
- `code/scripts/verify-refactor.sh` — Step 6 `PYTHONPATH` correction
- `specs/127_close_oracle_suite_regression_baseline/plans/01_close-oracle-regression-baseline.md` —
  this plan
- `specs/127_close_oracle_suite_regression_baseline/summaries/01_close-oracle-regression-baseline-summary.md`
  — implementation summary, recording the rubric category reached, wall-clock duration, any retry
  rung used, and whether the run was single-session or sharded

## Rollback/Contingency

- **Nothing is destroyed before it is replaced by something better.** All suite output is staged in
  `specs/127_close_oracle_suite_regression_baseline/run/` and promoted into `baselines/` only after
  the completeness checks and the rubric both pass. A truncated or red run never overwrites the
  committed partial baseline.
- **Recovering the prior partial baseline:** it is committed at `b40179c9`, so
  `git show b40179c9:specs/126_refactor_repo_core_infrastructure_theory_lib/baselines/oracle-run.txt`
  restores it without any destructive git operation. Prefer this over `git checkout --` on a dirty
  tree, which is blocked by the destructive-git guard.
- **Reverting the plan edits or the script change:** both are small, self-contained diffs; revert by
  editing forward or by `git revert` of the Phase 6 commit. Take
  `bash .claude/scripts/git-snapshot.sh` first if any rollback would discard uncommitted work.
- **If the suite cannot be completed at all** after exhausting Phase 2's ladder (including the
  per-file shard rung), the task stays open and the refactor plan's Phase 2 stays `[PARTIAL]`. Report
  the furthest rung reached, the wall clock consumed, and the kill signature. A partial run is a
  known state; a fabricated or force-fit green baseline is not recoverable from.
