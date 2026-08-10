# Implementation Plan: Verify Test-Failure Fixes and Publish Known-Failures Baseline

- **Task**: 129 - Triage pre-existing test failure backlog
- **Status**: [IMPLEMENTING]
- **Effort**: 9 hours (much of it wall-clock waiting on sweeps, not agent reasoning)
- **Dependencies**: 128, 130
- **Research Inputs**: specs/129_triage_preexisting_test_failure_backlog/reports/01_known-failures-baseline.md
- **Artifacts**: plans/01_verify-fixes-baseline-doc.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: python
- **Lean Intent**: false

## Overview

Twenty-two test fixes across 11 files (10 modified, 1 new) already exist uncommitted in the
working tree. They are **not** to be reverted or reimplemented. This plan verifies them, fixes
whatever verification proves still broken, completes the determinism mechanism that was left
half-applied, and publishes the categorized known-failures baseline document that is the task's
actual deliverable. Definition of done: every previously-failing node id is accounted for as
either verified-fixed, verified-still-failing-with-a-documented-reason, or fixed in this task; a
post-fix full sweep exists with a node-id-level failed-set diff against the pre-fix set; and
`code/docs/core/KNOWN_TEST_FAILURES.md` is committed.

### Research Integration

The research report (`reports/01_known-failures-baseline.md`) supplies the failure taxonomy and
is treated as authoritative on root causes: (A) a completely broken `create_test_model` helper
with two stacked bugs, masquerading as 14 unrelated failures; (B) stale `X[]` bracket-suffix
sentence-letter literals at 5 sites; (C) four genuine one-off defects; (D) a load-sensitive
timing/resource group. It also correctly documents three stale claims from the task description
that must not be carried forward (the `assert_and_track` failure is in
`models/tests/unit/test_structure.py`, not `iterate/tests/integration/test_generator_interface.py`;
the two ValueError message-drift tests do not exist as described).

The report is **not** authoritative on whether the fixes work. Its own verification run died to
`exit=124`. This plan supersedes its "22 fixes applied" claim with per-node-id evidence.

**Partial evidence already on disk** (`run/per-file-verify.txt`), which the report did not
interpret:

| File | Observed | Reading |
|---|---|---|
| `code/tests/e2e/test_batch_output_real.py` | `1 passed` | verified green |
| `code/src/model_checker/models/tests/unit/test_structure.py` | `16 passed` | verified green |
| `code/src/model_checker/builder/tests/unit/test_project.py` | `14 passed` | verified green |
| `code/src/model_checker/builder/tests/e2e/test_full_pipeline.py` | `3 passed` | verified green |
| `code/tests/integration/test_error_handling.py` | 11 dots then `exit=124` | partial, no failures seen |
| `code/tests/integration/test_performance.py` | `F..F....F...F.` then `exit=124` | **4 still failing** |
| `code/tests/integration/test_timeout_resources.py` | `.F...` then `exit=124` | **1 still failing** |
| `bimodal/tests/integration/test_iterate.py` | 6 dots, truncated | partial, no failures seen |
| `builder/tests/integration/test_performance.py` | never reached | unverified |

Mapping the `F` positions against a stable `--collect-only` ordering (verified this session)
gives these **suspected** still-failing node ids, to be confirmed by name in Phase 1, not
assumed:

- `tests/integration/test_performance.py::TestExecutionPerformance::test_simple_model_performance` (pos 1)
- `tests/integration/test_performance.py::TestExecutionPerformance::test_scaling_with_n[2-1.0]` (pos 4)
- `tests/integration/test_performance.py::TestMemoryPerformance::test_memory_cleanup` (pos 9)
- `tests/integration/test_performance.py::TestCachingPerformance::test_repeated_operations` (pos 13)
- `tests/integration/test_timeout_resources.py::TestTimeoutHandling::test_cli_command_timeout` (pos 2)

`test_repeated_operations` is the one the report claims to have fixed with an added outer paren
pair; if it is still failing, that fix is incomplete. `test_cli_command_timeout` was already
documented as load-sensitive and is expected here.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md consulted for this task.

## Goals & Non-Goals

**Goals**:
- Per-node-id verification evidence for all 22 existing fixes, structured so a timeout cannot
  destroy the evidence.
- Fixes for whatever Phase 1 proves still failing (starting from the five suspects above).
- ONE determinism mechanism, fully realized rather than half-applied, with the
  wall-clock-assertion vs. `max_time`-budget distinction driving which fix each test gets.
- A post-fix full sweep with a node-id-level failed-set diff against the pre-fix 27.
- `code/docs/core/KNOWN_TEST_FAILURES.md` committed and linked from the docs index.
- A decision executed (not deferred again) on `test_find_next_model_basic`.

**Non-Goals**:
- Reverting, re-deriving, or reimplementing any of the 22 existing fixes.
- Loosening wall-clock thresholds to arbitrary new literal values.
- Reaching zero failures. Some failures are legitimately environment-dependent; documenting
  them accurately is the deliverable, eliminating them is not.
- Touching production (non-test) source under `code/src/model_checker/` other than the two
  already-modified test-only files, unless Phase 4 proves a production defect.
- Enabling `pytest -n` anywhere.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| A sweep is killed and destroys evidence again (the exact prior failure) | H | H | Per-test `--timeout`, `python -u`, explicit `-v` so every result lands on its own line as it happens, `tee` to a per-file log, one file per invocation, backgrounded. Never overwrite an existing log — append or use a new name. |
| `pytest -n` is used to shorten sweeps | H | M | Explicitly forbidden below. It manufactures false failures in state-isolation and interleaving tests on this branch, which would corrupt the very baseline being built. TESTING_GUIDE 8.6 currently *recommends* `-n`; Phase 3 corrects that text. |
| Z3 ~20x solve-time variance makes a run non-reproducible | M | H | Run each suspect node id 3x before declaring it fixed or genuinely failing. Check `ps aux --sort=-%cpu` for competing load before any sweep and record what was running in the log. |
| A `max_time` overrun is misread as a real failure | H | M | Per TESTING_GUIDE 8.6 a timeout surfaces as `model_found == False`, i.e. a wrong-answer assertion, not an error. Phase 2's classification rule handles this explicitly. |
| Adding `-m "not slow"` to `addopts` silently changes CI/theory-runner behavior | M | M | Phase 3 greps for every existing `-m` usage and CI invocation first, records the collected-count delta both ways, and documents the override. |
| Pre-fix failed set is not on disk, so the required diff has no left-hand side | H | H | Phase 1 reconstructs it from the report's enumerated node ids into `run/failed-set-prefix.txt` and flags any shortfall against 27 rather than silently accepting fewer. |
| Fixing `test_find_next_model_basic` by restoring a removed method reintroduces dead API | M | M | Decision rule in Phase 4: production callers decide. No caller means the test is stale and gets rewritten, per the no-backwards-compatibility principle. |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2, 3, 4 | 1 |
| 3 | 5 | 2, 3, 4 |
| 4 | 6 | 5 |

Phases within the same wave can execute in parallel. Phases 2, 3, and 4 have disjoint file
territories (test files / config+docs / `builder/tests/unit/test_example.py`) and may be
dispatched together.

---

### Phase 1: Timeout-Hardened Per-File Verification of the Existing Fixes [IN PROGRESS]

**Goal**: Produce per-node-id pass/fail evidence for all 11 touched files, in a form that
survives a killed process, plus the reconstructed pre-fix failed set.

**The invocation contract** (use exactly this shape, one file per invocation):

```bash
cd /home/benjamin/Projects/ModelChecker/code
PYTHONPATH=src python -u -m pytest <ONE_FILE> \
  -v -rf --timeout=180 --timeout-method=thread --durations=5 \
  2>&1 | tee -a ../specs/129_triage_preexisting_test_failure_backlog/run/verify-<basename>.txt
echo "exit=${PIPESTATUS[0]}" >> ../specs/129_triage_preexisting_test_failure_backlog/run/verify-<basename>.txt
```

Why each part matters, do not drop any of them:
- `python -u` — unbuffered, so `tee` has the line on disk before a kill, not in a 4KB buffer.
- `-v` — one `PASSED`/`FAILED` line per node id as it completes. A kill then costs at most the
  in-flight test, which is exactly what the prior attempt lost.
- `--timeout=180 --timeout-method=thread` — `pytest-timeout` 2.4.0 is installed and confirmed
  working. A single hung test is killed and the run continues; the whole invocation no longer
  dies. This is the structural fix for the `exit=124` that destroyed the last attempt.
- one file per invocation, `tee -a` to a distinct per-file log — a failure in one file cannot
  cost the evidence for another.
- run each invocation via the Bash tool with `run_in_background: true`.

**FORBIDDEN**: `pytest -n` in any form. Also do not concatenate multiple files into one
invocation, and do not delete or truncate any existing file under `run/`.

**If an invocation still times out or is killed**: do not retry the whole file blindly.
1. Record the file as `PARTIAL` in the summary with the exact last node id that reported.
2. Re-invoke at node-id granularity for only the tests that had not reported yet
   (`pytest "<file>::<Class>::<test>"`), same flags.
3. If a specific node id is killed twice at 180s, mark it `UNVERIFIED (hangs)` and carry it into
   Phase 2 as a defect to triage — do not mark it passing, and do not silently omit it.
4. Never conclude "probably fine". An unverified node id is an open item, not a pass.

**Tasks**:
- [ ] Record competing load (`ps aux --sort=-%cpu | head -15`) into `run/verify-env.txt` before
      starting; if another pytest or a `lean --worker` fleet is running, note it in the log.
- [ ] Run the contract above for each of the 11 touched files (the 10 modified per
      `git status --short` plus any file importing the new `code/tests/fixtures/example_data.py`).
- [ ] For each of the 5 suspected still-failing node ids from the Overview, run it 3x
      individually and record all three outcomes (Z3 variance means 1 run proves nothing).
- [ ] Reconstruct `run/failed-set-prefix.txt`: one node id per line, extracted from the research
      report's tables (Root Cause A table = 14, Category (b) table = 4, section (a-i) = 3,
      section (a-ii) = 2, plus the Root Cause B sites and `test_empty_formula_lists`). Dedupe
      (`test_many_propositions` appears in two sections). If the deduped total is not 27, write
      the shortfall explicitly at the top of the file as
      `# UNACCOUNTED: {n} of 27 pre-fix failures not enumerated in the report` — do not pad or
      invent node ids.
- [ ] Write `run/verify-summary.md`: a table of every node id in `failed-set-prefix.txt` with
      status `VERIFIED_FIXED` / `STILL_FAILING` / `PARTIAL` / `UNVERIFIED`, plus the log file and
      failure excerpt for each non-green row.

**Timing**: 1.5-2 hours, mostly wall-clock wait. `test_performance.py` and
`test_timeout_resources.py` are the slow ones; the four already-green files take seconds.

**Depends on**: none

**Files to modify**:
- `specs/129_triage_preexisting_test_failure_backlog/run/verify-*.txt` - per-file logs (new)
- `specs/129_triage_preexisting_test_failure_backlog/run/failed-set-prefix.txt` - reconstructed pre-fix set (new)
- `specs/129_triage_preexisting_test_failure_backlog/run/verify-summary.md` - node-id status table (new)
- No source or test file is edited in this phase.

**Verification**:
- Every node id in `failed-set-prefix.txt` appears in `verify-summary.md` with a status.
- No status cell is blank or hedged.
- Commit the run logs and summary (`task 129 phase 1: verify existing fixes per-file`).

---

### Phase 2: Fix the Residual Failures Phase 1 Proves Still Broken [NOT STARTED]

**Goal**: Every `STILL_FAILING` / `UNVERIFIED (hangs)` row from Phase 1 is either fixed or
reclassified as legitimately environment-dependent with a recorded reason.

**Classification rule — apply this before writing any fix.** These three classes need different
fixes and conflating them is how the previous attempt half-solved the problem:

1. **`max_time`-budget class**: the test passes a `max_time` in its settings dict and asserts on
   a *semantic* outcome (`model_found`, `satisfiable`, "premises true / conclusion false"). Per
   TESTING_GUIDE.md 8.6 a solver timeout is reported as `model_found == False`, so the failure
   presents as a **wrong answer**, never as an error. Fix: raise `max_time` to the 30s sibling
   convention. Never lower it, never add a marker — the test is broken, not slow.
2. **Wall-clock-assertion class**: the test measures `time.time()` deltas and asserts
   `elapsed < <literal>`, with no `max_time` involved. Fix: the `slow` marker mechanism
   (Phase 3). Do **not** retune the literal threshold to a new arbitrary number.
3. **Defanged-assertion class** (specific to this codebase, found by the research): the failing
   assertion lives inside an `except Exception:` fallback branch and was only ever reachable
   because of the upstream helper bug. Such a test was never testing what it claims. Fix: make
   the happy path carry the assertion, so the test can actually catch a regression. Treat this as
   a genuine defect, not as a timing issue, and not as a candidate for the `slow` marker.

**Tasks**:
- [ ] Confirm by name (not by progress-character position) which node ids are still failing.
- [ ] Classify each into class 1, 2, or 3 above and record the classification in the fix's code
      comment.
- [ ] `test_repeated_operations`: the existing `"((A \\wedge B) \\vee (C \\wedge D))"` fix is
      suspected incomplete. Reproduce the failure, read the actual assertion, and fix the real
      cause. Do not revert the existing paren fix — build on it.
- [ ] `test_simple_model_performance`, `test_scaling_with_n[2-1.0]`, `test_memory_cleanup`: these
      are class-3 candidates (their assertions sit in except-branches per the research). Verify
      whether the assertion now runs on the happy path and fix accordingly.
- [ ] `test_cli_command_timeout`: expected class 2 / genuinely load-sensitive (real N=64 CLI
      subprocess against a 5s subprocess timeout). Already covered by its file's module-level
      `slow` marker — confirm, do not re-fix, and record it as a documented known failure for
      Phase 6 rather than forcing it green.
- [ ] Re-verify each fixed node id 3x using the Phase 1 invocation contract, appending to the
      same per-file logs.
- [ ] Update `run/verify-summary.md` statuses in place.

**Timing**: 1.5-2 hours.

**Depends on**: 1

**Files to modify**:
- `code/tests/integration/test_performance.py` - residual fixes for the confirmed failures
- `code/tests/integration/test_timeout_resources.py` - residual fixes if any beyond `test_cli_command_timeout`
- other already-touched test files only if Phase 1 proves a regression there
- `specs/129_triage_preexisting_test_failure_backlog/run/verify-summary.md` - status updates

**Verification**:
- Each fixed node id passes 3/3 individually.
- No node id remains `STILL_FAILING` without a written classification and reason.
- Commit (`task 129 phase 2: fix residual test failures`).

---

### Phase 3: Complete the Determinism Mechanism [NOT STARTED]

**Goal**: A bare `pytest` run is deterministic with respect to the load-sensitive group, with one
documented opt-in override. The mechanism is chosen, not offered as a menu.

**The mechanism**: the already-registered `slow` marker, applied as a module-level `pytestmark`
(done — three files already carry it), **plus** `-m "not slow"` added to `addopts` in
`code/pyproject.toml`. This is what actually realizes the determinism; the markers alone changed
nothing, because `addopts` does not filter them, which is why the previous attempt's fix was
inert. A CLI `-m` overrides the `addopts` value, so `-m slow` runs only the excluded group and
`-m "slow or not slow"` runs everything — both remain available without editing config.

Rejected alternatives, recorded so they are not relitigated: explicit per-assertion tolerances
(requires inventing new arbitrary thresholds, and TESTING_GUIDE 8.6's own guidance is that a
generous-looking margin still failed); a new custom marker (`slow` and `performance` are already
registered and unused, adding a third is churn); `max_time` bumps for this group (wrong class —
these are wall-clock assertions with no `max_time` involved).

**Tasks**:
- [ ] Grep for every existing `-m` usage and every pytest invocation in CI config, `code/scripts/`,
      `Makefile`/`nox` files, and the oracle tree, and record them. Confirm each still selects
      what it intends once `addopts` carries `-m "not slow"` (a CLI `-m` overrides it, so
      `-m countermodel` etc. will *include* slow tests again — verify that is acceptable for each
      call site and note any that are not).
- [ ] Add `-m "not slow"` to `addopts` in `code/pyproject.toml`.
- [ ] Record the collected-count delta: `--collect-only -q` with the new default vs.
      `-m "slow or not slow"`, into `run/collect-count-delta.txt`. The difference must equal
      exactly the tests in the three `slow`-marked files — if it does not, a marker leaked
      somewhere and must be tracked down before proceeding.
- [ ] Update `code/docs/core/TESTING_GUIDE.md` section 8.6: document the default `-m "not slow"`
      behavior, the `-m "slow or not slow"` full-validation invocation, and the
      wall-clock-vs-`max_time` classification rule from Phase 2 (it belongs in the guide, not
      only in a plan).
- [ ] In the same section, **remove the `prefer pytest -n <N>` recommendation** and replace it
      with a warning: `-n` has been demonstrated on this codebase to manufacture false failures
      in state-isolation and interleaving tests, so it must not be used for baseline or
      regression sweeps. Leaving that recommendation in place while this task forbids `-n` would
      leave the guide actively misleading.
- [ ] Update the Testing section of the root `CLAUDE.md` so the documented commands match the new
      default and show the full-sweep override.

**Timing**: 1-1.5 hours.

**Depends on**: 1

**Files to modify**:
- `code/pyproject.toml` - `addopts` gains `-m "not slow"`
- `code/docs/core/TESTING_GUIDE.md` - section 8.6: default invocation, classification rule, `-n` warning
- `CLAUDE.md` - Testing commands
- `specs/129_triage_preexisting_test_failure_backlog/run/collect-count-delta.txt` - count evidence (new)

**Verification**:
- `PYTHONPATH=src pytest --collect-only -q` excludes exactly the three `slow`-marked files.
- `PYTHONPATH=src pytest -m "slow or not slow" --collect-only -q` collects the full pre-change set.
- No task numbers appear in any file outside `specs/**` (this phase edits deliverables).
- Commit (`task 129 phase 3: complete slow-marker determinism mechanism`).

---

### Phase 4: Resolve `test_find_next_model_basic` [NOT STARTED]

**Goal**: The one item the research explicitly deferred is decided and executed.

**Decision rule** (do not defer a second time):
1. Grep the whole of `code/src/` and `oracle/` for `find_next_model`.
2. **No production caller** — the method genuinely does not exist and nothing wants it: the test
   is stale. **Rewrite** it against the current `model_checker.iterate` API, which is where
   iteration actually lives. This is the recommended and expected outcome, and it follows the
   project's no-backwards-compatibility principle: do not resurrect a removed method to satisfy a
   test.
3. **A production caller exists** — then this is a production defect, not a test defect. Do not
   rewrite the test. Mark it `[BLOCKED]`, record the caller in the handoff blockers, and leave it
   for a task that may touch production source.

**Tasks**:
- [ ] Run the grep and record the result in the phase notes.
- [ ] Execute branch 2 or 3 per the rule.
- [ ] If rewriting: the new test must exercise real iteration behavior (a second distinct model
      is produced), not merely assert that an attribute exists. Use `max_time: 30` per the 8.6
      convention.
- [ ] Verify with the Phase 1 invocation contract, 3 runs.

**Timing**: 1-1.5 hours.

**Depends on**: 1

**Files to modify**:
- `code/src/model_checker/builder/tests/unit/test_example.py` - rewrite `test_find_next_model_basic`

**Verification**:
- `test_example.py` passes in full, 3/3.
- Commit (`task 129 phase 4: rewrite find_next_model test against iterate API`).

---

### Phase 5: Post-Fix Full Sweep and Node-ID Failed-Set Diff [NOT STARTED]

**Goal**: Prove by node id that failures were removed and none were introduced. A bare count is
not acceptable evidence.

**Sweep contract**:

```bash
cd /home/benjamin/Projects/ModelChecker/code
PYTHONPATH=src python -u -m pytest src/model_checker/ tests/ \
  -m "slow or not slow" -v -rf --timeout=300 --timeout-method=thread \
  2>&1 | tee ../specs/129_triage_preexisting_test_failure_backlog/run/full-sweep-postfix.txt
```

`-m "slow or not slow"` is mandatory: the pre-fix 27/2148 sweep was unfiltered, so an
apples-to-apples comparison must override Phase 3's new `addopts` default. Run backgrounded.
`pytest -n` remains forbidden. Check and record competing load first.

**If the sweep is killed**: the per-test `--timeout` plus `-v` means the log still holds a
`PASSED`/`FAILED` line for every test that ran. Do not restart from zero. Record how far it got,
then resume with `--lf`-style targeting or by splitting the two testpaths into separate
invocations (`src/model_checker/` and `tests/` are independent) and concatenate the results.
Two half-sweeps with full node-id coverage beat one destroyed full sweep.

**Tasks**:
- [ ] Run the sweep (backgrounded) and also a default-invocation sweep (no `-m` override) so both
      the deterministic-default count and the everything count are on record.
- [ ] Extract the post-fix failed set to `run/failed-set-postfix.txt`, one node id per line,
      sorted.
- [ ] Produce `run/failed-set-diff.txt`: `comm`-style three-way split of
      `failed-set-prefix.txt` vs `failed-set-postfix.txt` — **Removed** (fixed), **Retained**
      (still failing), **Introduced** (new, i.e. regressions caused by this task's edits).
- [ ] Any node id in **Introduced** is a regression and blocks this phase. Fix it and re-sweep;
      do not carry it into the baseline document as if it were pre-existing.
- [ ] Record both counts and the total collected in `run/sweep-counts.txt` alongside the pre-fix
      27 failed / 2148 passed / 75 subtests reference.

**Timing**: 1.5-2 hours, dominated by two sweeps at roughly 5-15 minutes each plus retries under
load.

**Depends on**: 2, 3, 4

**Files to modify**:
- `specs/129_triage_preexisting_test_failure_backlog/run/full-sweep-postfix.txt` (new)
- `specs/129_triage_preexisting_test_failure_backlog/run/failed-set-postfix.txt` (new)
- `specs/129_triage_preexisting_test_failure_backlog/run/failed-set-diff.txt` (new)
- `specs/129_triage_preexisting_test_failure_backlog/run/sweep-counts.txt` (new)
- Source files only if a regression is found in **Introduced**.

**Verification**:
- `failed-set-diff.txt` exists with all three sections populated (empty **Introduced** is the
  goal and must be stated explicitly as empty, not omitted).
- Every node id in **Retained** has a corresponding row in `verify-summary.md` with a reason.
- Commit (`task 129 phase 5: post-fix full sweep and failed-set diff`).

---

### Phase 6: Publish the Known-Failures Baseline Document [NOT STARTED]

**Goal**: The task's actual deliverable — a committed, categorized statement of what legitimately
still fails and why, usable as a diff target by future refactors.

**Location**: `code/docs/core/KNOWN_TEST_FAILURES.md`, linked from `code/docs/core/README.md` and
cross-referenced from TESTING_GUIDE.md section 8.6. This is a deliverable outside `specs/**`:
**no task numbers, no "task N" citations, no plan/report path references**. Cite durable anchors
instead — file paths, section headings, the commit that established the baseline.

**Required content**:
- The baseline invocation, verbatim and copy-pasteable, in both forms (deterministic default and
  full `-m "slow or not slow"`), with the counts each produces and the commit SHA they were
  measured at.
- The categorized still-failing list, one row per node id: node id, category, why it fails, and
  whether it is expected to fail on a clean machine or only under load. Categories:
  environment-dependent wall-clock assertion; environment-dependent solver budget; genuine open
  defect. Every row traceable to Phase 5's **Retained** set — no rows without evidence.
- The wall-clock vs. `max_time`-budget distinction, stated as guidance for whoever reads a future
  failure: a `max_time` overrun presents as a wrong answer, not an error, so an inverted semantic
  assertion should be checked against the budget before being treated as a logic bug.
- The `-n` prohibition and its reason, so the baseline is not later invalidated by a parallel run.
- Explicitly: what was fixed in establishing this baseline, at the level of root cause (broken
  `create_test_model` helper; stale `X[]` bracket-suffix sentence-letter literals; unspecced
  `patch('z3.Solver')` tripping the mock assert-prefix typo guard; hardcoded default-theory
  assertion; bimodal `World Histories` vs `State Space` output header; too-tight bimodal iterate
  `max_time`). This is what makes the document a baseline rather than a snapshot.
- A note that several of the "performance" and "timeout" tests were previously passing via
  `except Exception:` fallback branches and therefore could not have caught a real regression;
  they now assert on the happy path. Future readers need this to understand why the pass counts
  moved.

**Tasks**:
- [ ] Write `code/docs/core/KNOWN_TEST_FAILURES.md` from Phase 5's evidence files. Do not restate
      any claim that Phase 1/5 did not verify.
- [ ] Add it to the navigation table in `code/docs/core/README.md`.
- [ ] Add a cross-reference from TESTING_GUIDE.md section 8.6.
- [ ] Re-read the finished document and confirm zero task-number references and zero `specs/`
      paths.
- [ ] Write `specs/129_triage_preexisting_test_failure_backlog/summaries/01_verify-fixes-baseline-doc-summary.md`.

**Timing**: 1.5 hours.

**Depends on**: 5

**Files to modify**:
- `code/docs/core/KNOWN_TEST_FAILURES.md` - the baseline deliverable (new)
- `code/docs/core/README.md` - navigation entry
- `code/docs/core/TESTING_GUIDE.md` - cross-reference from 8.6
- `specs/129_triage_preexisting_test_failure_backlog/summaries/01_verify-fixes-baseline-doc-summary.md` (new)

**Verification**:
- Every row in the document's still-failing table maps to a node id in
  `run/failed-set-diff.txt`'s **Retained** section, and vice versa.
- `grep -nEi 'task [0-9]|specs/' code/docs/core/KNOWN_TEST_FAILURES.md` returns nothing.
- Commit (`task 129 phase 6: publish known-failures baseline document`).

---

## Testing & Validation

- [ ] All 11 touched files have per-file verification logs under `run/` with per-node-id results.
- [ ] Each of the 5 suspected still-failing node ids has 3 recorded outcomes.
- [ ] `run/failed-set-diff.txt` shows an empty **Introduced** section, stated explicitly.
- [ ] `pytest --collect-only -q` (default) excludes exactly the three `slow`-marked files;
      `-m "slow or not slow"` restores the full set.
- [ ] `code/src/model_checker/builder/tests/unit/test_example.py` passes in full, 3/3.
- [ ] `KNOWN_TEST_FAILURES.md` rows and the **Retained** set are in exact correspondence.
- [ ] No `pytest -n` invocation appears anywhere in this task's logs, scripts, or docs edits.

## Artifacts & Outputs

- `specs/129_triage_preexisting_test_failure_backlog/plans/01_verify-fixes-baseline-doc.md` (this file)
- `specs/129_triage_preexisting_test_failure_backlog/run/verify-env.txt`
- `specs/129_triage_preexisting_test_failure_backlog/run/verify-<basename>.txt` (11 files)
- `specs/129_triage_preexisting_test_failure_backlog/run/verify-summary.md`
- `specs/129_triage_preexisting_test_failure_backlog/run/failed-set-prefix.txt`
- `specs/129_triage_preexisting_test_failure_backlog/run/failed-set-postfix.txt`
- `specs/129_triage_preexisting_test_failure_backlog/run/failed-set-diff.txt`
- `specs/129_triage_preexisting_test_failure_backlog/run/full-sweep-postfix.txt`
- `specs/129_triage_preexisting_test_failure_backlog/run/sweep-counts.txt`
- `specs/129_triage_preexisting_test_failure_backlog/run/collect-count-delta.txt`
- `specs/129_triage_preexisting_test_failure_backlog/summaries/01_verify-fixes-baseline-doc-summary.md`
- `code/docs/core/KNOWN_TEST_FAILURES.md` (primary deliverable)

## Rollback/Contingency

The 22 pre-existing fixes are uncommitted at plan time. Before Phase 1's first edit-bearing
phase (Phase 2), snapshot with `bash .claude/scripts/git-snapshot.sh` so the existing work has a
durable `.patch` under the task directory. Never run `git reset --hard`, `git checkout -- <path>`,
or `git clean -fd` against this working tree — the 22 fixes are the task's inherited asset and
the user has explicitly approved keeping all of them, including `code/tests/utils/helpers.py` and
the bimodal `test_iterate.py`.

Each phase commits independently, so rollback is per-phase `git revert` of a single commit:
- Phase 3 is the highest-blast-radius change (`pyproject.toml` `addopts` affects every
  invocation). Reverting that one commit fully restores prior behavior; the module-level `slow`
  markers are inert without it.
- Phase 6 is documentation only, safe to revert or rewrite.
- Phases 2 and 4 are test-file-scoped.

If Phase 5's sweep proves unrunnable in this environment even split in half, do not fabricate a
count: mark Phase 5 `[BLOCKED]`, record the environment evidence, and write
`KNOWN_TEST_FAILURES.md` from Phase 1/2's per-file evidence with an explicit statement that the
whole-suite cross-check is outstanding. A document that is honest about its evidence base is
still the deliverable; one that reports an unverified sweep count is not.
