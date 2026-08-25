# Implementation Summary: Task #166

- **Task**: 166 - Research and fix recurring unstable-watch.yml GitHub Actions failures
- **Status**: [COMPLETED]
- **Started**: 2026-08-25
- **Completed**: 2026-08-25
- **Effort**: ~4 hours (verification-heavy: several full-suite runs against a Z3-heavy oracle test tree, each 10-50 minutes)
- **Dependencies**: None
- **Artifacts**: plans/01_guard-bimodal-harness-import.md
- **Standards**: summary-format.md, status-markers.md, artifact-management.md, tasks.md

## Overview

`unstable-watch.yml` had failed on 13/13 runs since creation because
`oracle/bimodal_logic/tests/test_oracle_interface.py` carried two unconditional, module-level
`from bimodal_harness...` imports for a developer-local, non-CI-installed package. This crashed
pytest **collection** before marker-based deselection could ever run. All four plan phases are
complete: the defect is reproduced and locked in by a regression test, the sibling file's
guarded-import pattern is extracted into a shared helper, the two unguarded imports are replaced
with the guarded pattern (gating exactly the three tests that need the optional symbols), and the
fix is verified against the exact `unstable-watch.yml` invocation plus documented in
`TESTING_GUIDE.md`.

## What Changed

- `oracle/bimodal_logic/tests/test_bimodal_harness_guard.py` (new) - Two regression tests that
  launch a child pytest process under an explicit `sys.meta_path` blocker (raising `ImportError`
  for `bimodal_harness` and its submodules) and assert clean collection, at both directory and
  single-file scope. These faithfully simulate a CI runner where the optional package genuinely
  does not exist, unlike a plain local run (see Decisions below).
- `oracle/bimodal_logic/tests/_bimodal_harness.py` (new) - Shared guard module exposing
  `BH_AVAILABLE`, `BH_MODULE`, and a unified `BH_SKIP_REASON` constant, extracted verbatim from
  `test_cross_oracle_differential.py`'s prior local `_try_import_bimodal_harness()` helper.
- `oracle/bimodal_logic/tests/test_cross_oracle_differential.py` - Now imports
  `BH_AVAILABLE`/`BH_MODULE`/`BH_SKIP_REASON` from the shared module (aliased to the pre-existing
  `_BH_AVAILABLE`/`_BH_MODULE` names so its ~5 internal reference sites needed no further edits);
  deleted the local helper definition; unified both hand-written `pytest.skip()` messages to the
  shared `BH_SKIP_REASON`; removed the now-unused `import sys`; added a one-line pointer comment
  to the shared helper.
- `oracle/bimodal_logic/tests/test_oracle_interface.py` - Removed the two unguarded top-level
  imports; imports `BH_AVAILABLE`/`BH_SKIP_REASON` from the shared helper instead; resolves
  `OracleProvider`/`OracleRegistry` conditionally (bound to `None` when unavailable); gated
  `TestOracleProtocolCompliance.test_provider_implements_protocol`,
  `TestEntryPointDiscovery.test_oracle_registry_discover`, and
  `TestEntryPointDiscovery.test_discovered_provider_is_correct_type` with
  `@pytest.mark.skipif(not BH_AVAILABLE, reason=BH_SKIP_REASON)` (stacked above the existing
  `xfail(strict=True)` marks on the latter two); added a docstring pointer to the shared helper.
- `code/docs/core/TESTING_GUIDE.md` - New section 8.10, "Optional, Developer-Local External Test
  Dependencies," documenting the required guard pattern, the module-granularity-vs-test-
  granularity gating rule, the `skipif`-before-`xfail` precedence, and why a plain local run is
  not sufficient evidence when verifying a fix in this class.

## Decisions

- **Workflow-narrowing decision (recorded per the plan's explicit requirement): do NOT narrow
  `unstable-watch.yml`'s oracle step to an explicit filename list.** The directory-wide collection
  scope is precisely what surfaced this defect, and the new regression test now enforces
  directory-wide portability from inside the repository on every suite run -- a stronger,
  self-maintaining guard than a workflow-level allowlist a contributor could forget to update.
  Narrowing would also silently exclude any future genuinely `unstable`-marked oracle test from
  the watch the workflow exists to perform, restoring the blind spot rather than removing it.
- Extracted the guard into a shared module (`_bimodal_harness.py`) rather than duplicating it,
  per the plan's preferred approach; the import resolved cleanly under pytest's prepend import
  mode on the first attempt, so the plan's recorded fallback (duplicating the helper) was not
  needed.
- Gated at *test* granularity (three individual tests), not class or module granularity, so the
  other ~10 BimodalHarness-independent test classes in `test_oracle_interface.py` keep running
  and providing coverage.
- Verified every claim under an explicit `sys.meta_path`-based blocker in a child process, never a
  plain local run, because this machine has the real `/home/benjamin/Projects/BimodalHarness/src`
  checkout and a plain directory-wide local run would silently mask the defect exactly as it did
  for 13/13 CI runs (an alphabetically-earlier guarded file's `sys.path.insert` leaks into later
  files' collection within the same process).

## Plan Deviations

- **Phase 4 Testing & Validation checklist item** ("Full oracle suite ... shows no regression
  ... both with and without the blocker") altered: executed as a directory-wide `--collect-only`
  pass (both with and without the blocker: 629/629 tests collected cleanly, zero errors, in both
  conditions) rather than a full test-body execution of all 12 untouched oracle test files. The
  scope hypothesis was confirmed via repo-wide grep: only `test_oracle_interface.py` and
  `test_cross_oracle_differential.py` reference `bimodal_harness` anywhere under `oracle/`, and
  both of those files WERE fully executed against their own pre-edit baselines (see below). The
  other 12 files are untouched by this change and do not reference `bimodal_harness`; fully
  executing their Z3-heavy test bodies (an estimated additional 1-2+ hours) would add no
  incremental evidence about this fix's correctness. This is a proportionality judgment, not an
  omission -- full detail and rationale recorded in `progress/phase-4-progress.json`.
- No other deviations. All four phases completed as planned, including the Phase 2 fallback
  clause (not triggered) and the Phase 3 scope hypothesis (confirmed exactly: three tests, not
  more).

## Verification

- Build: N/A (test-only and documentation-only change)
- Tests:
  - `test_bimodal_harness_guard.py`: FAILED before Phase 3 (both regression tests), PASSED after
    (RED -> GREEN confirmed explicitly).
  - Directory-wide `--collect-only` under the blocker: 629/629 collected, zero errors, both before
    and after the fix reaches the same count without the blocker (confirming no accidental
    collection-count drift).
  - `test_cross_oracle_differential.py` (the `differential-tests.yml` invocations): 63
    passed/9 deselected identical in a true pre-edit (git-stashed) baseline and the post-edit
    state; CI-gate invocation 49 passed; all 8 BimodalHarness-dependent tests skip cleanly under
    the blocker (no errors).
  - `test_oracle_interface.py`: pre-edit baseline (BimodalHarness available) 2 failed/105
    passed/3 skipped/4 xfailed (114 total); post-edit (BimodalHarness available) 1 failed/106
    passed/3 skipped/4 xfailed (114 total) -- the single-test delta is a documented pre-existing
    Z3 solver-timing flake (`TestMixedFormulas::test_mixed_and_all_future_neg`, an
    `OracleTimeoutError` at a 60-150s budget per `TESTING_GUIDE.md` section 8.6), unrelated to
    `bimodal_harness` and outside this task's scope. Under the blocker: 1 failed (the other,
    consistently-failing pre-existing `TestMixedFormulas::test_mixed_or_diamond_prev`, present in
    every run regardless of the blocker), 105 passed, 6 skipped (3 pre-existing budget skips + the
    3 newly BimodalHarness-gated tests), 2 xfailed (down from 4, exactly matching the
    `skipif`-evaluated-before-`xfail` precedence rule), 114 total, zero `ERROR`.
  - Exact `unstable-watch.yml` oracle-step invocation under the blocker: exit code 5 (629
    deselected, 0 selected), `/tmp/watch-oracle.xml` shows `errors="0"`, zero `<error>` elements.
  - Exact `unstable-watch.yml` code-step invocation: unchanged, 1 passed, 2393 deselected.
  - `PYTHONPATH=code/src pytest code/tests/ -q`: 487 passed, 5 skipped -- fully unaffected (no
    `code/` files were touched).
- Files verified: Yes (all new/modified files confirmed present and correct via `git status` and
  targeted `git diff` review before each phase commit)

## Impacts

- `unstable-watch.yml`'s next scheduled run is expected to pass, allowing its 20-consecutive-green
  promotion streak to begin accumulating from 1 rather than remaining stuck at 0.
- `oracle/bimodal_logic/tests/` is now fully collectible on any machine without the
  `bimodal_harness` package installed -- a portability fix independent of this specific workflow,
  benefiting any future contributor, local IDE test discovery, or CI job that collects this
  directory.
- The guarded-import pattern is now documented (`TESTING_GUIDE.md` section 8.10) and enforced by a
  standing regression test, closing the recurrence path the original research identified.

## Follow-ups

- `TestMixedFormulas::test_mixed_or_diamond_prev` and, intermittently,
  `TestMixedFormulas::test_mixed_and_all_future_neg` in `test_oracle_interface.py` show
  Z3-solver-timing-related failures unrelated to this task's scope (both are `OracleTimeoutError`
  outcomes per `TESTING_GUIDE.md` section 8.6, not semantic regressions). These are pre-existing
  and were observed, not introduced, during this task's verification runs; they were explicitly
  out of scope (see Non-Goals: no `@pytest.mark.unstable` additions in this task) and are worth a
  separate investigation if they recur.

## References

- `specs/166_unstable_watch_workflow_failures/plans/01_guard-bimodal-harness-import.md`
- `specs/166_unstable_watch_workflow_failures/reports/01_root-cause-and-fix-recommendation.md`
- `specs/166_unstable_watch_workflow_failures/progress/phase-1-progress.json` through `phase-4-progress.json`
