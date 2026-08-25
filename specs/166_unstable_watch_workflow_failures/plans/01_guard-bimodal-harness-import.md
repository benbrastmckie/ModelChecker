# Implementation Plan: Guard the bimodal_harness Import in the Oracle Test Tree

- **Task**: 166 - Research and fix recurring unstable-watch.yml GitHub Actions failures
- **Status**: [NOT STARTED]
- **Effort**: 3 hours
- **Dependencies**: None
- **Research Inputs**: specs/166_unstable_watch_workflow_failures/reports/01_root-cause-and-fix-recommendation.md
- **Artifacts**: plans/01_guard-bimodal-harness-import.md (this file)
- **Standards**: plan-format.md; status-markers.md; artifact-management.md; tasks.md
- **Type**: general
- **Lean Intent**: false

## Overview

`unstable-watch.yml` has failed on 13/13 runs since creation, always with the same pytest
**collection** error: `oracle/bimodal_logic/tests/test_oracle_interface.py` lines 37-38 carry
unconditional, module-level `from bimodal_harness...` imports for a package that is not part of
this repository, is not declared in `code/pyproject.toml`, and is never installed by any CI
workflow. Because pytest must import a module before it can read its markers, this crashes
collection before `-m unstable` deselection can apply, so the workflow's already-correct exit-code-5
("no unstable tests in the oracle tree") path is never reached. The fix is to apply the guarded-import
pattern already proven in the sibling file `test_cross_oracle_differential.py`, extracted into one
shared helper module, and to lock the fix in with a regression test that collects the whole
`oracle/bimodal_logic/tests/` directory with `bimodal_harness` forcibly unavailable. Definition of
done: that regression test passes, the exact `unstable-watch.yml` oracle invocation exits 0 or 5 with
`bimodal_harness` blocked, and no previously-passing oracle test changes outcome when
BimodalHarness *is* available.

### Research Integration

Findings from `reports/01_root-cause-and-fix-recommendation.md` integrated into this plan:

- **Single root cause, not flakiness.** All 13 runs share a byte-identical signature; no
  ModelChecker semantic regression, no solver-timing noise, no dependency drift. The plan therefore
  contains no investigation phase — the diagnosis is settled.
- **Precedent exists in-tree.** `test_cross_oracle_differential.py:1236-1255` already implements
  `_try_import_bimodal_harness()` (path-existence check, conditional `sys.path.insert`,
  `try/except ImportError`, module-level `_BH_AVAILABLE` flag consumed by `pytest.skip()` in
  `setup_method`). Phases 2-3 reuse this pattern rather than inventing one.
- **The local mask.** On the original author's machine the sibling file sorts first
  (`c` < `o`), its `sys.path.insert` runs during collection, and the later unguarded import
  inherits a working path as an accidental side effect. Every verification step in this plan must
  therefore *block* `bimodal_harness` explicitly — a plain local run proves nothing.
- **Rejected alternatives** (do not revisit): installing/vendoring `bimodal_harness` in CI,
  soft-failing the oracle step, retiring the workflow. Rationale is recorded in the research
  report's "Recommended Long-Term Solution" section.
- **Documentation gap named by the research**: `TESTING_GUIDE.md` has no stated convention for
  optional, developer-local external test dependencies. Phase 4 closes it.

Confirmed during planning by direct inspection (narrowing the fix surface below what the research
left open): across the entire `oracle/` tree, `test_oracle_interface.py:37-38` are the **only**
unguarded module-level `bimodal_harness` imports. Every other reference is either function-local
with its own `try/except` (including `test_oracle_interface.py:1061`) or inside the already-guarded
sibling. The two guarded symbols are consumed by exactly three tests:
`TestOracleProtocolCompliance.test_provider_implements_protocol` (uses `OracleProvider`) and
`TestEntryPointDiscovery.test_oracle_registry_discover` /
`test_discovered_provider_is_correct_type` (use `OracleRegistry`). All other tests in the module
are BimodalHarness-independent and must remain collectible and running.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md consulted for this task.

## Goals & Non-Goals

**Goals**:
- Make `oracle/bimodal_logic/tests/` fully collectible on any machine without `bimodal_harness`,
  with the three dependent tests skipping rather than crashing collection.
- Land a regression test that fails today and passes after the fix, so this class of defect cannot
  recur silently in a future test file.
- Factor the guard into one shared helper consumed by both files, eliminating the duplicated
  pattern the research flagged.
- Restore `unstable-watch.yml` to green (oracle step reaching its already-handled exit code 5).
- Document the required pattern for optional developer-local test dependencies.

**Non-Goals**:
- Installing, vendoring, or declaring `bimodal_harness` as a real dependency.
- Changing `unstable-watch.yml`'s classification logic, streak accounting, or non-gating contract.
- Adding `@pytest.mark.unstable` to any oracle test (the oracle tree legitimately has none).
- Touching `differential-tests.yml` or `tests.yml`.
- Any git push, branch publication, pull request, or `/merge` invocation. Per
  `.claude/rules/pr-prohibition.md` the implementer commits locally only and stops.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Verification passes locally only because BimodalHarness really is present on this machine, repeating the exact mask that hid the bug | H | H | Every verification step in every phase runs under an explicit `sys.meta_path` blocker that raises `ImportError` for `bimodal_harness`; a run without the blocker is never accepted as evidence |
| Extracting the helper touches `test_cross_oracle_differential.py`, which `differential-tests.yml` gates on | M | M | Phase 2 is a pure move with no behavior change; verify by running that workflow's exact invocations both with and without the blocker before proceeding |
| Shared-module import path proves fragile under pytest's prepend import mode | M | L | `oracle/bimodal_logic/tests/__init__.py` exists, so a relative import resolves; if it does not, fall back to duplicating the ~15-line helper in `test_oracle_interface.py` (explicit fallback recorded in Phase 2) |
| Skipping the three dependent tests reduces real coverage | L | H (by design) | Already the accepted trade-off for `TestBimodalHarnessIntegration` in the sibling; gate at *test* granularity, never class or module, so the ~10 other classes keep running |
| Adding `skipif` above the existing `xfail(strict=True)` marks changes reporting semantics | L | M | `skipif` is evaluated first, so the tests report as skipped, not as strict-xfail failures; assert this explicitly in Phase 3 verification |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4 | 3 |

Phases within the same wave can execute in parallel. This plan is fully sequential.

---

### Phase 1: Reproduce the CI failure and add the failing regression test [NOT STARTED]

- **Goal:** Establish RED. Reproduce the exact CI collection crash locally under a
  `bimodal_harness` blocker, then commit a regression test that fails for that reason.
- **Tasks:**
  - [ ] Reproduce the raw defect: `PYTHONPATH=code/src python -m pytest oracle/bimodal_logic/tests/test_oracle_interface.py --collect-only -q` and confirm `ModuleNotFoundError: No module named 'bimodal_harness'`.
  - [ ] Create `oracle/bimodal_logic/tests/test_bimodal_harness_guard.py`. It MUST NOT import `bimodal_harness` at module level (that would reintroduce the very defect).
  - [ ] Implement a subprocess-based blocker harness in that file: launch `python -c` in a child process that first inserts a `sys.meta_path` finder whose `find_spec` raises `ImportError` for `bimodal_harness` and any `bimodal_harness.*` submodule, then calls `pytest.main([...])`. Pass `PYTHONPATH=code/src` through the child environment. The blocker is what simulates every CI runner; do not substitute a `sys.modules` deletion or a `monkeypatch`, neither of which survives into a fresh collection.
  - [ ] Add the primary regression test: run `--collect-only -q` over the whole `oracle/bimodal_logic/tests/` directory under the blocker and assert the child exits 0 with no `ERROR collecting` and no `ModuleNotFoundError` in its output. Directory scope, not file scope — this is the scope `unstable-watch.yml` actually uses and the scope that would catch a future offender.
  - [ ] Add a second, narrower regression test asserting the same for `test_oracle_interface.py` alone, so a failure localizes immediately.
  - [ ] Give the file a module docstring naming the failure mode it prevents and pointing at the shared helper as the required pattern.
  - [ ] Run the new tests and confirm BOTH FAIL against unmodified source. Record the failure output.
  - [ ] Confirm `--collect-only` in the child cannot recurse: the child collects but never executes this file's own tests.
- **Timing:** 45 minutes
- **Depends on:** none
- **Verification Tier:** local
- **Scope Hypothesis:** Planning asserts that `test_oracle_interface.py:37-38` are the only unguarded module-level `bimodal_harness` imports in `oracle/`. Confirm at implementation time with `grep -rn "^from bimodal_harness\|^import bimodal_harness" oracle/ --include=*.py`; if the directory-scoped regression test reports a collection error in any file other than `test_oracle_interface.py`, the hypothesis is refuted and Phase 3's scope must widen to cover that file too.
- **Files to modify:**
  - `oracle/bimodal_logic/tests/test_bimodal_harness_guard.py` - new file; blocker harness plus two failing regression tests
- **Verification:**
  - `PYTHONPATH=code/src python -m pytest oracle/bimodal_logic/tests/test_bimodal_harness_guard.py -v` reports both new tests FAILING, with the failure message showing the `ModuleNotFoundError: No module named 'bimodal_harness'` collection error from the child process.
  - The new file itself collects cleanly under the blocker (self-consistency check).

---

### Phase 2: Extract the guard into a shared helper module [NOT STARTED]

- **Goal:** Move `_try_import_bimodal_harness()` out of `test_cross_oracle_differential.py` into one
  shared module both test files can consume, with zero behavior change.
- **Tasks:**
  - [ ] Create `oracle/bimodal_logic/tests/_bimodal_harness.py` (leading underscore: not a test module). Move the helper verbatim from `test_cross_oracle_differential.py:1236-1253`, preserving the existence check on `/home/benjamin/Projects/BimodalHarness/src`, the conditional `sys.path.insert`, and the `try/except ImportError`.
  - [ ] Export a module-level `BH_AVAILABLE` flag and a `BH_SKIP_REASON` string constant so both consumers share one skip message instead of two hand-written ones.
  - [ ] Give the module a docstring stating that any test file in this tree touching `bimodal_harness` must import from here rather than importing `bimodal_harness` at module scope.
  - [ ] Update `test_cross_oracle_differential.py` to import from the shared module and delete the local helper definition. Keep the existing `_BH_AVAILABLE` / `_BH_MODULE` names bound to the shared values so the ~7 downstream reference sites in that file need no edits.
  - [ ] Confirm the import resolves under pytest's prepend import mode (the `tests/` and `bimodal_logic/` packages both have `__init__.py`; `oracle/` does not, so `oracle/` lands on `sys.path` and both a relative import and `bimodal_logic.tests._bimodal_harness` resolve).
  - [ ] Fallback if that import proves fragile: abandon extraction, duplicate the helper directly in `test_oracle_interface.py`, revert this phase's edit to the sibling, and record the decision in the phase notes. Do not spend more than 20 minutes on import-path debugging before taking the fallback.
- **Timing:** 30 minutes
- **Depends on:** 1
- **Verification Tier:** interface
- **Scope Hypothesis:** This phase asserts it touches exactly two files (one new, one edited) and that `test_cross_oracle_differential.py` has ~7 internal reference sites to `_BH_AVAILABLE`/`_BH_MODULE` that the alias preserves. Confirm with `grep -n "_BH_AVAILABLE\|_BH_MODULE\|_try_import_bimodal_harness" oracle/bimodal_logic/tests/test_cross_oracle_differential.py` before and after; the before/after counts must match and no site may be left referencing a deleted name.
- **Files to modify:**
  - `oracle/bimodal_logic/tests/_bimodal_harness.py` - new shared guard module
  - `oracle/bimodal_logic/tests/test_cross_oracle_differential.py` - import the shared helper, delete the local definition, keep existing names as aliases
- **Verification:**
  - `PYTHONPATH=code/src python -m pytest oracle/bimodal_logic/tests/test_cross_oracle_differential.py --collect-only -q` succeeds unchanged.
  - Run `differential-tests.yml`'s own invocations against `test_cross_oracle_differential.py` (its non-slow, no-BimodalHarness selection) and confirm identical pass/skip counts to a pre-change baseline captured at the start of this phase.
  - Repeat that run under the Phase 1 blocker and confirm the BimodalHarness-dependent tests still skip cleanly rather than erroring.
  - Phase 1's regression tests still FAIL (this phase does not fix the defect and must not appear to).

---

### Phase 3: Guard test_oracle_interface.py and gate the three dependent tests [NOT STARTED]

- **Goal:** Turn Phase 1 GREEN. Remove the two unguarded module-level imports and skip only the
  tests that genuinely need them.
- **Tasks:**
  - [ ] Delete `from bimodal_harness.oracle.protocol import OracleProvider` and `from bimodal_harness.oracle.registry import OracleRegistry` at `test_oracle_interface.py:37-38`.
  - [ ] Import `BH_AVAILABLE` and `BH_SKIP_REASON` from the shared module instead, and resolve `OracleProvider` / `OracleRegistry` only when available (module-level conditional binding to `None` otherwise, so the names still exist for the skipped tests' bodies).
  - [ ] Gate `TestOracleProtocolCompliance.test_provider_implements_protocol` with `@pytest.mark.skipif(not BH_AVAILABLE, reason=BH_SKIP_REASON)`. Gate at test granularity — the other tests in that class do not use `OracleProvider` and MUST keep running.
  - [ ] Gate `TestEntryPointDiscovery.test_oracle_registry_discover` and `test_discovered_provider_is_correct_type` the same way, stacking `skipif` above the existing `@pytest.mark.xfail(strict=True, ...)` marks. Leave `test_entry_point_registered` and `test_entry_point_loads_correct_class` untouched — they use only `importlib.metadata` and have no BimodalHarness dependency.
  - [ ] Verify (do not modify) that `TestSpotCheckCrossSignal._get_spot_check_formulas` at line 1061 is already correctly guarded by its own `try/except ImportError` returning `None`, and that its callers handle `None`. If a caller does not, gate that caller too.
  - [ ] Confirm no other symbol in the module resolves through `bimodal_harness`.
- **Timing:** 45 minutes
- **Depends on:** 2
- **Verification Tier:** interface
- **Scope Hypothesis:** This phase asserts exactly three tests require the guarded symbols (one in `TestOracleProtocolCompliance`, two in `TestEntryPointDiscovery`) and that the other ~10 test classes in the module are BimodalHarness-independent. Confirm at implementation time with `grep -n "OracleProvider\|OracleRegistry" oracle/bimodal_logic/tests/test_oracle_interface.py`, excluding `Z3OracleProvider` matches, which are a different symbol from `bimodal_logic` and must NOT be gated. If more than three tests match, widen the gating and record the corrected count.
- **Files to modify:**
  - `oracle/bimodal_logic/tests/test_oracle_interface.py` - replace unguarded imports with the shared guard; add three `skipif` marks
- **Verification:**
  - Phase 1's two regression tests now PASS.
  - Under the blocker: `PYTHONPATH=code/src python -m pytest oracle/bimodal_logic/tests/ --collect-only -q` reports zero collection errors.
  - Under the blocker, run `test_oracle_interface.py` and confirm exactly three tests report as `SKIPPED` (not `XFAIL`, not `ERROR`) and that every other test in the module runs to its normal outcome.
  - WITHOUT the blocker (BimodalHarness present on this machine): run `test_oracle_interface.py` and confirm the pass/fail/xfail counts are identical to a baseline captured before this phase's edit — the fix must be invisible when the dependency is available.

---

### Phase 4: Verify the workflow invocation, record the narrowing decision, document the pattern [NOT STARTED]

- **Goal:** Prove the actual CI condition is fixed, close the documentation gap, and record the
  defense-in-depth decision explicitly.
- **Tasks:**
  - [ ] Run the exact `unstable-watch.yml` oracle-step invocation from the repo root under the blocker: `PYTHONPATH=code/src python -m pytest oracle/bimodal_logic/tests/ -m unstable -v --junitxml=/tmp/watch-oracle.xml`. Capture the exit code and assert it is 0 or 5 (the workflow treats both as success; with no `unstable`-marked oracle test present, 5 is the expected value).
  - [ ] Inspect `/tmp/watch-oracle.xml` and confirm it contains no `<error>` element — this is what the workflow's `classify` step parses, and an error element is what produced the `NEW` classification that failed every run.
  - [ ] Run the code-tree step too (`cd code && PYTHONPATH=src python -m pytest tests/ src/model_checker -m unstable -v --junitxml=/tmp/watch-code.xml`) to confirm it is still green and this change did not perturb it.
  - [ ] **Record the workflow-narrowing decision.** Decision: do NOT narrow `unstable-watch.yml`'s oracle step to an explicit filename list. Rationale: the directory-wide scope is precisely what surfaced this defect, and the Phase 1 regression test now enforces directory-wide portability from inside the repo on every suite run — a stronger, self-maintaining guard than a workflow-level allowlist that a contributor must remember to update. Narrowing would also silently exclude any future genuinely `unstable`-marked oracle test from the watch the workflow exists to perform, and would restore the blind spot rather than remove it. Write this decision and rationale into the implementation summary so a future reader does not re-open it.
  - [ ] Add a short subsection to `code/docs/core/TESTING_GUIDE.md` (adjacent to the section 8.9 `unstable`-marker material) naming `oracle/bimodal_logic/tests/_bimodal_harness.py` as the required pattern for any test file depending on an external, developer-local package, and stating the rule: never import such a package at module scope. Per `.claude/rules/no-task-references-in-deliverables.md`, cite file paths and section headings only — no task-number references in this file.
  - [ ] Add a one-line pointer comment at the top of both `test_oracle_interface.py` and `test_cross_oracle_differential.py` directing readers to the shared helper.
  - [ ] Commit locally. Do NOT push, do NOT open a pull request, do NOT invoke `/merge`.
- **Timing:** 45 minutes
- **Depends on:** 3
- **Verification Tier:** full
- **Files to modify:**
  - `code/docs/core/TESTING_GUIDE.md` - new subsection on optional developer-local test dependencies
  - `oracle/bimodal_logic/tests/test_oracle_interface.py` - pointer comment
  - `oracle/bimodal_logic/tests/test_cross_oracle_differential.py` - pointer comment
- **Verification:**
  - Workflow oracle-step invocation under the blocker exits 0 or 5, and `/tmp/watch-oracle.xml` has no `<error>` element.
  - Workflow code-step invocation still passes its one `unstable`-marked test.
  - Full oracle suite (`PYTHONPATH=code/src python -m pytest oracle/bimodal_logic/tests/ -q`) shows no regression against the pre-change baseline, both with and without the blocker.
  - `git log --oneline -1` shows a local commit; `git status` confirms nothing was pushed.

---

## Testing & Validation

- [ ] `oracle/bimodal_logic/tests/test_bimodal_harness_guard.py` fails before Phase 3 and passes after (RED -> GREEN, per `code/docs/core/TESTING_GUIDE.md`).
- [ ] Whole-directory `--collect-only` under an explicit `bimodal_harness` blocker: zero collection errors.
- [ ] Exact `unstable-watch.yml` oracle-step command under the blocker: exit code 0 or 5, JUnit XML free of `<error>` elements.
- [ ] Exact `unstable-watch.yml` code-step command: unchanged, still green.
- [ ] `differential-tests.yml`'s invocations against `test_cross_oracle_differential.py`: identical counts to the pre-change baseline.
- [ ] With BimodalHarness available: `test_oracle_interface.py` pass/fail/xfail counts identical to the pre-change baseline.
- [ ] Under the blocker: exactly the three BimodalHarness-dependent tests report `SKIPPED`; no test reports `ERROR`.
- [ ] `PYTHONPATH=code/src pytest code/tests/ -v` unaffected (this change does not touch `code/`).

## Artifacts & Outputs

- `oracle/bimodal_logic/tests/_bimodal_harness.py` (new) - shared guarded-import helper
- `oracle/bimodal_logic/tests/test_bimodal_harness_guard.py` (new) - portability regression test
- `oracle/bimodal_logic/tests/test_oracle_interface.py` (modified) - guarded imports, three `skipif` marks
- `oracle/bimodal_logic/tests/test_cross_oracle_differential.py` (modified) - consumes the shared helper
- `code/docs/core/TESTING_GUIDE.md` (modified) - optional-external-dependency convention
- `specs/166_unstable_watch_workflow_failures/summaries/01_guard-bimodal-harness-import-summary.md` - implementation summary, including the recorded workflow-narrowing decision

## Rollback/Contingency

- All changes are confined to test files and one documentation file; no production `model_checker`
  source is touched, so the blast radius of a revert is nil.
- Revert path: `git revert` the phase commits in reverse order. Phase 2 is independently revertible
  (see its in-phase fallback to duplicating the helper), and Phase 3's fix does not depend on
  Phase 2 having taken the shared-module route.
- If the shared-module extraction destabilizes `test_cross_oracle_differential.py` in any way, take
  Phase 2's recorded fallback: revert the sibling to its current local helper and duplicate the
  guard in `test_oracle_interface.py`. That variant still fully satisfies Phase 1's regression test
  and closes the CI failure; only the de-duplication goal is given up.
- If, after the fix, `unstable-watch.yml` still fails on its next scheduled run for a *different*
  reason, that is a new failure mode outside this plan's diagnosis — capture it with
  `gh run view <id> --log-failed` and open a follow-up rather than widening this task.
