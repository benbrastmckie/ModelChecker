# Implementation Plan: Deterministic, correctly-named bimodal BuildExample integration test

- **Task**: 130 - Make `builder/tests/unit/test_example.py::TestBuildExampleIntegration::test_logos_extensional_theory` deterministic and correctly named
- **Status**: [IMPLEMENTING]
- **Effort**: 1.25 hours
- **Dependencies**: None
- **Research Inputs**: `specs/130_stabilize_order_dependent_builder_test/reports/01_order-dependent-test-diagnosis.md`
- **Artifacts**: plans/01_deterministic-bimodal-builder-test.md (this file)
- **Standards**:
  - `.claude/context/formats/plan-format.md`
  - `.claude/context/formats/status-markers.md`
  - `.claude/rules/artifact-formats.md`
  - `.claude/rules/state-management.md`
  - `code/docs/core/TESTING_GUIDE.md`
- **Type**: python
- **Lean Intent**: false

## Overview

A single integration test in `code/src/model_checker/builder/tests/unit/test_example.py` is both
misnamed and non-deterministic. Its body builds a **bimodal** theory example (not logos, and not a
restricted extensional fragment), and its `SIMPLE` example sets only `N`, so `max_time` silently
inherits `BimodalSemantics.DEFAULT_EXAMPLE_SETTINGS['max_time'] = 1` while the actual Z3 solve
takes ~1.7s — the assertion outcome is therefore a race against a too-tight deadline. The fix is
entirely contained in that one test file: rename the test and correct its bimodal framing, give the
`SIMPLE` example explicit `max_time` headroom, and verify the outcome is identical across isolated,
file-scope, and full-builder-suite invocations. Definition of done: the renamed test passes
identically in all three invocation modes, with no new failures introduced elsewhere in the builder
suite.

### Research Integration

Findings from `reports/01_order-dependent-test-diagnosis.md` that this plan takes as settled and
does not re-investigate:

- **Root cause is a timeout race, not state leakage.** The report searched for and ruled out every
  candidate leakage mechanism (bimodal `get_theory` caching, settings-merge mutation, module-level
  Z3 context/`set_param`, model-level memoization). A fresh Z3 context is used per solve. The only
  defect is the budget: ~1.7s of real solve time against an inherited 1s `max_time`.
- **The `model_found=True` assertion is semantically sound.** `bimodal.get_theory(config=None)`
  accepts but entirely ignores its `config` argument, always returning the full bimodal theory. `A`
  alone does not entail `B` under bimodal semantics; the countermodel exists and *is* found once
  `max_time` is raised (verified at `max_time: 10`, solver run time 1.6883s). So the assertion stays
  as-is — only the budget and the name change.
- **The name is wrong on two counts**: wrong theory (bimodal, not logos) and it implies an
  "extensional" restriction that `get_theory` never applies. Recommended replacement, matching the
  file's `test_build_example_*` sibling convention:
  `test_build_example_bimodal_theory_countermodel`.
- **Current observed polarity**: on this branch the test FAILS deterministically in all three
  invocations. The previously-documented "passes only in the full suite" polarity did not reproduce.
  Phase 1 re-confirms the actual pre-change baseline rather than assuming either polarity.

### Prior Plan Reference

No prior plan for this task.

### Roadmap Alignment

No `roadmap_path` was provided in the delegation context and no roadmap phases are requested, so no
ROADMAP.md consultation applies to this plan.

## Goals & Non-Goals

**Goals**:
- Rename `test_logos_extensional_theory` to `test_build_example_bimodal_theory_countermodel`, and
  correct its docstring and in-body comments so they describe the bimodal theory the body actually
  loads (dropping the `logos` / `extensional` / "without complex operators" framing).
- Give the test's `SIMPLE` example explicit `max_time` headroom so the ~1.7s solve is never
  decided by machine timing or invocation context.
- Prove determinism empirically: identical result in an isolated node-id run, a file-scope run, and
  a full `builder/tests/` suite run.
- Keep all changes inside `code/src/model_checker/builder/tests/unit/test_example.py`.

**Non-Goals**:
- Fixing `bimodal.get_theory`'s ignored `config` argument (follow-up candidate; outside file scope).
- Fixing `test_find_next_model_basic` in the same class, which fails separately with
  `AttributeError: 'BuildExample' object has no attribute 'find_next_model'` and also omits
  `max_time` (follow-up candidate; explicitly excluded from this task).
- Fixing the other pre-existing failures in the builder suite (6 failed / 238 passed baseline).
- Changing the test's assertion semantics, `N`, or any production source file.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Chosen `max_time` headroom is still too tight on a loaded machine | M | L | Use `max_time: 10`, ~6x the measured 1.6883s solve; sibling bimodal examples in `theory_lib/bimodal/examples.py` use 5-30s for comparable N/M. Phase 4 records the actual solver runtime to confirm the margin empirically. |
| Rename breaks an external reference to the old test name | L | L | Verified: the only code reference is the `def` at `test_example.py:312`. All other hits are in `specs/**` (task artifacts and historical baselines), which are records of past runs and must not be rewritten. Phase 2 re-greps to confirm. |
| Full-suite verification is misread as "must be all green" | M | M | The builder suite has documented pre-existing failures (`specs/122_rootcause_crossoracle_differential_and_establish_t/baselines/builder-suite-pre-existing-failures.txt`). Phase 1 captures the exact pre-change FAILED set; Phase 4 diffs against it so success = target test flipped to pass, zero other changes — not an all-green suite. |
| Test passes for the wrong reason (e.g. still timing out but assertion coincidentally satisfied) | M | L | Phase 4 confirms the model is genuinely found by checking the reported solver runtime is well under budget and no TIMEOUT is emitted, not merely that the assertion passed. |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4 | 3 |

Phases within the same wave can execute in parallel. This plan is fully sequential: all phases edit
or verify the same test method, and the verification phase requires the baseline from Phase 1.

---

### Phase 1: Capture pre-change three-invocation baseline [COMPLETED]

**Goal**: Record the exact current behavior of the target test in all three invocation modes, plus
the full-suite FAILED set, so Phase 4 can prove the change did what it claims and nothing else.

**Tasks**:
- [x] Create `specs/130_stabilize_order_dependent_builder_test/baselines/` if absent.
- [x] Run the isolated invocation and record pass/fail plus the assertion message:
      `PYTHONPATH=code/src pytest "code/src/model_checker/builder/tests/unit/test_example.py::TestBuildExampleIntegration::test_logos_extensional_theory" -v`
- [x] Run the file-scope invocation and record the result for the target test:
      `PYTHONPATH=code/src pytest code/src/model_checker/builder/tests/unit/test_example.py -v`
- [x] Run the full builder suite and record the sorted list of `FAILED` lines plus the
      failed/passed counts:
      `PYTHONPATH=code/src pytest code/src/model_checker/builder/tests/ -v`
- [x] Save all three outputs under `baselines/` (e.g. `pre-change-three-invocations.txt` and a
      sorted `pre-change-failed-set.txt` containing only the `FAILED ...` lines from the full-suite
      run).

**Deviation (observed polarity)**: the plan's "Current observed polarity" note (see Research
Integration above) stated the test "FAILS deterministically in all three invocations" on this
branch. Actual Phase 1 measurement contradicts that: isolated run FAILS (`AssertionError: False is
not true`, 1.29s call), but both the file-scope run (9 passed/1 failed, target PASSED at 0.16s)
and the full-suite run (239 passed/5 failed, target PASSED at 0.17s) show the target test PASSING.
This is consistent with the root-cause diagnosis (a timeout race against `max_time: 1`) and is, if
anything, a cleaner demonstration of the order-dependent flakiness the task is named for. Full
builder-suite pre-existing FAILED set is 5 (not the plan's referenced 6-failure historical
baseline from `specs/122_.../baselines/`); the 5 failures are unrelated pre-existing issues
(`test_theory_library_execution`, `test_multiple_examples_process_efficiently`,
`test_small_model_generation_completes_quickly`, `test_find_next_model_basic`,
`test_project_initialization_default`) and match the "not part of this plan" scope.

**Timing**: 20 minutes (dominated by suite runtime)

**Depends on**: none

**Files to modify**:
- `specs/130_stabilize_order_dependent_builder_test/baselines/*` - new baseline capture files (task
  artifacts, not production code; outside the code file_scope by design)

**Verification**:
- Baseline files exist, are non-empty, and each of the three invocations has a recorded outcome for
  the target test.
- The sorted pre-change FAILED set is captured and includes the target test.

---

### Phase 2: Rename the test and correct its bimodal framing [COMPLETED]

**Goal**: The test's name, docstring, and comments accurately describe what the body does — build a
`BuildExample` over the full bimodal theory and assert a countermodel is found.

**Tasks**:
- [x] Rename `def test_logos_extensional_theory` to
      `def test_build_example_bimodal_theory_countermodel`.
- [x] Replace the docstring `"""Test BuildExample with logos extensional theory."""` with wording
      that names the bimodal theory and the countermodel assertion, and notes that
      `get_theory`'s config argument has no effect (so the loaded theory is the full bimodal one).
- [x] Update the misleading in-body comment `# Simple test without complex operators` — the loaded
      theory has the full bimodal operator set; describe the example as a simple premise/conclusion
      pair instead.
- [x] Update the `# Simple example A premises, B conclusion - should find a countermodel` comment to
      drop any logos/extensional framing and state the bimodal expectation.
- [x] Leave the `assertTrue(result["model_found"], ...)` assertion and its message semantically
      intact (the research established the expectation is sound); reword only if the message itself
      implies logos/extensional.
- [x] Consider renaming the local temp file `logos_test.py` written by the test to a bimodal-accurate
      name for consistency (cosmetic, same file, no external dependency). Renamed to
      `bimodal_test.py`.
- [x] Re-grep the repository for `test_logos_extensional_theory` and confirm no remaining reference
      outside `specs/**`.

**Deviation (additional edits beyond the plan's explicit list)**: the `semantic_theories` dict key
and the two downstream `build_module.semantic_theories["Extensional"]` /
`BuildExample(..., "Extensional")` references were also renamed to `"Bimodal"` for internal
consistency with the new test name and docstring — the plan's task list did not call this out
explicitly, but leaving the old `"Extensional"` key/label in place after the rename would have
reintroduced the same misleading framing the rename is meant to fix. The docstring's initial
draft literally quoted `extensional` (from `get_theory(['extensional'])`) to explain the ignored
`config` argument; reworded to describe the argument generically without repeating the word, to
satisfy the "no occurrence of `logos`/`extensional`" verification bullet below. The literal
`get_theory(['extensional'])` call inside the test's inline module-content string is unchanged
(it is the real API call under test, not comment/docstring framing).

**Timing**: 15 minutes

**Depends on**: 1

**Files to modify**:
- `code/src/model_checker/builder/tests/unit/test_example.py` - rename the method at line 312, fix
  its docstring and the comments at roughly lines 313, 319, and 350

**Verification**:
- `PYTHONPATH=code/src pytest "code/src/model_checker/builder/tests/unit/test_example.py::TestBuildExampleIntegration::test_build_example_bimodal_theory_countermodel" -v`
  collects and runs the test under its new node id (it is still expected to FAIL at this phase — the
  timing fix lands in Phase 3; a collection error is a real failure, an assertion failure is not).
- `grep -rn "test_logos_extensional_theory" code/` returns nothing.
- No occurrence of `logos` or `extensional` remains in the renamed test's name, docstring, or
  comments.

---

### Phase 3: Give the SIMPLE example explicit max_time headroom [NOT STARTED]

**Goal**: Remove the timing race by setting `max_time` explicitly instead of inheriting the 1s
bimodal default, so the ~1.7s solve always completes.

**Tasks**:
- [ ] In the renamed test's inline module content, change
      `example_range = {"SIMPLE": [["A"], ["B"], {"N": 2}]}` to include `"max_time": 10` in the
      settings dict.
- [ ] Add a short comment on that line explaining why the explicit budget exists: the bimodal
      default is 1s, the real solve is ~1.7s, so an inherited default makes the outcome
      machine-timing-dependent.
- [ ] Do not change `N` (or add `M`) — the research measured ~1.7s at the existing `N=2` / default
      `M=2`, and changing the search space would invalidate that measurement.
- [ ] Confirm the change is confined to the renamed test's module content string; the other
      `example_range` literals in this file belong to out-of-scope tests and stay untouched.

**Timing**: 10 minutes

**Depends on**: 2

**Files to modify**:
- `code/src/model_checker/builder/tests/unit/test_example.py` - the `SIMPLE` example settings dict
  inside the renamed test's inline module content (around line 320)

**Verification**:
- `PYTHONPATH=code/src pytest "code/src/model_checker/builder/tests/unit/test_example.py::TestBuildExampleIntegration::test_build_example_bimodal_theory_countermodel" -v`
  now PASSES.
- `git diff` on the test file shows exactly one settings-dict change plus the Phase 2 naming and
  comment edits, and no edits to any other test's `example_range`.

---

### Phase 4: Verify determinism across all three invocations [NOT STARTED]

**Goal**: Prove the outcome is identical in isolation, at file scope, and in the full builder suite,
and that nothing else in the suite changed.

**Tasks**:
- [ ] Isolated run, by node id, at least twice:
      `PYTHONPATH=code/src pytest "code/src/model_checker/builder/tests/unit/test_example.py::TestBuildExampleIntegration::test_build_example_bimodal_theory_countermodel" -v`
- [ ] File-scope run:
      `PYTHONPATH=code/src pytest code/src/model_checker/builder/tests/unit/test_example.py -v`
- [ ] Full builder suite run:
      `PYTHONPATH=code/src pytest code/src/model_checker/builder/tests/ -v`
- [ ] Confirm the target test PASSES in all three, every run — identical result, not merely
      "passes somewhere".
- [ ] Confirm the pass is genuine, not a coincidence: check the run reports a real solve (no
      `TIMEOUT: Model search exceeded maximum time` for this example) and that the observed solve
      duration leaves clear margin under the configured budget. Record the observed duration.
- [ ] Diff the post-change sorted FAILED set from the full-suite run against Phase 1's
      `pre-change-failed-set.txt` (e.g. `comm -13` / `comm -23`): the only permitted difference is
      the target test's removal. Any newly-appearing FAILED line is a regression and must be fixed
      before the phase is complete.
- [ ] Save the post-change outputs and the diff under
      `specs/130_stabilize_order_dependent_builder_test/baselines/`.

**Timing**: 25 minutes (dominated by repeated suite runs)

**Depends on**: 3

**Files to modify**:
- `specs/130_stabilize_order_dependent_builder_test/baselines/*` - post-change verification records

**Verification**:
- Target test PASSES in isolated (x2), file-scope, and full-suite invocations — three-for-three,
  repeated.
- Observed solve duration recorded and comfortably below the configured `max_time`.
- FAILED-set diff shows exactly one removal (the target test) and zero additions.
- `test_find_next_model_basic`'s pre-existing failure is still present and unchanged — expected,
  since it is explicitly out of scope, and it must not be silently reported as fixed.

---

## Testing & Validation

- [ ] `PYTHONPATH=code/src pytest "code/src/model_checker/builder/tests/unit/test_example.py::TestBuildExampleIntegration::test_build_example_bimodal_theory_countermodel" -v` passes on repeated isolated runs.
- [ ] `PYTHONPATH=code/src pytest code/src/model_checker/builder/tests/unit/test_example.py -v` — target test passes; only the known out-of-scope `test_find_next_model_basic` failure remains from this file.
- [ ] `PYTHONPATH=code/src pytest code/src/model_checker/builder/tests/ -v` — target test passes; FAILED set differs from the Phase 1 baseline by exactly the target test's removal.
- [ ] `grep -rn "test_logos_extensional_theory" code/` returns no matches.
- [ ] No occurrence of `logos` or `extensional` in the renamed test's name, docstring, or comments.
- [ ] `git diff --stat` shows exactly one changed file under `code/`: `code/src/model_checker/builder/tests/unit/test_example.py`.

## Artifacts & Outputs

- `code/src/model_checker/builder/tests/unit/test_example.py` — renamed test with corrected bimodal
  docstring/comments and an explicit `max_time` on its `SIMPLE` example.
- `specs/130_stabilize_order_dependent_builder_test/baselines/pre-change-three-invocations.txt`
- `specs/130_stabilize_order_dependent_builder_test/baselines/pre-change-failed-set.txt`
- `specs/130_stabilize_order_dependent_builder_test/baselines/post-change-three-invocations.txt`
- `specs/130_stabilize_order_dependent_builder_test/baselines/failed-set-diff.txt`
- `specs/130_stabilize_order_dependent_builder_test/summaries/01_deterministic-bimodal-builder-test-summary.md`
  (written at implementation completion)

### Follow-Up Candidates (not part of this plan)

Recorded from the research report; deliberately excluded from this task's scope:

- `theory_lib/bimodal/__init__.py`'s `get_theory(config=None)` accepts and silently ignores its
  `config` argument, so every `get_theory(['extensional'])` call site in the codebase gets the full
  bimodal theory. Any expectation of operator-set restriction is currently false repository-wide.
- `test_find_next_model_basic` (same class, same file) fails with `AttributeError: 'BuildExample'
  object has no attribute 'find_next_model'` and also omits `max_time` on its `SAT` example — the
  same missing-headroom pattern this plan fixes for one test applies to it too.

## Rollback/Contingency

All production-code changes are confined to a single test file, so reverting is a one-file
operation: `git checkout HEAD -- code/src/model_checker/builder/tests/unit/test_example.py` restores
the pre-change state (subject to the working-tree safety rule in `.claude/rules/git-workflow.md` —
snapshot first if other uncommitted changes exist). The baseline artifacts under `specs/` are
additive records and can be left in place, since they document the investigation regardless of
whether the fix lands.

If Phase 4 shows the test still flakes at `max_time: 10`, the contingency is to raise the budget
further (sibling bimodal examples use up to 30s) and re-run Phase 4 rather than to weaken the
assertion — the research established the countermodel genuinely exists, so a failure to find it
remains a budget problem, not an assertion problem.
