# Implementation Plan: Ground the Wall-Clock Performance Budgets

- **Task**: 136 - ground_wallclock_performance_budgets
- **Status**: [IMPLEMENTING]
- **Effort**: 6 hours
- **Dependencies**: None (task 135 is complete through its Phase 6; its Phase 7 is absorbed here — see "Relationship to Task 135")
- **Research Inputs**: specs/136_ground_wallclock_performance_budgets/reports/01_wallclock-budget-grounding.md
- **Artifacts**: plans/01_wallclock-budget-grounding.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: python
- **Lean Intent**: false

## Overview

Three test files carry 24 wall-clock assertions whose pass/fail state changes between identical
runs on the same commit, which is why `code/pyproject.toml` still quarantines them behind
`addopts = ... -m "not slow"`. The research measured every one of them and found a single
structural cause: the quantity being measured is not the code's cost but the bimodal theory's
`max_time` cap (default `1` second). Two assertions are arithmetically unreachable, fifteen are
vacuous, seven are correctness tests wearing a stopwatch, four are hang guards, and one is a
genuine Z3-free micro-benchmark. This plan applies those dispositions file by file, removes the
now-unneeded `slow` marks from all three files, deletes the `-m "not slow"` quarantine clause,
and verifies the result with three separate unfiltered full-suite invocations that must produce
an **identical** green result set.

**Definition of done**: every affected test either passes reliably across repeat full-suite
samples or has been removed; markers narrowed to exactly one remaining `slow`-marked test
repo-wide; the `-m "not slow"` addopts clause deleted; an unfiltered run verified green and
repeatable across at least 3 separate invocations.

### Research Integration

The report is authoritative and materially reshapes the task. The findings this plan is built on:

1. **Root cause (report §4)**: `BimodalSemantics.DEFAULT_EXAMPLE_SETTINGS` sets `max_time: 1`,
   and neither `create_test_model` nor the builder tests' generated modules override it. Measured
   elapsed is `min(real_solve_time, max_time) + overhead`, so every N ∈ {2,3,4,8} measures
   ≈1.03 s. Budgets of 0.5 s and 1.0 s sit *inside* or *below* that distribution.
2. **No budget needs re-grounding (report §6.4)**: category (a) — "real regression guard needing a
   measured p95/p99 budget" — is **empty**. Zero assertions survive as performance guards.
3. **Relative-scaling ratios measured and rejected (report §5)**: under the cap all ratios are
   ≈1.0 and vacuous; lift the cap and identical input varies 129x in-process, so a ratio compounds
   two noisy measurements rather than cancelling them. Do not build one.
4. **Marker state already partly narrowed (report §2)**: two of the three files were narrowed from
   module-level `pytestmark` to per-class marks by commit `aebf7a23`. Only the builder file still
   carries a module-level mark (line 31). `-m slow` collects **41** tests, not 43 (verified again
   at plan time: `41/2195 tests collected`).
5. **Both concurrency tests are already unmarked and pass**. Re-marking them would regress prior
   work. Leave `TestConcurrentPerformance::test_sequential_vs_concurrent` and
   `TestResourceLimits::test_concurrent_model_building` completely untouched.
6. **Segfault blocker resolved**: an unfiltered run (`-m ""`, 2195 collected) completed
   3 failed / 2192 passed in 6:13 with no interpreter abort.
7. **Cap-burn is free cost (report §7)**: ~20 s of the ~65 s quarantined runtime is spent waiting
   out `max_time` for solves whose result is never inspected. Setting a small explicit `max_time`
   on those tests cuts cost ~90% *and* removes their timing sensitivity.

### Divergence From the Original Task Description (stated, not scope drift)

The task description anticipated deriving p95/p99 budgets across repeat samples and re-grounding
the assertions. **The measurement does not support that framing.** A p95 of a distribution whose
ceiling is the `max_time` cap describes the cap, not the code. This plan therefore *drops or
converts* assertions where the description anticipated *re-budgeting* them. Two further specific
supersessions:

- The description named the two concurrency tests as "the two concurrency crashers" to be marked
  `slow`. They are already rewritten, unmarked, and green. **Not re-marked here.**
- The description's marker list assumed three module-level `pytestmark` lines. Only one remains.

Additionally, "narrow the module-level marker to per-test marks on only the tests that justify
it" resolves — after the dispositions below — to an **empty** justified set for all three files.
The marks are therefore deleted outright rather than pushed down to per-test marks. This is the
same instruction carried to its measured conclusion, not a reduction of scope.

### Relationship to Task 135

Task 135 is complete through its Phases 1-6. Its **only** remaining work is Phase 7: deleting the
`-m "not slow"` clause, deleting the TEMPORARY comment block at `code/pyproject.toml:85-103`, and
updating the `slow` marker description — hard-gated on this task. Phase 5 of this plan performs
exactly that deletion, and Phase 6 applies task 135's own verification bar, carried verbatim:

> run the unfiltered suite 3 times as separate invocations requiring an identical green result set

Doing the deletion here avoids a further dispatch round-trip. Task 135's Phase 7 is thereby
**satisfied by reference** and must be marked complete rather than performed a second time
(Phase 7 of this plan).

### Roadmap Alignment

No `specs/ROADMAP.md` was provided in the delegation context and none was loaded. No roadmap
phases are included.

## Goals & Non-Goals

**Goals**:
- Eliminate every wall-clock assertion in the three named files whose budget is measured against
  the `max_time` cap rather than the code's real cost.
- Preserve or strengthen assertion power: every test that loses a timing clause either gains a
  behavioural assertion or is deleted outright as vacuous.
- Reduce cap-burn on tests that never inspect the solve result, so un-quarantining does not
  materially slow the default run.
- Remove all `slow` marks from the three files, leaving exactly one `slow`-marked test repo-wide.
- Delete the `-m "not slow"` quarantine clause and its TEMPORARY comment block; rewrite the
  `slow` marker description so it no longer claims a quarantine that no longer exists.
- Verify with 3 separate unfiltered invocations producing an identical green result set.

**Non-Goals**:
- Building a benchmark harness. Report §5.3 establishes that trustworthy timing here requires
  subprocess isolation plus repeat sampling — that is an opt-in benchmarking job, not a unit test.
  Do not build one; do not add `pytest-benchmark`.
- Re-grounding any budget from measured p95/p99. Category (a) is empty.
- Fixing `bimodal`'s default `max_time: 1` being below its own examples' real solve time
  (report §9.1). Real, but a separate audit with semantic consequences.
- Fixing `bimodal.get_theory(subtheories)` ignoring its argument (report §9.2).
- Fixing `BaseExampleTest.validate_example` doing no model checking (report §9.3).
- Any edit under `oracle/` — concurrent work is active there.
- Re-marking either concurrency test.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| An out-of-scope, load-sensitive test (e.g. the bimodal `BM_CM_4` example, observed at 21.39 s against a 30 s budget in prior full-suite work) breaks the identical-result-set bar in Phase 6 | H | M | Run the three sweeps with no concurrent oracle suite active. If a failure outside the three named files appears, do NOT declare green: record it, reproduce it in isolation, and follow the Phase 6 contingency (revert the Phase 5 commit and report a blocker) rather than shipping a red default run. |
| Deleting the quarantine makes the default run materially slower | M | L | Cap-burn reduction is folded into Phases 1-3. Report §7 estimates net addition ~35 s on a ~5:37 baseline (~+10%). Measure the filtered-run wall time in Phase 4 and the unfiltered wall time in Phase 6 and record both. |
| A "convert to behavioural assertion" rewrite asserts something that is not actually true of the code (e.g. `get_theory` is not identity-cached; `Syntax` exposes no comparable structure) | M | M | Every conversion below carries an explicit fallback. Run the converted test before committing; if the intended property does not hold, take the stated fallback and record the finding in the summary. Never assert a property you have not observed to hold. |
| Deleting tests is mistaken for lost coverage | M | M | A vacuous assertion that cannot fail is not coverage. Each deletion below cites its measured justification. The summary must enumerate every deleted test with its reason. |
| Hang guards depend on `pytest-timeout`, which is installed in this environment but not declared in `code/pyproject.toml`'s `dev` extra | M | M | Verified present at plan time. Phase 5 declares it in the `dev` extra so the guards do not silently vanish elsewhere (stated scope addition — see Phase 5). |
| Repeat unfiltered sweeps are expensive (~6:13 each, ~19 min for three) | L | H | Budgeted in Phase 6. Run them as background invocations; do not interleave other heavy work on the machine. |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 2, 3 | -- |
| 2 | 4 | 1, 2, 3 |
| 3 | 5 | 4 |
| 4 | 6 | 5 |
| 5 | 7 | 6 |

Phases within the same wave can execute in parallel. Phases 1-3 are territory-disjoint (one file
each) and may be dispatched concurrently.

**Territory contract for Wave 1** — no phase may edit a file owned by another:
- Phase 1 owns `code/src/model_checker/builder/tests/integration/test_performance.py`
- Phase 2 owns `code/tests/integration/test_performance.py`
- Phase 3 owns `code/tests/integration/test_timeout_resources.py`
- No phase in Wave 1 touches `code/pyproject.toml` (Phase 5 owns it).

---

### Phase 1: Builder performance file — dispositions, cap-burn, unmark [COMPLETED]

**Goal**: Apply every disposition to
`code/src/model_checker/builder/tests/integration/test_performance.py`, including the two
arithmetically-unreachable assertions that fail 5/5, and remove the file's module-level
`pytestmark`.

**Per-test dispositions** (measured columns are 5-sample min–max from report §6.3):

| Test | Measured | Action |
|---|---|---|
| `test_small_model_generation_completes_quickly` | 1.199–1.253 vs <0.5 (**5/5 fail**) | Delete the `assertLess(elapsed_time, 0.5, ...)` and the `start_time`/`elapsed_time` timing scaffolding. Keep as an end-to-end integration test: assert `build_module.runner.run_examples()` completes without raising and that `build_module` was constructed. Rename to `test_small_model_runs_end_to_end` and rewrite the docstring — the current name and docstring both assert a 500 ms claim that has a measured floor of 1.20 s. |
| `test_medium_model_generation_completes_within_timeout` | 1.18–1.24 vs <2.0 | Delete the timing clause and scaffolding; keep as an end-to-end integration test as above. Rename to drop the "within timeout" claim. |
| `test_large_model_generation_completes_within_timeout` | 1.19–1.25 vs <5.0 | **Delete the whole test.** It is a copy-paste duplicate of the "medium" test — both use `N: 5` with the same premises/conclusions; only the example key and budget differ. Saves ~1.2 s and one misleading name. |
| `test_multiple_examples_process_efficiently` | 5.98–6.23 vs avg<0.5 / total<2.0 (**5/5 fail**) | Delete **both** timing assertions and the `avg_time` computation. Keep as a multi-example integration test: assert all five examples were processed without raising. |
| `test_comparison_mode_performance` | 0.12–0.14 vs <2.0 | Delete the timing clause. Keep as a comparison-mode smoke test asserting `run_comparison()` completes. **Rewrite the docstring**: `get_theory(['extensional'])` and `get_theory(['counterfactual'])` return the identical object (verified: `is` comparison True, same 17 operators), so this compares bimodal against itself. Say so in a comment; do not attempt to fix `get_theory` here. |
| `test_module_loading_performance` | <0.005 vs <0.1 | **Retain as-is.** Z3-free, 20x headroom. Add a one-line comment stating the assertion is a hang guard, not a performance budget. |
| `test_serialization_performance` | <0.005 | **Retain exactly as-is.** Pure Python, no Z3, averaged over 100 iterations — the one well-built timing assertion in the whole set. Do not touch. |
| `test_constraint_generation_scales_linearly` | 4.01–4.26 | **Delete the whole test.** All four cases hit the 1 s cap so `time_ratio ≈ 1.0` is compared against 4, 9 and 16 — stable precisely because it measures nothing, and it could not detect a genuine quadratic blowup because the cap truncates the signal before the assertion sees it. Re-scoping it to count constraints instead of seconds is a different test and out of scope. Saves ~4.2 s. |
| `TestMemoryUsage::test_memory_usage_stays_within_bounds` | <0.005 | **Delete.** Body is `self.assertTrue(True, "placeholder")`. |
| `TestMemoryUsage::test_no_memory_leaks_in_iteration` | <0.005 | **Delete.** Same placeholder. Delete the now-empty `TestMemoryUsage` class with them. |

**Tasks**:
- [ ] Apply the ten dispositions above.
- [ ] Delete the module-level `pytestmark = pytest.mark.slow` at line 31 and the four-line comment
      above it (lines 26-30), which explains a quarantine that will no longer exist.
- [ ] Remove the now-unused `import pytest` only if nothing else in the file uses it; keep it if
      any `pytest.mark` or fixture reference remains.
- [ ] Remove `import time` if no timing code remains outside `test_serialization_performance`
      (it does use `time`, so the import stays).
- [ ] Run the file 3 times: `cd code && PYTHONPATH=src python -m pytest -p no:cacheprovider -m "" src/model_checker/builder/tests/integration/test_performance.py -q`
      and confirm an identical green result set each time.

**Timing**: 1 hour

**Depends on**: none

**Files to modify**:
- `code/src/model_checker/builder/tests/integration/test_performance.py` — dispositions, delete
  module-level mark and its comment.

**Verification**:
- Three consecutive runs of the file alone produce identical, all-green results.
- `pytest --collect-only -m slow` no longer collects anything from this file.
- No test in the file asserts a wall-clock budget except `test_serialization_performance`
  (Z3-free, averaged) and `test_module_loading_performance` (Z3-free hang guard).

---

### Phase 2: Integration performance file — dispositions, cap-burn, unmark [COMPLETED]

**Goal**: Apply every disposition to `code/tests/integration/test_performance.py` and remove all
five per-class `slow` marks. `TestConcurrentPerformance` is not touched.

**Per-test dispositions** (report §6.1):

| Test | Measured | Action |
|---|---|---|
| `test_simple_model_performance` | 0.85–1.01 vs <1.0 (**2/5 fail**, and 1 of the 3 unfiltered-run failures) | Budget equals the `max_time` cap. Delete the timing clause. The test currently asserts **nothing** about the model — replace with a behavioural assertion: the model was constructed and is well-formed (`model is not None` plus one structural property available from `create_model`). Keep `@pytest.mark.timeout(5)`. |
| `test_medium_model_performance` | 1.09–1.10 vs <5.0 | Vacuous (5x above a 1.03 s ceiling). Delete the timing clause; keep as a construction smoke test with an `assert model is not None`. |
| `test_complex_model_performance` | 5.81–6.19 vs <20.0 | The only test whose cost is real (N=16 Python-side constraint generation, not solver-capped), 3.3x headroom. **Retain the 20 s assertion as an explicit hang guard**; add a comment saying so — it means "did not hang", not "was fast". Leave the `except Exception` branch and `@pytest.mark.timeout(30)` in place. |
| `test_scaling_with_n[2-1.0]` | 0.60–1.15 vs <1.0 (**4/5 fail**) | Budget equals the cap. Delete the timing clause from the parametrized body. |
| `test_scaling_with_n[4-2.0]` | 1.07–1.09 vs <2.0 | Vacuous (2x cap). Covered by the same deletion. |
| `test_scaling_with_n[8-10.0]` | 1.08–1.09 vs <10.0 | Vacuous (10x cap). Covered by the same deletion. After deleting the timing clause the `max_time` parameter is unused — **drop the parametrize tuple's second element**, keeping `@pytest.mark.parametrize("n", [2, 4, 8])`, and assert construction succeeds (or raises for `n >= 8`, as the existing `except` branch already allows). |
| `test_memory_usage_simple` | 0.35–1.10 | No wall-clock assertion. Unmark only. |
| `test_memory_usage_complex` | 1.33–1.37 | No wall-clock assertion. Unmark only. |
| `test_memory_cleanup` | 3.16–4.76 | No wall-clock assertion. Unmark, **and add `'max_time': 0.05`** to the 5 `create_test_model({'N': 3})` calls — the test asserts only `gc` object growth and never inspects the solve. Cap-burn reduction per report §7. |
| `test_batch_small_examples` | **<0.005** vs <2.0 | `validate_example` does only structural assertions — no model checking at all, so the budget measures ~20 list constructions. Delete the timing clause and scaffolding; keep the structural validation loop. |
| `test_batch_mixed_complexity` | **<0.005** vs <5.0 | Same. Delete the timing clause and scaffolding. |
| `TestConcurrentPerformance::test_sequential_vs_concurrent` | — | **Leave completely alone.** Already unmarked, already rewritten to assert the single-threaded-construction contract, green in all 6 measured runs. |
| `test_repeated_operations` | <0.005, ratio ≤1.5x | Ratio of two sub-millisecond parse times; passes only because the first is a cold start. Pure noise. Delete the timing clause and convert to a determinism assertion: two `Syntax` parses of the same formula produce equivalent structure. **Fallback**: if `Syntax` exposes no comparable attribute to assert equality on, delete the test outright and say so in the summary. |
| `test_theory_loading_performance` | <0.005, ratio ≤1.1x | Intent is "the theory cache works". Assert that directly: `get_theory('bimodal') is get_theory('bimodal')`. **Run it before committing** — if identity does not hold, the cache does not exist as assumed; fall back to asserting the two results are equal in operator content, and record the finding in the summary. Delete the timing clause either way. |
| `test_maximum_n_performance` | 0.05–0.07 vs <35 | 500x headroom; fails fast at N=64. Vacuous. Delete the timing clauses in both branches; assert the construction attempt terminated (it already does, via the try/except shape). Keep `@pytest.mark.timeout(60)`. |
| `test_many_propositions_performance` | <0.005 vs <2.0 | Wrapped in `except Exception: pass` — cannot fail. Delete the timing clause; assert the parse produced a `Syntax` object on the success path. |

**Tasks**:
- [ ] Apply the sixteen dispositions above.
- [ ] Delete the `@pytest.mark.slow` decorator from all five marked classes:
      `TestExecutionPerformance`, `TestMemoryPerformance`, `TestBatchPerformance`,
      `TestCachingPerformance`, `TestWorstCasePerformance` (verify the exact set against the file
      at edit time).
- [ ] Rewrite the file header comment (lines 15-23), which explains why classes are marked slow.
      Replace with a short note recording *why* the wall-clock assertions were removed: the
      measured quantity was the theory's `max_time` cap, not the code's cost. Do not cite task
      numbers — this file is outside `specs/`.
- [ ] Run the file 3 times: `cd code && PYTHONPATH=src python -m pytest -p no:cacheprovider -m "" tests/integration/test_performance.py -q`
      and confirm an identical green result set each time.

**Timing**: 1.25 hours

**Depends on**: none

**Files to modify**:
- `code/tests/integration/test_performance.py` — dispositions, remove per-class marks, rewrite
  header comment.

**Verification**:
- Three consecutive runs of the file alone produce identical, all-green results.
- `pytest --collect-only -m slow` no longer collects anything from this file.
- `TestConcurrentPerformance` is byte-identical to its pre-change state (`git diff` shows no hunk
  inside it).

---

### Phase 3: Timeout/resources file — dispositions, cap-burn, unmark [COMPLETED]

**Goal**: Apply every disposition to `code/tests/integration/test_timeout_resources.py`, remove
all per-class and per-method `slow` marks, and cut the largest cap-burn in the set.
`test_concurrent_model_building` is not touched.

**Per-test dispositions** (report §6.2):

| Test | Measured | Action |
|---|---|---|
| `test_z3_solver_timeout` | 0.07–0.09 vs <5.0 | 55x headroom; the assertion means "did not hang". **Retain**, unmark, add a comment saying it is a hang guard. |
| `test_cli_command_timeout` | 0.26–0.29 vs <6.0 | Backed by a real `subprocess` `timeout=5`. **Retain**, unmark, add the same hang-guard comment. |
| `test_various_timeout_values[0.001/0.01/0.1]` | 0.07–0.18 | Asserts `settings['max_time'] == timeout_value` — that the dict it just built contains what it put there. Tautological. Rewrite to assert the setting **reaches the model** (assert the constructed model's resolved settings carry the `max_time` value). **Fallback**: if no accessible attribute exposes the resolved setting, delete the test and say so in the summary. |
| `test_large_state_space` | 0.16–0.22 | No timing assertion. Unmark only. |
| `test_many_propositions` | 0.32–1.10 | Has **no assertion at all** — a bare try/except with a comment. Add one: assert the constructed model is not `None` on the success path (the `except MemoryError: pass` branch stays). Unmark. |
| `test_concurrent_model_building` | — | **Leave completely alone.** Already unmarked and green. |
| `test_keyboard_interrupt_cleanup` | <0.005 | **Delete the whole test.** It asserts only that `module_path` is truthy and does not test interrupts at all — a stub whose name claims coverage it does not provide. |
| `test_graceful_shutdown` | 0.94–1.09 | No timing assertion; `@pytest.mark.timeout(10)` is already the right mechanism. Unmark only. |
| `test_performance_with_many_constraints` | 1.14–1.17 vs <1.5 | Margin only 0.33 s over a cap-pinned 1.15 s — has not failed yet but is the same shape as the ones that do. Delete both timing clauses; assert the construction attempt terminated. |
| `test_scaling_behavior[2-0.1]` | 0.26–0.29 vs <0.3 | **Tightest margin in the entire set — as little as 0.01 s. This is the next flake.** Delete the timing clause. |
| `test_scaling_behavior[4-0.5]` | 0.79–1.09 vs <1.5 | Margin 0.41 s over a cap-pinned value. Covered by the same deletion. |
| `test_scaling_behavior[8-2.0]` | 4.08–4.10 vs <6.0 | The 4.1 s is pure cap-burn (`max_time` = 4.0). Delete the timing clause **and** shrink the cap. After deletion `expected_time` is used only to compute `max_time`; keep the parametrize but set `max_time` to a small constant (0.05) since no timing is asserted, or drop the second parametrize element entirely and use a fixed small `max_time`. Prefer the latter — it is simpler and removes a now-meaningless parameter name. |
| `test_memory_released_after_error` | **10.88–11.06** | Most expensive test in the set; 10 s of it is 10 × 1.0 s cap-burn for solves it never inspects — it asserts only `gc` object growth. Unmark **and set `'max_time': 0.05`** in its settings dict. Expected cost after: ~1 s. |
| `test_file_handles_closed` | 3.23–3.68 | No timing assertion. Unmark. Reduce the CLI subprocess iteration count from 5 to 3 (report §7) — the assertion is about handle-leak growth, which 3 iterations exercise as well as 5. |

**Tasks**:
- [ ] Apply the fourteen dispositions above.
- [ ] Delete `@pytest.mark.slow` from all marked classes (`TestTimeoutHandling`,
      `TestInterruptHandling`, `TestPerformanceDegradation`, `TestResourceRecovery`) and from the
      two per-method marks inside `TestResourceLimits` (`test_large_state_space`,
      `test_many_propositions`).
- [ ] Rewrite the file header comment (lines 14-25) and the `TestResourceLimits` docstring's
      explanation of why it carries per-method marks — both describe a mark set that will be gone.
- [ ] Run the file 3 times: `cd code && PYTHONPATH=src python -m pytest -p no:cacheprovider -m "" tests/integration/test_timeout_resources.py -q`
      and confirm an identical green result set each time.

**Timing**: 1.25 hours

**Depends on**: none

**Files to modify**:
- `code/tests/integration/test_timeout_resources.py` — dispositions, remove class and method
  marks, rewrite header comment and `TestResourceLimits` docstring.

**Verification**:
- Three consecutive runs of the file alone produce identical, all-green results.
- `pytest --collect-only -m slow` no longer collects anything from this file.
- `test_concurrent_model_building` is byte-identical to its pre-change state.
- `test_memory_released_after_error` now runs in roughly 1 s, not 11 s (check `--durations=0`).

---

### Phase 4: Marker sweep and filtered-suite verification [COMPLETED]

**Deviation from the task list**: the task text above predicted "5 [deletions] from the builder
file, 1 from the timeout file" (6). The per-phase disposition tables specify **4** builder
deletions and **1** timeout-file deletion (5). The collected count confirms 5 is correct:
2195 baseline - 5 = **2190** collected unfiltered. No fallback deletions were needed in Phases
2 or 3 — every intended behavioural property was verified to hold before the conversion.


**Goal**: Confirm exactly one `slow`-marked test remains repo-wide and that the still-filtered
default suite is green, before the quarantine clause is removed.

**Tasks**:
- [ ] Run `cd code && PYTHONPATH=src python -m pytest -p no:cacheprovider -m slow --collect-only -q`
      and confirm it collects **exactly 1** test:
      `src/model_checker/models/tests/unit/test_semantic.py::TestSemanticDefaultsNBounds::test_max_n_itself_is_constructible`.
      (Baseline at plan time: 41 collected of 2195.)
- [ ] Confirm that test keeps its `@pytest.mark.slow` and its explanatory docstring — it
      legitimately allocates ~3.5 GB over ~10 s to keep `MAX_N` honest. Do **not** unmark it.
- [ ] Run the full default (still-filtered) suite once and record wall time and result set:
      `cd code && PYTHONPATH=src python -m pytest -q -p no:cacheprovider`. It must be green.
      Baseline for comparison: 1 failure / 2136 passed / 43 deselected in 5:37 (from the addopts
      comment block, measured before the concurrency fix landed).
- [ ] Record the total collected count and confirm it accounts for every test deleted in
      Phases 1-3 (expected deletions: 5 from the builder file, 1 from the timeout file, plus any
      fallback deletions taken in Phase 2/3 — enumerate them explicitly).
- [ ] Confirm `pytest-timeout` is active (it is installed in this environment) so the
      `@pytest.mark.timeout(...)` hang guards retained in Phases 2 and 3 are real and not
      silently-ignored unknown marks.

**Timing**: 0.5 hours

**Depends on**: 1, 2, 3

**Files to modify**: none (verification only)

**Verification**:
- `-m slow` collects exactly 1 test.
- Filtered full suite is green.
- Deleted-test accounting reconciles: `2195 - (tests deleted) = ` new collected total.

---

### Phase 5: Delete the quarantine clause from pyproject.toml [COMPLETED]

**Goal**: Remove the `-m "not slow"` filter — not relax it — along with the TEMPORARY comment
block that justified it, and rewrite the `slow` marker description so it describes what the
marker now means.

**Tasks**:
- [ ] Delete the `-m \"not slow\"` clause from `addopts` (line 104). Result:
      `addopts = "--durations=0 -v --import-mode=importlib"`.
- [ ] Delete the entire TEMPORARY comment block at lines 85-103. Both defects it names are now
      resolved: the concurrency segfault by the construction guard, and the ungrounded wall-clock
      budgets by Phases 1-3.
- [ ] Rewrite the `slow` marker description (line 110). It currently reads "Quarantined pending
      fixes (see the addopts note above) -- NOT a permanent opt-out; these tests are expected to
      rejoin the default run", which will be false in both clauses. Replace with a description of
      the marker's actual remaining meaning: genuinely expensive tests that run in the default
      suite and can be deselected explicitly with `-m "not slow"` when a fast local iteration
      loop is wanted. **Keep the marker definition** — it is still used by
      `test_max_n_itself_is_constructible`.
- [ ] **Stated scope addition**: add `pytest-timeout` to `[project.optional-dependencies].dev`
      alongside `pytest-xdist`. Several tests retained in Phases 2 and 3 rely on
      `@pytest.mark.timeout(...)` as their only hang guard. The plugin is installed in this
      environment but undeclared, so those guards would silently become no-op unknown marks in a
      clean `pip install -e ".[dev]"` environment. This is one line in a file this phase already
      owns and is directly entailed by the hang-guard dispositions; it is called out here so it is
      not mistaken for unflagged scope creep.
- [ ] Leave `code/tests/conftest.py`'s duplicate `slow` marker registration (line 262) alone — its
      text, "marks tests as slow (deselect with `-m \"not slow\"`)", remains accurate as usage
      guidance.

**Timing**: 0.5 hours

**Depends on**: 4

**Files to modify**:
- `code/pyproject.toml` — delete addopts clause, delete comment block, rewrite marker
  description, declare `pytest-timeout` in the `dev` extra.

**Verification**:
- `rg -n 'not slow' code/pyproject.toml` returns only the new marker-description usage text, never
  an `addopts` occurrence.
- A bare `cd code && PYTHONPATH=src python -m pytest --collect-only -q` now collects the full
  suite with **0 deselected**.
- Commit this phase on its own so it can be reverted independently (see Phase 6 contingency).

---

### Phase 6: Repeat unfiltered verification — 3 separate invocations [COMPLETED]

**Result**: three separate invocations, all green, identical result set — 2190 collected / 2190
passed / 0 failed / 0 deselected each, in 336.81s, 387.33s and 418.11s. Evidence:
`specs/136_ground_wallclock_performance_budgets/evidence/unfiltered-repeat-results.md`.


**Goal**: Apply task 135's verification bar verbatim: run the unfiltered suite 3 times as
**separate invocations** requiring an **identical green result set**. A single green run is not
evidence — the defect being fixed is result-set *instability*, and comparing failure sets across
runs is what exposed it.

**Tasks**:
- [ ] Ensure no concurrent oracle suite or other heavy job is running on the machine. Prior
      measurements were deliberately taken under load; this verification must not be.
- [ ] Run three **separate** invocations, capturing full output to distinct files under
      `specs/136_ground_wallclock_performance_budgets/evidence/`:
      `cd code && PYTHONPATH=src python -m pytest -q -p no:cacheprovider` (three times; ~6-7 min
      each).
- [ ] Compare the three result sets. The bar is **identical**, not merely "all green three
      times": same collected count, same passed count, same (empty) failure set.
- [ ] Explicitly account for the 3 failures the research measured in its unfiltered run. All three
      are in scope and are eliminated by Phases 1-3:
      - `tests/integration/test_performance.py::TestExecutionPerformance::test_simple_model_performance`
        — timing clause deleted, converted to a behavioural assertion (Phase 2).
      - `builder/.../test_multiple_examples_process_efficiently` — both timing assertions deleted
        as arithmetically unreachable (Phase 1).
      - `builder/.../test_small_model_generation_completes_quickly` — timing assertion deleted as
        arithmetically unreachable (Phase 1).
      If any of the three still fails, the corresponding disposition was not applied correctly —
      fix it, do not justify it.
- [ ] Record the unfiltered wall time and compare against the ~6:13 research measurement and the
      ~5:37 filtered baseline. Report the delta. Expected: roughly +10% over the filtered baseline
      after cap-burn reduction.
- [ ] Write the three result sets and the comparison to
      `specs/136_ground_wallclock_performance_budgets/evidence/unfiltered-repeat-results.md`.

**Contingency (must be followed, not improvised)**: if any invocation is red:
- **Failure inside the three named files** — the disposition was applied incorrectly. Fix it and
  restart the three-run sequence from scratch. Partial credit for earlier green runs is not
  allowed; the bar is three consecutive identical green invocations.
- **Failure outside the three named files** — do **not** declare green and do **not** delete the
  test. Reproduce it in isolation to determine whether it is a genuine regression or a
  pre-existing load-sensitive flake (the bimodal `BM_CM_4` example is the known candidate: it has
  passed in isolation at 21.39 s against a 30 s budget while failing under full-suite load). Then:
  revert the Phase 5 commit so the default run is not left red, record the failure as a blocker in
  the handoff with the isolation evidence, and mark the task `[PARTIAL]`. Do not ship a red
  default suite in order to close the task.

**Timing**: 1 hour (≈20 min of it is unattended run time)

**Depends on**: 5

**Files to modify**:
- `specs/136_ground_wallclock_performance_budgets/evidence/unfiltered-repeat-results.md` (new)

**Verification**:
- Three separate invocations, identical result sets, all green, 0 deselected.
- Evidence file records all three raw summaries plus the comparison and wall-time delta.

---

### Phase 7: Close out task 135's Phase 7 by reference [COMPLETED]

**Goal**: Record that task 135's only remaining work was performed here, so it is not performed a
second time.

**Tasks**:
- [ ] Mark Phase 7 of
      `specs/135_fix_concurrent_model_building_segfault/plans/01_single-threaded-construction-guard.md`
      as `[COMPLETED]`, with a one-line note under the phase stating it was satisfied by this
      task's Phase 5 (the `-m "not slow"` deletion) and Phase 6 (the 3-invocation verification
      bar, applied verbatim from that task's own handoff), and citing the evidence file path.
- [ ] Do **not** re-run the deletion or the verification. Do not edit `code/pyproject.toml` again.
- [ ] Note in this task's summary and in `.orchestrator-handoff.json` that task 135 now has no
      remaining implementation work, so its status can be closed by the orchestrator or `/todo`.
      Do not transition task 135's `state.json` status from inside this task.

**Timing**: 0.25 hours

**Depends on**: 6

**Files to modify**:
- `specs/135_fix_concurrent_model_building_segfault/plans/01_single-threaded-construction-guard.md`
  — Phase 7 marker and by-reference note.

**Verification**:
- Task 135's plan has no `[NOT STARTED]` or `[PARTIAL]` phase remaining.
- The by-reference note names this task's evidence file path.

---

## Testing & Validation

- [ ] Each of Phases 1-3: the owned file passes 3 consecutive identical green runs in isolation.
- [ ] Phase 4: `-m slow` collects exactly 1 test repo-wide
      (`test_max_n_itself_is_constructible`); filtered full suite green.
- [ ] Phase 4: deleted-test accounting reconciles against the 2195 baseline.
- [ ] Phase 5: `--collect-only` reports **0 deselected**; no `-m "not slow"` remains in `addopts`.
- [ ] Phase 6: three separate unfiltered invocations produce an identical, all-green result set.
- [ ] Phase 6: all three previously-failing tests are accounted for — each either passes or was
      deleted with a recorded reason.
- [ ] No test outside the three named files was modified.
- [ ] Nothing under `oracle/` was modified (`git diff --stat -- oracle/` is empty).
- [ ] Both concurrency tests are byte-identical to their pre-change state.

## Artifacts & Outputs

- `specs/136_ground_wallclock_performance_budgets/plans/01_wallclock-budget-grounding.md`
  (this file)
- `specs/136_ground_wallclock_performance_budgets/evidence/unfiltered-repeat-results.md`
  (Phase 6 — three raw run summaries plus comparison)
- `specs/136_ground_wallclock_performance_budgets/summaries/01_wallclock-budget-grounding-summary.md`
  — must enumerate every deleted test with its measured justification, every timing clause
  converted to a behavioural assertion, every fallback taken (Phase 2's `Syntax`/`get_theory`
  fallbacks, Phase 3's `max_time`-reaches-solver fallback), and the before/after suite wall times.
- Modified: `code/src/model_checker/builder/tests/integration/test_performance.py`,
  `code/tests/integration/test_performance.py`,
  `code/tests/integration/test_timeout_resources.py`, `code/pyproject.toml`,
  `specs/135_fix_concurrent_model_building_segfault/plans/01_single-threaded-construction-guard.md`

## Rollback/Contingency

- **Per-phase commits**: each of Phases 1, 2, 3 and 5 is committed separately so any one can be
  reverted without disturbing the others. Phase 5 in particular must be a standalone commit — the
  Phase 6 contingency depends on being able to revert the quarantine deletion alone while keeping
  the test-file improvements.
- **If the unfiltered suite cannot be made green** for reasons outside the three named files:
  revert the Phase 5 commit (restoring the quarantine), keep Phases 1-3 (they are improvements
  regardless), mark the task `[PARTIAL]`, and record the out-of-scope failure as a hard blocker
  with isolation evidence. Task 135's Phase 7 then remains open and Phase 7 of this plan is not
  performed.
- **If a behavioural conversion cannot assert a true property** (the `get_theory` identity or
  `Syntax` comparability fallbacks): delete the test rather than assert something unverified, and
  record the finding. An assertion that was never observed to hold is worse than no test.
- **Full revert**: `git revert` the phase commits in reverse order. No migrations, no generated
  artifacts, no state outside the repo is involved.
