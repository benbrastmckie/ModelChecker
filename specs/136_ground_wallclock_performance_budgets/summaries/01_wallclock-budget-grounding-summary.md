# Implementation Summary: Ground the Wall-Clock Performance Budgets

- **Task**: 136 - ground_wallclock_performance_budgets
- **Session**: sess_1786211832_501137_136
- **Plan**: `specs/136_ground_wallclock_performance_budgets/plans/01_wallclock-budget-grounding.md`
- **Report**: `specs/136_ground_wallclock_performance_budgets/reports/01_wallclock-budget-grounding.md`
- **Status**: all 7 phases COMPLETED
- **Date**: 2026-08-08

## Outcome

The `-m "not slow"` quarantine is **deleted** from `code/pyproject.toml`. The default test run is
now unfiltered — 2190 tests, 0 deselected — and was verified green across three separate
invocations with an identical result set. Exactly one `slow`-marked test remains repo-wide, and
it keeps its mark deliberately.

The central finding of the research held up under implementation: **no budget needed
re-grounding, because none of them was measuring the code.** The bimodal theory's default
`max_time` is 1 second, so every model construction in these files measured
`min(real_solve_time, max_time) + overhead` and pinned near that cap regardless of N. Budgets at
0.5s were arithmetically unreachable; budgets at 1.0s sat inside the measured distribution and
flipped run to run; budgets at 2s and above sat over a ceiling the quantity could not physically
reach and could never fail. A p95 of that distribution would describe the cap, not the code. The
task description anticipated deriving p95/p99 budgets; the measurement does not support that
framing, and the plan superseded it explicitly rather than silently.

## Verification

**Three separate unfiltered invocations, identical green result set** (the non-negotiable bar,
carried verbatim from the concurrent-construction task):

| Run | Collected | Passed | Failed | Deselected | Wall time |
|---|---|---|---|---|---|
| 1 | 2190 | 2190 | 0 | 0 | 336.81s (5:36) |
| 2 | 2190 | 2190 | 0 | 0 | 387.33s (6:27) |
| 3 | 2190 | 2190 | 0 | 0 | 418.11s (6:58) |

Identity is structural, not merely count-equality: collection is a deterministic 2190 with 0
deselected, and every run reported 2190 passed with zero FAILED/ERROR/skipped/xfail lines, so the
passed set equals the full collected set in all three. Full detail, including the discarded
truncated fourth measurement, in
`specs/136_ground_wallclock_performance_budgets/evidence/unfiltered-repeat-results.md`.

**The 3 known failures are accounted for, not justified.** The research's unfiltered baseline was
3 failed / 2192 passed. All three were in scope and all three now pass 3/3:

| Previously failing | Why it failed | Now |
|---|---|---|
| `test_simple_model_performance` | Budget (1.0s) numerically equal to the `max_time` cap; 2/5 observed failure rate | Timing clause deleted; asserts the model was constructed and is well-formed (it previously asserted nothing at all about the model) |
| `test_multiple_examples_process_efficiently` | 5 x ~1.24s against a 2.0s total budget — unreachable, 5/5 failures | Both timing assertions deleted; renamed `test_multiple_examples_run_end_to_end`; asserts all five examples loaded and processed |
| `test_small_model_generation_completes_quickly` | Measured floor 1.20s against a 0.5s budget — unreachable, 5/5 failures | Timing assertion deleted; renamed `test_small_model_runs_end_to_end`; asserts the load-and-run path completes |

Per-phase isolated verification (3 consecutive identical runs each): builder file 6 passed
(8.13/8.09/8.10s); integration performance file 16 passed (16.22/15.73/14.49s); timeout/resources
file 15 passed (8.89/8.49/9.07s).

## Deleted tests, with justification

Five tests were deleted. A vacuous assertion is not coverage; each deletion is measured, not
stylistic.

| Test | File | Measured justification |
|---|---|---|
| `test_large_model_generation_completes_within_timeout` | builder `test_performance.py` | Copy-paste duplicate of the "medium" test — identical premises, conclusions and `N: 5`; only the example key and the budget differed. Saves ~1.2s |
| `test_constraint_generation_scales_linearly` | builder `test_performance.py` | All four cases hit the 1s cap, so `time_ratio ~ 1.0` was compared against 4, 9 and 16 — stable precisely because it measured nothing, and unable to detect a genuine blowup because the cap truncates the signal before the assertion sees it. Saves ~4.2s |
| `TestMemoryUsage::test_memory_usage_stays_within_bounds` | builder `test_performance.py` | Entire body was `self.assertTrue(True, "placeholder")` |
| `TestMemoryUsage::test_no_memory_leaks_in_iteration` | builder `test_performance.py` | Same placeholder. The now-empty class was deleted with them |
| `test_keyboard_interrupt_cleanup` | `test_timeout_resources.py` | Created a module containing `time.sleep(10)`, then asserted only that the returned path was truthy. It never sent an interrupt and tested nothing about cleanup |

**Accounting reconciles**: 2195 baseline - 5 deletions = **2190** collected, confirmed by
`--collect-only`. Each deletion site carries a comment explaining what used to be there and why
it went, so the removal is not silent to a future reader.

## Timing clauses converted to behavioural assertions

| Test | Timing clause removed | Assertion gained |
|---|---|---|
| `test_simple_model_performance` | `elapsed < 1.0` | `model is not None`, `model.N == 3`, `model.semantics is not None` |
| `test_medium_model_performance` | `elapsed < 5.0` | `model is not None`, `model.N == 8` |
| `test_scaling_with_n` | per-N budget | construction succeeds with the requested N (or raises for `n >= 8`) |
| `test_batch_small_examples` / `test_batch_mixed_complexity` | `elapsed < 2.0` / `< 5.0` | the batch was fully built and structurally validated |
| `test_repeated_operations` | parse-time ratio `<= 1.5x` | two `Syntax` parses of the same formula yield the same structure |
| `test_theory_loading_performance` | load-time ratio `<= 1.1x` | `get_theory('bimodal') is get_theory('bimodal')` |
| `test_maximum_n_performance` | `elapsed < 35` | the attempt terminated (the `@pytest.mark.timeout(60)` is the real hang guard) |
| `test_many_propositions_performance` | `elapsed < 2.0` | the parse produced the expected `Syntax` on the success path |
| `test_various_timeout_values` | (tautology, not timing) `settings['max_time'] == timeout_value` | `model.max_time == timeout_value` — the setting actually reaches the model |
| `test_many_propositions` | (had no assertion at all) | `model is not None` on the success path |
| `test_performance_with_many_constraints` | `elapsed < max_time + 0.5` | the attempt terminated |
| `test_scaling_behavior` | `elapsed < expected_time * 3` | construction terminates at each N |
| builder: 4 end-to-end tests | four budgets | the loaded `example_range` / `semantic_theories` content is what the module declared |

**No fallback was taken.** The plan carried three "if the property does not hold, delete the test
and record it" fallbacks. Each intended property was probed and verified to hold *before* the
conversion was written, so none was needed:

- `get_theory('bimodal') is get_theory('bimodal')` — verified `True`.
- `Syntax` structural comparability — `all_sentences` is a dict with stable string keys and
  `infix_conclusions` is a list; both compare cleanly across two parses.
- The resolved `max_time` reaching the model — `ModelDefaults.max_time` exposes it directly.

Two `try/except` blocks were restructured while converting them (`test_various_timeout_values`,
`test_many_propositions`) so the new assertions sit outside the `try`. Left inside, an assertion
failure would have been caught by the test's own `except Exception` and silently converted into
the fallback branch — the converted test would have been unable to fail for the reason it exists.

## Retained timing assertions

Five survive, each documented in place as what it actually is:

- `test_serialization_performance` (builder) — **untouched**. Pure Python, no Z3, averaged over
  100 iterations. The one well-built timing assertion in the set.
- `test_module_loading_performance` (builder) — hang guard, Z3-free, 20x headroom.
- `test_complex_model_performance` — hang guard. The one construction whose cost is real rather
  than solver-capped (N=16 Python-side constraint generation, ~6s against 20s).
- `test_z3_solver_timeout` — hang guard, 55x headroom.
- `test_cli_command_timeout` — hang guard, backed by the subprocess's own `timeout=5`.

Each now carries a comment saying the budget means "did not hang", not "was fast", so a future
reader does not mistake it for a performance guard and tighten it.

## Cap-burn reduction

Tests that never inspect the solve result no longer wait out the full `max_time` for a solve they
discard:

| Test | Before | After | Change |
|---|---|---|---|
| `test_memory_released_after_error` | 10.88-11.06s | 0.96s | `max_time: 0.05` (asserts only `gc` object growth) |
| `test_file_handles_closed` | 3.23-3.68s | 2.34s | CLI iterations 5 -> 3 |
| `test_memory_cleanup` | 3.16-4.76s | — | `max_time: 0.05` on its 5 constructions |
| `test_scaling_behavior[8]` | 4.08-4.10s | — | fixed small `max_time` replaces the derived 4.0s cap |

The `test_timeout_resources.py` file as a whole went from ~25s+ to ~8.9s.

## Markers

- All `slow` marks removed from the three files: 1 module-level `pytestmark` (builder), 9 class
  decorators, and 2 per-method marks.
- `-m slow` now collects **exactly 1** test repo-wide:
  `models/tests/unit/test_semantic.py::TestSemanticDefaultsNBounds::test_max_n_itself_is_constructible`.
  It keeps its mark and explanatory docstring — it legitimately allocates ~3.5GB over ~10s to keep
  `MAX_N` honest.
- The `slow` marker *definition* is kept (that one test still uses it) but its description was
  rewritten: it no longer claims a quarantine, and now describes the marker's real remaining
  meaning — genuinely expensive tests that run in the default suite and can be deselected
  explicitly for a fast local loop.
- Neither concurrency test was re-marked. Both are byte-identical to their pre-task state
  (verified programmatically): `TestConcurrentPerformance::test_sequential_vs_concurrent` (1793
  bytes) and `TestResourceLimits::test_concurrent_model_building` (2806 bytes).

## Wall-time impact

| Measurement | Result | Wall time |
|---|---|---|
| Filtered baseline in the old `addopts` comment (pre-dates the concurrency fix) | 1 failed / 2136 passed / 43 deselected | 5:37 |
| Research unfiltered run, before this task | 3 failed / 2192 passed | 6:13 |
| Filtered, after Phases 1-3, quarantine still in place | 2189 passed / 1 deselected | 6:14 |
| Unfiltered, quarantine deleted (mean of 3 runs) | 2190 passed | **6:21** |

+13% over the filtered baseline while running 54 more tests and finishing green. The predicted
~+10% held.

## Plan Deviations

1. **Deleted-test count in the Phase 4 task list was wrong (plan-internal inconsistency).** The
   Phase 4 text predicted "5 deletions from the builder file, 1 from the timeout file" (6); the
   per-phase disposition tables specify 4 and 1 (5). The disposition tables are correct, and the
   collected count confirms it: 2195 - 5 = 2190. Annotated in the plan under Phase 4.
2. **Phase 2 test renames not performed.** Phase 1 explicitly instructed renames (its names
   carried numeric claims — "completes_quickly", "within_timeout"); Phases 2 and 3 did not, and
   their names are generic ("performance"). Names were left as-is per the plan and the docstrings
   updated instead. Flagging it because `test_simple_model_performance` no longer asserts anything
   about performance; a future rename would be reasonable but was out of this plan's scope.
3. **Two `try/except` blocks restructured beyond the literal disposition** (see above). Necessary
   for the converted assertions to be able to fail at all; a strictly literal edit would have
   produced a test that swallowed its own new assertion.
4. **Phase 6 required a fourth suite invocation.** The first attempt at run 3 was killed at 580s
   by the harness's own command timeout at 55% progress (zero failures recorded). That truncated
   measurement was discarded, not counted, and the run was re-executed detached. Recorded in the
   evidence file rather than quietly dropped.
5. **`pytest-timeout` added to the `dev` extra** — a stated scope addition already called out in
   the plan's Phase 5, not new drift. Several retained hang guards depend on
   `@pytest.mark.timeout(...)`; the plugin was installed here but undeclared, so those guards
   would have become silently-ignored unknown marks in a clean `pip install -e ".[dev]"`.

## Cross-task closure

The concurrent-construction task's Phase 7 was the same `pyproject.toml` deletion performed here
in Phase 5, gated on this task. It is now marked `[COMPLETED]` in
`specs/135_fix_concurrent_model_building_segfault/plans/01_single-threaded-construction-guard.md`
with a by-reference note pointing at this task's Phases 5-6 and the evidence file, and its gated
Testing & Validation checkbox is ticked with the same reference. That plan now has **no**
unfinished phase. The deletion and the verification were **not** performed a second time.

That task therefore has no remaining implementation work and can be closed by the orchestrator or
`/todo`. Its `state.json` status was deliberately **not** transitioned from inside this task.

## Findings Reported, Not Fixed (out of scope)

Carried forward from the research; each is real and each has semantic consequences beyond this
task's file scope:

1. **Bimodal's default `max_time: 1` is below the real solve time for its own simple examples.**
   The builder's N=2 example reports *"there is no countermodel"* at `max_time=1` and *"there is a
   countermodel"* at `max_time=5` — a silent semantic inversion of exactly the kind
   `TESTING_GUIDE.md` 8.6 warns about. Any bimodal example near the 1s boundary is at risk. Worth
   a dedicated audit.
2. **`bimodal.get_theory(subtheories)` ignores its argument.** `get_theory(['extensional'])` and
   `get_theory(['counterfactual'])` return the identical object. The builder's comparison test
   therefore compares bimodal against itself; this is now stated in that test's docstring rather
   than left implied.
3. **`BaseExampleTest.validate_example` does no model checking** — it is a pure type/shape check.
   Tests named "batch performance" built on it were measuring list construction. Now stated in the
   class docstring.

## Files Modified

- `code/src/model_checker/builder/tests/integration/test_performance.py`
- `code/tests/integration/test_performance.py`
- `code/tests/integration/test_timeout_resources.py`
- `code/pyproject.toml`
- `specs/135_fix_concurrent_model_building_segfault/plans/01_single-threaded-construction-guard.md`
  (authorized cross-task marker edit only)

Nothing under `oracle/` was modified (`git diff --stat -- oracle/` is empty across the task's
commits).

## Commits

| Commit | Phase |
|---|---|
| `538f6ece` | phase 1: ground builder performance assertions |
| `5e502baa` | phase 2: ground integration performance assertions |
| `ae6d051e` | phase 3: ground timeout/resource assertions and cut cap-burn |
| `87f6fedb` | phase 4: marker sweep, filtered suite green |
| `a116617f` | phase 5: delete the `-m "not slow"` quarantine from addopts (standalone, independently revertible) |
| `31052be4` | phase 6: 3 unfiltered invocations green with identical result set |
