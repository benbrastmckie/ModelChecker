# Known Test Failure Baseline

## Summary

A fresh full sweep at HEAD (`PYTHONPATH=code/src pytest code/src/model_checker/ code/tests/ -v`,
background PID, ~5 minutes) found **27 failed, 2148 passed, 75 subtests passed**. This confirms
the task description's raw count but the *composition* is materially different from what the
task description assumed: most of the "timing/resource-sensitive" bucket is not timing-sensitive
at all. It is a single shared test helper bug (`create_test_model`) and a repeated stale-syntax
literal (`'A[]'`-style bracket-suffixed sentence letters) cascading through unrelated files. Two
of the three specific defects named in the task description (the `assert_and_track` mock-spec
failure, and the two ValueError message-drift tests) do not reproduce as described; investigating
why turned up the real underlying bugs at different locations (see "Stale claims" below).

**Verification note**: 22 of the 27 failures were root-caused and fixed by 10 file edits plus one
new fixture module (see "Fixes applied"). A background re-run of the touched files to confirm the
fixes was still finishing at report-writing time; see `run/per-file-verify.txt` in this task
directory for whatever that run captured, and the handoff JSON `blockers` for what remains
unconfirmed.

## Stale claims from the task description (verified wrong, don't carry forward)

Per the standing instruction to verify rather than assume inherited claims:

- **`assert_and_track` AttributeError**: task description located this in
  `iterate/tests/integration/test_generator_interface.py`. That file's `Mock(spec=[...,
  'assert_and_track'])` pattern is correct and all 6 tests in it pass (verified 3x). The *real*
  occurrence is `code/src/model_checker/models/tests/unit/test_structure.py::TestModelDefaultsStructure::test_attribute_initialization_order`,
  which does `with patch('z3.Solver'):` with **no spec at all** -- an unspecced `Mock`/`MagicMock`
  raises `AttributeError` for *any* attribute name starting with `assert` (a typo-guard built into
  `unittest.mock`, confirmed against a bare Python repro), regardless of whether the real object
  has that method. Fix: `patch('z3.Solver', spec=Solver)`.
- **Two ValueError message-drift tests ("Empty token list" / "The expression [] is incomplete")**:
  `code/src/model_checker/utils/tests/unit/test_parsing.py` (19 tests) passes in full; the
  messages the task description worried about are already exactly what `parsing.py` raises. The
  *real* failures with these exact messages are elsewhere entirely (see Group A below) --
  triggered by invalid input formulas, not by a message-text mismatch.
- The task description's `27/2148` figure is otherwise accurate as a raw count at HEAD (the
  session's earlier witness-error and `test_build_example_bimodal_theory_countermodel` fixes are
  both confirmed still in effect and did not regress).

## Root cause A: `create_test_model` test helper was completely broken (14 failures)

`code/tests/utils/helpers.py::create_test_model` had two independent, stacked bugs:

1. Default `conclusions = ['A[]']` -- `'A[]'` is not a valid formula. The tokenizer only splits on
   `(`/`)`, so `'A[]'` survives as one token; it fails `.isalnum()` and doesn't start with `\\`, so
   `parse_expression` falls through to a branch that recurses on the (now-empty) remaining tokens,
   raising `ValueError: Empty token list`. Sentence letters in this grammar are plain alnum tokens
   (`'A'`, `'p0'`, ...) -- confirmed against `bimodal/examples.py`, which never uses bracket
   suffixes anywhere.
2. `semantics = semantics_class(full_settings, syntax)` -- passes two positional args, but
   `BimodalSemantics.__init__(self, settings)` (and the production call site,
   `builder/example.py:176`, `self.semantics(self.settings)`) both take exactly one. This bug was
   invisible because bug (1) always raised first, before this line ever ran.

Both bugs had to be fixed together (`code/tests/utils/helpers.py`) -- fixing only the default
formula would have surfaced the `TypeError` from bug (2) as a new failure. Verified by hand: with
both fixes, `create_test_model` successfully builds a `ModelDefaults` and, when given very short
`max_time` values, returns normally with `model_found`/`satisfiable` reflecting a timeout rather
than raising (matches the documented [8.6] behavior: timeouts never raise).

Because `BaseModelTest.create_model` (in `code/tests/utils/base.py`) and `test_timeout_resources.py`
call `create_test_model` heavily inside broad `try/except Exception` blocks, this single upstream
bug masqueraded as 14 separate, unrelated-looking failures across 3 files:

| Node id | Symptom before fix |
|---|---|
| `tests/integration/test_error_handling.py::TestFrameworkErrorHandling::test_z3_timeout_handling` | `ValueError: Empty token list` |
| `tests/integration/test_error_handling.py::TestFrameworkErrorHandling::test_memory_limit_handling` | `ValueError: Empty token list` |
| `tests/integration/test_performance.py::TestExecutionPerformance::test_simple_model_performance` | `ValueError: Empty token list` |
| `tests/integration/test_performance.py::TestExecutionPerformance::test_medium_model_performance` | `ValueError: Empty token list` |
| `tests/integration/test_performance.py::TestExecutionPerformance::test_scaling_with_n[2-1.0]` | `assert 2 >= 8` (except-branch fallback assertion, not a real scaling failure) |
| `tests/integration/test_performance.py::TestExecutionPerformance::test_scaling_with_n[4-2.0]` | `assert 4 >= 8` (same) |
| `tests/integration/test_performance.py::TestMemoryPerformance::test_memory_usage_simple` | `ValueError: Empty token list` |
| `tests/integration/test_performance.py::TestMemoryPerformance::test_memory_usage_complex` | `ValueError: Empty token list` |
| `tests/integration/test_performance.py::TestMemoryPerformance::test_memory_cleanup` | `ValueError: Empty token list` |
| `tests/integration/test_performance.py::TestConcurrentPerformance::test_sequential_vs_concurrent` | `Concurrent (0.00s) much slower than sequential (0.00s)` -- both timings are ~0 because every call raised instantly |
| `tests/integration/test_timeout_resources.py::TestTimeoutHandling::test_various_timeout_values[0.01]` | `assert 0.01 < 0.01` (except-branch fallback, not a real timeout-value bug) |
| `tests/integration/test_timeout_resources.py::TestTimeoutHandling::test_various_timeout_values[0.1]` | `assert 0.1 < 0.01` (same) |
| `tests/integration/test_timeout_resources.py::TestResourceLimits::test_large_state_space` | `assert ('memory' in 'empty token list' or 'resource' in 'empty token list')` |
| `tests/integration/test_timeout_resources.py::TestResourceLimits::test_many_propositions` | `ValueError: Empty token list` |

None of these are genuinely about performance, memory, or timeout-value handling -- the assertions
that *look* like they're testing those things are all in `except Exception:` fallback branches
that only ever ran because the helper always raised. This is worth flagging on its own: several of
these tests were "passing" a different way before -- by accepting almost any exception as the
"acceptable degradation" case -- and would not actually have caught a real regression in scaling,
memory, or timeout behavior. Fixing the helper restores their ability to test what they claim to.

## Root cause B: stale bracket-suffix sentence-letter syntax (5 more sites, some already counted above)

The same `X[]`-suffix pattern recurs, independent of `create_test_model`, in test-authored formula
literals:

- `code/tests/integration/test_performance.py::TestCachingPerformance::test_repeated_operations` --
  `formula = "(A[] \\wedge B[]) \\vee (C[] \\wedge D[])"` -> fixed to
  `"((A \\wedge B) \\vee (C \\wedge D))"`. Note this needed an *additional* outer paren pair
  beyond just dropping the bracket suffixes: this grammar requires the whole top-level binary
  expression wrapped in one enclosing `(...)` pair (confirmed by direct construction -- dropping
  only the suffixes and keeping `"(A \\wedge B) \\vee (C \\wedge D)"`, two parenthesized
  sub-expressions joined by a bare `\vee` with no enclosing parens, raises `ValueError: Unbalanced
  parentheses`).
- `code/tests/e2e/test_batch_output_real.py` -- embedded example module used `["A[]"]` as its
  conclusion -> fixed to `["A"]`. (This is the `test_bimodal_batch_output` CLI failure.)
- `code/tests/integration/test_error_handling.py::TestEdgeCases::test_very_long_formulas` -- used
  `"P[]"` as its base sentence letter, **and** additionally wrapped the unary `\neg` operator in
  parentheses each iteration (`f"(\\neg {formula})"`). This grammar's parentheses denote binary
  infix grouping only (confirmed: `\neg A` parses, `(\neg A)` raises `ValueError: Operator missing
  after operand`) -- unary operators are never parenthesized. Both are fixed.
- `code/tests/integration/test_timeout_resources.py::TestResourceLimits::test_many_propositions` --
  `assumptions = [f"p{i}[]" for i in range(num_props)]` -> fixed to `f"p{i}"`. (Already counted in
  Root Cause A's table since it also depends on the helper, but this formula bug is independent
  and would have persisted even after the helper fix.)
- `code/tests/integration/test_performance.py::TestExecutionPerformance::test_many_propositions_performance` --
  same `f"p{i}[]"` pattern, silently swallowed by a bare `except Exception: pass` so it never
  actually exercised its own timing assertion (not in the 27-failure list, but a silently-defanged
  test worth fixing alongside the rest). Fixed.

## Category (b): genuine defects (unrelated to the above two root causes)

| Node id | Root cause | Status |
|---|---|---|
| `models/tests/unit/test_structure.py::TestModelDefaultsStructure::test_attribute_initialization_order` | Unspecced `patch('z3.Solver')` trips the mock assert-prefix typo guard on the real `assert_and_track` call inside `ModelDefaults` construction. | **Fixed**: `patch('z3.Solver', spec=Solver)`. |
| `builder/tests/unit/test_project.py::TestBuildProjectCore::test_project_initialization_default` | `BuildProject()`'s default theory is now deliberately `registry.get_registered()[0]` (see `project.py`'s docstring and `docs/THEORY_ARCHITECTURE.md`'s Layering section), not a hardcoded `'logos'`. The test asserted the old hardcoded value. | **Fixed**: assert against `registry.get_registered()[0]` dynamically. |
| `builder/tests/e2e/test_full_pipeline.py::TestFullPipeline::test_theory_library_execution` | Bimodal's model output renders a `"World Histories"` table, not the generic `"State Space"` header the test checked for. | **Fixed**: assertion updated to `"World Histories"`. |
| `builder/tests/unit/test_example.py::TestBuildExampleIntegration::test_find_next_model_basic` | `BuildExample` has no `find_next_model` method anywhere in `builder/` -- genuine API drift; no equivalent method exists on the class (iteration lives in `model_checker.iterate`, not as a `BuildExample` method). | **Not fixed** -- needs a design decision (restore the method vs. rewrite the test against the current iterate API), out of scope for a safe mechanical fix. |

## Category (a): timing/resource-sensitive (environment-dependent, not code bugs)

Split per the requested wall-clock-assertion vs. max_time-budget distinction:

### (a-i) max_time-budget failures (Z3 solve exceeds a too-tight solver budget; per TESTING_GUIDE.md 8.6 this never raises, it silently reports `model_found=False`, inverting the test's semantic conclusion)

- `theory_lib/bimodal/tests/integration/test_iterate.py::TestBimodalIteratorReal::test_iterate_example_generator_yields_models`
  -- shared `_build_example` helper used `max_time: 2`; observed solve times for this exact
  example are 2.8-4.4s even in isolation with no competing load. **Fixed**: bumped to `max_time:
  30` (matches the sibling-bimodal-examples convention). Also hardens the sibling test
  `test_iterate_two_produces_distinct_models` in the same class, which shares the helper.
- `builder/tests/unit/test_example.py::TestBuildExampleIntegration::test_build_example_bimodal_theory_countermodel`
  -- **not newly broken**: this is the test the delegation said was already fixed with
  `max_time=30`. Confirmed: passes 3/3 in isolation and when run with the rest of its file (4/4
  runs clean). It appears in the original 27-failure full-sweep list purely as a rare flake under
  full-suite load, consistent with the documented ~20x Z3 solve-time variance (up to 15s observed
  elsewhere for an unrelated formula). Not additionally mitigated; residual risk accepted given
  the budget is already at the documented generous convention.
- `code/tests/integration/test_timeout_resources.py::TestTimeoutHandling::test_cli_command_timeout`
  -- runs a real N=64 CLI subprocess against a 5s subprocess timeout; Python-side constraint
  generation for N=64 plausibly exceeds 5s under load even though the Z3-side `max_time` is only
  0.01. Not fixed directly; addressed via the marker mechanism below (opt-out by default).

### (a-ii) wall-clock-assertion failures (measuring literal elapsed time against a fixed literal budget, no `max_time` setting involved)

- `builder/tests/integration/test_performance.py::TestBuilderPerformance::test_multiple_examples_process_efficiently`
  (observed 1.217s vs. 500ms budget)
- `builder/tests/integration/test_performance.py::TestBuilderPerformance::test_small_model_generation_completes_quickly`
  (observed 1.203s vs. 500ms budget)

Neither was loosened (that would require picking a new, possibly-arbitrary threshold); both are
addressed via the marker mechanism below.

## Recommended determinism mechanism: use the existing `slow` marker (no new infrastructure needed)

`code/pyproject.toml` already registers `slow: Tests that are computationally expensive and
skipped in CI` and `performance: Tests that verify performance characteristics` under
`[tool.pytest.ini_options]`, but **no test file actually used either marker** before this task.
Recommendation: apply the existing `slow` marker as a module-level `pytestmark`, not introduce a
tolerance scheme or a new marker. This is what was implemented:

- `code/tests/integration/test_performance.py` -- `pytestmark = pytest.mark.slow`
- `code/tests/integration/test_timeout_resources.py` -- `pytestmark = pytest.mark.slow`
- `code/src/model_checker/builder/tests/integration/test_performance.py` -- `pytestmark = pytest.mark.slow`

**This alone does not yet change default-run determinism** -- `addopts` in `pyproject.toml` does
not exclude `slow` by default, so a plain `pytest` invocation still runs these files. Realizing
the benefit requires a follow-up decision (deliberately not made unilaterally here, since it
changes default CI/test behavior project-wide): add `-m "not slow"` to the default invocations
documented in `CLAUDE.md`/`TESTING_GUIDE.md` (and any CI workflow), keeping a separate `-m slow`
(or unfiltered) invocation for full performance validation. This is a one-line `addopts` or
per-invocation change once approved.

`test_build_example_bimodal_theory_countermodel` and `test_cli_command_timeout` were deliberately
left out of the `slow`-marking (the first lives in a file of otherwise-fast unit tests where
marking the whole file `slow` would be overbroad; `test_cli_command_timeout` is inside
`test_timeout_resources.py`, already covered by that file's module-level marker).

## xdist / parallel-run safety

No test in the three now-`slow`-marked files, nor in the fixed files, shares mutable module-level
state, global singletons, or environment-variable side effects between tests (checked: no
module-level caches, no `os.environ` writes, `create_test_model`/`create_test_example` build a
fresh `Syntax`/`Semantics`/`ModelConstraints` per call). `test_sequential_vs_concurrent` and
`test_concurrent_model_building` spawn their own threads internally but don't share state across
test functions. None of this file set appears interleaving-sensitive in the way the oracle suite's
`-n 6` regressions were; no recommendation to add explicit serialization markers here. (This
project's `pyproject.toml` does not invoke `-n` by default, and this baseline does not recommend
enabling it.)

## Fixes applied (10 files + 1 new file)

1. `code/tests/utils/helpers.py` -- `create_test_model`: default `conclusions` `'A[]'` -> `'A'`;
   `semantics_class(full_settings, syntax)` -> `semantics_class(full_settings)`; docstring fixed.
2. `code/tests/fixtures/example_data.py` -- **new file**, provides `STANDARD_SETTINGS = {'N': 2,
   'max_time': 30}` (the module `test_empty_formula_lists` imports but that never existed).
3. `code/tests/e2e/test_batch_output_real.py` -- `["A[]"]` -> `["A"]`.
4. `code/tests/integration/test_performance.py` -- fixed 3 `X[]`-suffix formulas
   (`test_repeated_operations`, `test_many_propositions_performance`); added `pytestmark =
   pytest.mark.slow`.
5. `code/tests/integration/test_timeout_resources.py` -- fixed `f"p{i}[]"` -> `f"p{i}"`; added
   `pytestmark = pytest.mark.slow`.
6. `code/tests/integration/test_error_handling.py` -- fixed `test_very_long_formulas`'s `"P[]"`
   sentence letter and its incorrect parenthesization of unary `\neg`.
7. `code/src/model_checker/models/tests/unit/test_structure.py` -- `patch('z3.Solver')` ->
   `patch('z3.Solver', spec=Solver)`.
8. `code/src/model_checker/builder/tests/unit/test_project.py` -- default-theory assertion now
   checks `registry.get_registered()[0]` instead of a hardcoded `'logos'`.
9. `code/src/model_checker/builder/tests/e2e/test_full_pipeline.py` -- assertion string `"State
   Space"` -> `"World Histories"`.
10. `code/src/model_checker/theory_lib/bimodal/tests/integration/test_iterate.py` -- shared
    `_build_example`'s `max_time: 2` -> `max_time: 30`.
11. `code/src/model_checker/builder/tests/integration/test_performance.py` -- added `pytestmark =
    pytest.mark.slow` (no assertion changes).

## Verification methodology and its limits

The sandbox this task ran in had heavy *unrelated* concurrent load for most of the session
(multiple other `claude` sessions plus several `lean --worker` processes from an unrelated Lean
project, confirmed via `ps aux --sort=-%cpu`). This is the same class of interference documented
in TESTING_GUIDE.md 8.6 ("concurrent test sessions contend... a long suite can be killed outright
by resource pressure from a competing run"), and it made repeated full-file pytest re-runs
unreliable during this task (a background 8-file pytest invocation and a follow-up per-file loop
both stalled/timed out with no clean completion line, `run/per-file-verify.txt`).

Given that, every fix in this report was independently confirmed by direct interpreter-level
reconstruction of the exact code path the test exercises (constructing `Syntax`/`Semantics`/
`ModelConstraints`/`ModelDefaults` by hand with the corrected arguments/formulas, or reproducing
the `unittest.mock` spec behavior in isolation) rather than solely by re-running the full test
file under pytest. This is weaker than a clean pytest pass for the file as a whole (it doesn't
catch e.g. an unrelated import error in the same file), but it does directly confirm the specific
defect and fix for each node id listed above. The original 27-failure sweep (before any fixes)
was a full, clean, uncontended pytest run with a normal completion summary, so those 27 counts and
node ids are solid.

## Not fixed / left for follow-up

- `test_find_next_model_basic` (genuine API-drift defect, needs a design decision).
- Wall-clock budgets in `builder/tests/integration/test_performance.py` and the subprocess timeout
  in `test_cli_command_timeout` were not loosened, only marked `slow` (opt-out mechanism, not a
  budget fix).
- The `-m "not slow"` default-invocation change (to actually realize determinism) was not applied
  to `CLAUDE.md`/`TESTING_GUIDE.md`/CI config -- flagged as a follow-up decision.
- Independent confirmation that all 22 targeted fixes now pass end-to-end: a background
  re-verification run did not finish cleanly (see handoff `blockers`); a smaller per-file
  re-verification was launched and its output is at `run/per-file-verify.txt` in this task
  directory.
