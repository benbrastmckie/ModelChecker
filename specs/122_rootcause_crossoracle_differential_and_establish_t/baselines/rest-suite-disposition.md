# Everything-Else Full Suite (Phase 6): Failure Root-Cause and Disposition

Run: `PYTHONPATH=<pylibs>:code/src pytest code/tests/ code/src/model_checker
--ignore=code/src/model_checker/theory_lib/bimodal/tests -n 6
--junitxml=baselines/junit-rest.xml -q` -- 1880 tests, 1852 passed, 28 failed, 0 errors, 47.4s.

Collection is clean (0 errors), matching task-121's 2095-test/0-error full-suite baseline
(2095 total - 286 bimodal already measured in Phase 4 = 1809 expected; the extra ~71 tests to
1880 come from `code/tests/` top-level integration/e2e suites that were outside task-121's
`code/src/model_checker`-scoped collection check but are included here since Phase 6 covers
`code/tests/` + `code/src/model_checker`).

All 28 failures were re-run serially (`-n 0`, no concurrent workers) to rule out the CPU-
contention pattern found in Phases 4-5: **all 28 reproduced identically** (`28 failed in 14.27s`,
`baselines/rest-failures-serial-rerun.txt`) -- these are genuine, deterministic, pre-existing
conditions, not xdist/timing flakes. None trace to task 122's own source edits (`output/
__init__.py`, `builder/module.py`, the two oracle test files) -- confirmed by category below.

## Category A: already documented pre-existing (Phase 2), 6 tests

Exact overlap with Phase 2's `builder-suite-pre-existing-failures.txt` (recorded when this
task's `builder/module.py` fix was verified not to introduce new failures):

- `test_full_pipeline.py::TestFullPipeline::test_theory_library_execution` (display-format drift)
- `test_performance.py::TestBuilderPerformance::test_multiple_examples_process_efficiently` (timing threshold, 1.08s vs 500ms budget)
- `test_performance.py::TestBuilderPerformance::test_small_model_generation_completes_quickly` (timing threshold, 1.10s vs 500ms budget)
- `test_example.py::TestBuildExampleIntegration::test_find_next_model_basic` (`BuildExample` has no `find_next_model` attribute -- API drift)
- `test_project.py::TestBuildProjectCore::test_project_initialization_default` (default theory mismatch: `'bimodal' != 'logos'`)
- `test_serialize.py::TestRealTheoryIntegration::test_serialize_real_bimodal_theory_preserves_structure` (serialization format assertion)

(Phase 2's 7th pre-existing failure, `test_example.py::test_logos_extensional_theory`, is a
documented ~25% intermittent flake and did not trigger in this run -- consistent with its
recorded flakiness, not a regression.)

## Category B: malformed `"A[]"` test-formula literal -- pre-existing, systemic, out of scope (10 tests)

- `test_batch_output_real.py::TestBatchOutputReal::test_bimodal_batch_output`
- `test_performance.py::TestMemoryPerformance::test_memory_usage_simple`
- `test_performance.py::TestMemoryPerformance::test_memory_usage_complex`
- `test_performance.py::TestMemoryPerformance::test_memory_cleanup`
- `test_performance.py::TestExecutionPerformance::test_simple_model_performance`
- `test_performance.py::TestExecutionPerformance::test_medium_model_performance`
- `test_error_handling.py::TestFrameworkErrorHandling::test_z3_timeout_handling`
- `test_error_handling.py::TestFrameworkErrorHandling::test_memory_limit_handling`
- `test_timeout_resources.py::TestResourceLimits::test_large_state_space`
- `test_timeout_resources.py::TestResourceLimits::test_many_propositions`

Root cause: `code/tests/utils/helpers.py::create_test_model()` (line ~283) defaults
`conclusions=['A[]']` ("Simple valid formula" per its own docstring -- it is not). `test_
bimodal_batch_output` independently hardcodes the identical literal `["A[]"]` in an inline
example module. `A[]` is not valid formula syntax for the current parser: it produces
`ValueError: Empty token list` (or, for tests wrapping the call in a try/except that inspects
the exception message, `ValueError: The expression [] is incomplete.`) deep in
`model_checker.utils.parsing.parse_expression`, deterministically, every time
`create_test_model()` is called with default conclusions, or whenever the hardcoded `"A[]"`
literal is used. This is a shared test-helper defect that predates task 122 (none of task 122's
source edits touch `code/tests/utils/helpers.py`, `code/tests/integration/test_performance.py`,
`code/tests/integration/test_error_handling.py`, `code/tests/integration/test_timeout_
resources.py`, or `code/tests/e2e/test_batch_output_real.py`) and affects every test built on
top of the shared `create_test_model()` default. Out of scope for task 122 (fixing it is a
one-line change to a shared fixture but touches 10 tests' worth of behavior across performance/
timeout/error-handling suites unrelated to the differential/oracle gate -- recommended as a
dedicated, cheap follow-up task rather than an unreviewed drive-by fix here).

## Category C: timing/threshold tests sensitive to machine load -- pre-existing, out of scope (4 tests)

- `test_performance.py::TestConcurrentPerformance::test_sequential_vs_concurrent` (`assert 0.0008s < 0.00018s` -- compares near-zero-duration measurements, inherently noisy at microsecond scale)
- `test_timeout_resources.py::TestTimeoutHandling::test_cli_command_timeout` (subprocess killed at a hardcoded 5s budget; environment-dependent)
- `test_timeout_resources.py::TestTimeoutHandling::test_various_timeout_values[0.01]` (`assert 0.01 < 0.01` -- boundary-equal comparison, not strict, fails by construction)
- `test_timeout_resources.py::TestTimeoutHandling::test_various_timeout_values[0.1]` (`assert 0.1 < 0.01` -- looks like a parametrize-id/threshold mismatch in the test itself)

Root cause: test-authoring defects (non-strict/boundary-equal comparisons, comparing
microsecond-scale durations, a hardcoded CLI timeout budget) unrelated to task 122's scope.
None involve bimodal/oracle code paths.

## Category D: broken scaling assertion -- pre-existing, out of scope (2 tests)

- `test_performance.py::TestExecutionPerformance::test_scaling_with_n[2-1.0]` (`assert 2 >= 8`)
- `test_performance.py::TestExecutionPerformance::test_scaling_with_n[4-2.0]` (`assert 4 >= 8`)

The assertion compares a parametrized `N` value against a hardcoded `8` that does not match the
parametrize table (`N=2`, `N=4` cases can never satisfy `>= 8`) -- a test-authoring defect
(likely a stale threshold left over from a prior parametrize table), not a production regression.

## Category E: mock API misuse -- pre-existing, out of scope (1 test)

- `test_structure.py::TestModelDefaultsStructure::test_attribute_initialization_order`
  (`AttributeError: 'assert_and_track' is not a valid assertion... Did you mean:
  'assert_any_call'?`)

The test calls a nonexistent `Mock.assert_and_track(...)` method (not a real `unittest.mock`
API) instead of a real assertion method -- a test-authoring bug unrelated to `ModelDefaults`'
actual attribute-initialization behavior.

## Category F: missing fixtures module -- pre-existing, out of scope (1 test)

- `test_error_handling.py::TestEdgeCases::test_empty_formula_lists`
  (`ModuleNotFoundError: No module named 'tests.fixtures.example_data'`)

References a `tests/fixtures/example_data` module that does not exist in the current tree
(likely dropped during an earlier test-tree restoration/reorganization, tasks 119-121, without
updating this reference). Not touched by task 122.

## Category G: parsing defect variant of Category B -- pre-existing, out of scope (1 test)

- `test_error_handling.py::TestEdgeCases::test_very_long_formulas`
  (`ValueError: The expression [] is incomplete.`)
- `test_performance.py::TestCachingPerformance::test_repeated_operations`
  (`ValueError: The expression [] is incomplete.`)

Same empty/malformed-expression parsing failure family as Category B (different call site, same
underlying "constructing a formula from an empty/placeholder string" pattern), not traced to a
single shared literal but the same class of test-authoring defect.

## Category H: `WitnessRegistryError`/`WitnessConstraintError.theory` not set as expected -- pre-existing, out of scope (2 tests)

- `test_error_handling.py::TestWitnessErrorHandling::test_witness_registry_error_basic`
  (`assert None == 'exclusion'`)
- `test_error_handling.py::TestWitnessErrorHandling::test_witness_constraint_error_basic`
  (`assert None == 'exclusion'`)

`WitnessRegistryError`/`WitnessConstraintError` are constructed without their `theory` field
being populated (defaults to `None`) where the test expects `'exclusion'`. Plausibly related to
task 120's exclusion-theory restoration (a constructor-arg wiring gap), but not part of task
122's declared scope (bimodal/oracle differential and the release gate) and not touched by any
of task 122's source edits. Documented for a follow-up task closer to exclusion-theory
maintenance.

## Final disposition summary

| Category | Count | Root cause class | Pre-existing? | Fixed here? |
|---|---|---|---|---|
| A | 6 | Already documented in Phase 2 (`builder/` suite) | Yes | No -- out of scope |
| B | 10 | Malformed `"A[]"` shared test-formula literal | Yes | No -- out of scope, recommend follow-up |
| C | 4 | Timing/threshold test-authoring defects | Yes | No -- out of scope |
| D | 2 | Broken scaling-assertion threshold | Yes | No -- out of scope |
| E | 1 | Mock API misuse in test | Yes | No -- out of scope |
| F | 1 | Missing `tests.fixtures.example_data` module | Yes | No -- out of scope |
| G | 2 | Empty/malformed-expression parsing (Category B variant) | Yes | No -- out of scope |
| H | 2 | `WitnessRegistryError`/`WitnessConstraintError.theory` unset | Yes | No -- out of scope |
| **Total** | **28** | | | |

All 28 failures are confirmed deterministic (non-flaky, reproduce serially) and pre-existing --
none trace to task 122's source edits or to the differential/oracle work this task targets.
Recommended follow-up: a dedicated `general` or `python` task to (1) fix the shared `"A[]"`
literal in `code/tests/utils/helpers.py::create_test_model()` and `test_batch_output_real.py`
(Categories B/G, 12 tests, likely the highest-value single fix), (2) restore or remove the
`tests.fixtures.example_data` reference (Category F), (3) wire `theory` into
`WitnessRegistryError`/`WitnessConstraintError` construction (Category H), and (4) either fix or
delete the remaining test-authoring defects (Categories C, D, E). None of this is required for
task 122's own definition of done (differential root-caused, bimodal/oracle suites green,
release baseline recorded with justified pre-existing gaps documented).
