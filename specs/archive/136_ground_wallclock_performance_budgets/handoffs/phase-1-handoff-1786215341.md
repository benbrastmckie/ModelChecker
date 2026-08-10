# Phase 1 handoff — builder performance file

- File: `code/src/model_checker/builder/tests/integration/test_performance.py`
- Module-level `pytestmark = pytest.mark.slow` deleted (with its comment block); `import pytest` removed (no longer used).
- Deleted outright (4 tests): `test_large_model_generation_completes_within_timeout` (copy-paste duplicate of medium),
  `test_constraint_generation_scales_linearly` (all four cases cap-pinned, ratio ~1.0 vs 4/9/16),
  `TestMemoryUsage::test_memory_usage_stays_within_bounds` and `::test_no_memory_leaks_in_iteration` (both `assertTrue(True)` placeholders; class deleted).
  NOTE: the plan's Phase 4 text says "5 deletions from the builder file"; the actual disposition table lists 4. 4 is correct.
- Renamed + timing deleted, behavioural assertion added: `test_small_model_runs_end_to_end`,
  `test_medium_model_runs_end_to_end`, `test_multiple_examples_run_end_to_end`, `test_comparison_mode_runs_end_to_end`
  (each now asserts the loaded `example_range` / `semantic_theories` content).
- Retained: `test_module_loading_performance` (hang-guard comment added), `test_serialization_performance` (untouched).
- Verification: 3 consecutive isolated runs, identical result set `6 passed` in 8.13/8.09/8.10s. Was 10 tests.
