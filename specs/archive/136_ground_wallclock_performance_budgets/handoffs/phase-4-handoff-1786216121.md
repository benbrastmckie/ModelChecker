# Phase 4 handoff — marker sweep and filtered-suite verification

- `-m slow --collect-only`: **1/2190 collected, 2189 deselected** — exactly
  `src/model_checker/models/tests/unit/test_semantic.py::TestSemanticDefaultsNBounds::test_max_n_itself_is_constructible`.
  It keeps its mark and docstring; not unmarked. (Baseline was 41/2195.)
- Deleted-test accounting: 2195 baseline - 5 deletions = **2190** collected unfiltered. Confirmed.
  Deletions: builder `test_large_model_generation_completes_within_timeout`,
  `test_constraint_generation_scales_linearly`, `TestMemoryUsage::test_memory_usage_stays_within_bounds`,
  `TestMemoryUsage::test_no_memory_leaks_in_iteration`; timeout-file `test_keyboard_interrupt_cleanup`.
  No fallback deletions were required (all three "if the property does not hold" fallbacks were
  pre-verified by probe and the property held in every case).
- Filtered default suite: **2189 passed, 1 deselected in 374.33s (6:14)**. Green.
  (addopts-comment baseline: 1 failed / 2136 passed / 43 deselected in 5:37. The filtered run is now
  slower because the 40 un-marked tests already rejoined it in Phases 1-3.)
- `pytest-timeout` is installed and loaded (pytest 9.0.3), so the retained `@pytest.mark.timeout(...)`
  hang guards are real, not silently-ignored unknown marks. Phase 5 declares it in the `dev` extra.
