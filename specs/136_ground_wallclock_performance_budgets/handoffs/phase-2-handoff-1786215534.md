# Phase 2 handoff — code/tests/integration/test_performance.py

- All five `@pytest.mark.slow` class decorators deleted (TestExecutionPerformance, TestMemoryPerformance,
  TestBatchPerformance, TestCachingPerformance, TestWorstCasePerformance). Header comment rewritten.
- No tests deleted from this file (16 before, 16 after).
- Timing clauses deleted + behavioural assertion added: `test_simple_model_performance` (now asserts
  `model is not None`, `model.N == 3`, `model.semantics is not None`), `test_medium_model_performance`,
  `test_scaling_with_n` (parametrize reduced to `n` only; the `max_time` tuple element existed solely to
  feed the deleted budget), `test_batch_small_examples`, `test_batch_mixed_complexity`,
  `test_maximum_n_performance`, `test_many_propositions_performance`.
- `test_complex_model_performance`: 20s/30s budgets RETAINED as documented hang guards (real N=16 cost ~6s).
- `test_repeated_operations`: converted to a determinism assertion on `Syntax.all_sentences` /
  `infix_conclusions`. NO fallback needed -- the structure is comparable (verified by probe).
- `test_theory_loading_performance`: converted to `get_theory('bimodal') is get_theory('bimodal')`.
  NO fallback needed -- identity VERIFIED True by probe before the edit.
- Cap-burn: `test_memory_cleanup` now passes `'max_time': 0.05` to its 5 `create_test_model` calls.
- `TestConcurrentPerformance` untouched: no changed line falls inside it (only the module header comment,
  which previously referenced it, changed).
- Verification: 3 consecutive isolated runs, identical `16 passed` in 16.22/15.73/14.49s.
