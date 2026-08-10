# Phase 3 handoff — code/tests/integration/test_timeout_resources.py

- All `@pytest.mark.slow` marks deleted: 4 class decorators (TestTimeoutHandling, TestInterruptHandling,
  TestPerformanceDegradation, TestResourceRecovery) and 2 per-method marks in TestResourceLimits.
  Header comment and TestResourceLimits docstring rewritten.
- Deleted (1 test): `test_keyboard_interrupt_cleanup` -- asserted only that a path was truthy, never
  sent an interrupt. 16 tests before, 15 after.
- Retained as documented hang guards: `test_z3_solver_timeout` (5s vs 0.07-0.09s measured),
  `test_cli_command_timeout` (6s, backed by the subprocess's own timeout=5).
- `test_various_timeout_values`: tautological `settings['max_time'] == timeout_value` replaced by
  `model.max_time == timeout_value` and `model.settings['max_time'] == timeout_value`. NO fallback
  needed -- `ModelDefaults.max_time` exposes the resolved setting (verified by probe before the edit).
  Assertions moved out of the try block so a failure cannot be swallowed by the except branch.
- `test_many_propositions`: had no assertion at all; now asserts `model is not None` on the success path.
- Timing clauses deleted: `test_performance_with_many_constraints`, `test_scaling_behavior`
  (parametrize reduced to `n`; a fixed `max_time: 0.05` replaces the derived cap).
- Cap-burn: `test_memory_released_after_error` now sets `max_time: 0.05` -> 0.96s (was 10.88-11.06s).
  `test_file_handles_closed` CLI iterations 5 -> 3 -> 2.34s (was 3.23-3.68s).
- `test_concurrent_model_building` untouched: no changed line falls inside it.
- Verification: 3 consecutive isolated runs, identical `15 passed` in 8.89/8.49/9.07s (was ~25s+).
