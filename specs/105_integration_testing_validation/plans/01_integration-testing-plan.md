# Implementation Plan: Task #105

- **Task**: 105 - Integration testing and validation
- **Status**: [NOT STARTED]
- **Effort**: 5 hours
- **Dependencies**: 103 (completed), 104 (completed), 112 (completed)
- **Research Inputs**: specs/105_integration_testing_validation/reports/01_integration-testing.md
- **Artifacts**: plans/01_integration-testing-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: python
- **Lean Intent**: false

## Overview

Create a comprehensive integration test file (`test_oracle_interface.py`) that validates the Z3OracleProvider through the `find_countermodel()` API (not the internal `run_test` pipeline), covering all 52 examples, enriched formula round-trips, cross-signal spot checks, ternary serialization, boundary/temporal_depth consistency, edge cases, entry-point discovery, and Z3 state isolation. The existing test suite (710 tests) covers internal pipeline regression; this task fills the 8 gaps identified in research by testing exclusively through the oracle's public API surface.

### Research Integration

Key findings from the research report (01_integration-testing.md):
- **52 examples** in `examples.py` (13 countermodels + 39 theorems), not 43 as stated in the original task description; 43 is the count after excluding 9 timeout-sensitive examples
- **Oracle API gap**: Existing `test_oracle_provider.py` regression tests use `run_test()` (internal pipeline), not `find_countermodel()`. The oracle API takes a single JSON formula (no premises), so examples with premises must be tested on their conclusion formula only, with expected behavior documented per-example
- **11 enriched operators** with known primitive expansions -- none currently tested through `find_countermodel()`
- **SPOT_CHECK_FORMULAS**: 10 known-invalid formulas from BimodalHarness `_mock.py`; 5 box-containing formulas may disagree due to S5 vs Kripke semantics divergence
- **Task 114 fix**: `M = max(depth+2, 3)` is now active, so `boundary_safe = True` for all non-timeout examples
- **Entry-point discovery** requires editable install (`pip install -e .`); tests must skip gracefully if not installed

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No actionable ROADMAP.md items found (roadmap contains only placeholder).

## Goals & Non-Goals

**Goals**:
- Run all 52 bimodal examples through `find_countermodel()` as parametrized oracle regression tests (with documented exclusions for timeout-sensitive examples)
- Verify enriched formula round-trips: each of 11 enriched operators submitted in enriched and primitive form produce identical SAT/UNSAT via the oracle
- Validate `formula_folded_json` presence and correctness in all SAT outputs
- Verify ternary `{source, duration, target}` serialization across all SAT results
- Confirm `temporal_depth` consistency between enriched and primitive forms
- Test `validate_self()` with BimodalHarness SPOT_CHECK_FORMULAS
- Cover edge cases: timeout, unsupported frame_class, malformed JSON
- Verify entry-point discovery (conditional on package installation)
- Confirm Z3 isolation under 100+ sequential calls with memory tracking

**Non-Goals**:
- Duplicating internal pipeline tests already covered by `test_bimodal.py` and `test_oracle_provider.py`
- Testing BimodalHarness internals (that is BimodalHarness's responsibility)
- Achieving complete coverage of all possible formula structures (differential testing in task 109 covers that)
- Modifying any production code -- this is a pure test-writing task

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Examples with premises yield different oracle results than pipeline | M | H | Document per-example that oracle tests conclusion only; compare against manually determined expected oracle behavior |
| Timeout-sensitive examples cause CI flakiness | H | M | Use REGRESSION_TIMEOUT_EXAMPLES exclusion set consistent with existing tests; generous timeout_ms for temporal formulas |
| SPOT_CHECK_FORMULAS import fails (BimodalHarness not installed) | M | M | Conditional import with `pytest.importorskip` or `skipIf` |
| Entry-point discovery test fails in dev environment | L | H | Use `pytest.mark.skipif` checking for installed package metadata |
| Z3 memory measurement noise gives false positives | M | M | Use generous threshold (50% growth tolerance); measure over 200+ calls |
| TopOperator bug affects enriched `top` tests | L | L | Use `imp(bot, bot)` expansion for top, document the known bug |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2, 3, 4 | 1 |

Phases within the same wave can execute in parallel.

---

### Phase 1: Oracle interface regression tests [COMPLETED]

**Goal**: Create `test_oracle_interface.py` with oracle protocol compliance tests and the 52-example regression suite through `find_countermodel()`.

**Tasks**:
- [ ] Create `code/src/model_checker/theory_lib/bimodal/tests/unit/test_oracle_interface.py`
- [ ] Implement test fixtures: JSON formula constants for each example conclusion (converting infix to JSON dict)
- [ ] Build `_example_conclusion_to_json()` helper: for each of the 52 examples, construct the JSON dict for its first conclusion formula (hand-crafted JSON dicts matching the infix strings)
- [ ] Create `EXAMPLE_JSON_CATALOG` dict mapping example names to `(json_formula, has_premises, expected_sat)` tuples
- [ ] For no-premises examples: `expected_sat` matches `expectation` from settings
- [ ] For premises examples: document that oracle tests conclusion only; determine expected SAT/UNSAT for each conclusion formula independently
- [ ] **TestOracleProtocolCompliance** class:
  - [ ] `test_provider_implements_protocol()`: verify `isinstance(provider, OracleProvider)` using runtime_checkable (conditional import from BimodalHarness)
  - [ ] `test_five_properties_exist()`: verify all 5 required properties (provider_id, provider_version, semantics_version, supported_frame_classes, capabilities)
  - [ ] `test_find_countermodel_method_exists()`: verify method signature
  - [ ] `test_validate_self_method_exists()`: verify method signature
  - [ ] `test_return_format_sat()`: verify SAT returns dict matching StructuredCountermodel schema (all required keys, correct types)
  - [ ] `test_return_format_unsat()`: verify UNSAT returns None
- [ ] **TestOracleExampleRegressionViaAPI** class:
  - [ ] Parametrize over `EXAMPLE_JSON_CATALOG` entries (excluding REGRESSION_TIMEOUT_EXAMPLES)
  - [ ] For each example: call `provider.find_countermodel(json_formula)` and verify SAT/UNSAT matches expected
  - [ ] Verify `test_active_example_count()` reports correct number of active examples
- [ ] Run tests: `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/unit/test_oracle_interface.py -v`

**Timing**: 2 hours

**Depends on**: none

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_oracle_interface.py` -- new file (primary deliverable)

**Verification**:
- All protocol compliance tests pass
- 42+ parametrized example tests pass (52 minus timeout exclusions)
- No imports from internal pipeline (`run_test` must not appear in this file)

---

### Phase 2: Enriched formula round-trip tests [NOT STARTED]

**Goal**: For each of the 11 enriched operators, verify that submitting enriched-tag JSON and primitive-tag JSON to `find_countermodel()` yields identical SAT/UNSAT results, and that `formula_folded_json` and `temporal_depth` are consistent.

**Tasks**:
- [ ] **TestEnrichedRoundTrip** class in `test_oracle_interface.py`:
  - [ ] Create `ENRICHED_PRIMITIVE_PAIRS` list: 11 entries, each a tuple of `(enriched_json, primitive_json, operator_name)`
  - [ ] For each pair, construct a formula that is SAT (has countermodel) so we can compare outputs
  - [ ] `test_enriched_vs_primitive_sat_agreement(operator_name, enriched_json, primitive_json)`: parametrized test verifying both forms return same SAT/UNSAT
  - [ ] `test_temporal_depth_identical(operator_name, enriched_json, primitive_json)`: for SAT results, verify `temporal_depth` is identical in both outputs
  - [ ] `test_formula_folded_json_present_all_sat()`: for each enriched operator producing SAT, verify `formula_folded_json` key exists and is a valid formula dict with `tag` key
  - [ ] `test_formula_folded_json_uses_enriched_tags()`: verify that `formula_folded_json` uses enriched tags where possible (fold_formula maximizes enriched operators)
- [ ] **TestMixedFormulas** class:
  - [ ] `test_mixed_enriched_primitive_formula()`: submit formulas combining enriched and primitive tags (e.g., `imp(neg(A), some_future(B))`) and verify they produce valid results
  - [ ] 3-5 mixed formula tests covering L1, L2, L3 operator combinations
  - [ ] `test_deeply_nested_enriched()`: formula with 3+ levels of enriched operator nesting
- [ ] Run enriched round-trip tests

**Timing**: 1.5 hours

**Depends on**: 1

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_oracle_interface.py` -- add test classes

**Verification**:
- All 11 enriched operators produce identical SAT/UNSAT as their primitive equivalents
- `temporal_depth` matches between enriched and primitive forms
- `formula_folded_json` is present and valid in all SAT results
- Mixed formula tests pass without errors

---

### Phase 3: Cross-signal and boundary tests [NOT STARTED]

**Goal**: Validate cross-signal with SPOT_CHECK_FORMULAS, verify temporal_depth/boundary_safe consistency across all oracle outputs, and confirm ternary serialization format for all SAT results.

**Tasks**:
- [ ] **TestSpotCheckCrossSignal** class:
  - [ ] Conditional import of `SPOT_CHECK_FORMULAS` from `bimodal_harness.oracle._mock` with `pytest.importorskip`
  - [ ] `test_validate_self_temporal_only()`: filter SPOT_CHECK_FORMULAS to temporal-only (formulas 4-5, 7, 9-10), call `validate_self()`, expect True
  - [ ] `test_validate_self_all_formulas()`: call `validate_self()` with all 10, document expected result (may be False due to box semantics divergence)
  - [ ] `test_spot_check_individual_countermodels()`: for each temporal-only spot-check formula, call `find_countermodel()` individually and verify non-None result
- [ ] **TestBoundaryRegressionViaOracle** class:
  - [ ] `test_boundary_safe_true_for_all_examples()`: for each active (non-timeout) example in EXAMPLE_JSON_CATALOG, verify `boundary_safe == True` in the oracle output
  - [ ] `test_time_bound_formula()`: for formulas with known temporal_depth d, verify `time_bound == max(d+2, 3)` in the output
  - [ ] `test_temporal_depth_correct_in_output()`: for 5+ formulas with known temporal depths (0, 1, 2), verify `temporal_depth` matches expected value
- [ ] **TestTernarySerializationAll** class:
  - [ ] `test_all_sat_task_relation_ternary()`: iterate over all SAT results from EXAMPLE_JSON_CATALOG, verify every `task_relation` entry is a dict with exactly `{source, duration, target}` keys and integer values
  - [ ] `test_no_binary_pairs()`: verify no `task_relation` entry is a 2-element list/tuple
- [ ] Run cross-signal and boundary tests

**Timing**: 1 hour

**Depends on**: 1

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_oracle_interface.py` -- add test classes

**Verification**:
- SPOT_CHECK temporal-only formulas produce countermodels and `validate_self` returns True
- `boundary_safe == True` for all non-timeout oracle results
- `time_bound == max(depth+2, 3)` for all tested formulas
- All `task_relation` entries are ternary dicts with integer values

---

### Phase 4: Edge cases and stress tests [NOT STARTED]

**Goal**: Test timeout handling, unsupported frame_class, malformed JSON, entry-point discovery, and Z3 isolation with memory tracking.

**Tasks**:
- [ ] **TestEdgeCases** class:
  - [ ] `test_timeout_handling()`: construct a complex temporal formula and call `find_countermodel()` with `timeout_ms=1`; verify returns None (timeout treated as UNSAT/timeout)
  - [ ] `test_unsupported_frame_class_dense()`: call `find_countermodel(SIMPLE_SAT_JSON, frame_class="Dense")`, verify returns None
  - [ ] `test_unsupported_frame_class_arbitrary()`: call with frame_class="NonExistent", verify None
  - [ ] `test_malformed_formula_missing_tag()`: pass `{"foo": "bar"}` (no "tag" key), verify raises appropriate exception or returns None
  - [ ] `test_malformed_formula_unknown_tag()`: pass `{"tag": "unknown_operator"}`, verify raises or returns None
  - [ ] `test_malformed_formula_missing_fields()`: pass `{"tag": "imp"}` (missing left/right), verify raises or returns None
- [ ] **TestEntryPointDiscovery** class:
  - [ ] `test_entry_point_registered()`: use `importlib.metadata.entry_points(group="bimodal_harness.oracle_providers")` to check the `z3_base` entry point exists; skip if package not installed
  - [ ] `test_oracle_registry_discover()`: conditional import of `OracleRegistry`; call `discover()` and verify `z3_base` is found; skip if BimodalHarness not importable
  - [ ] `test_discovered_provider_is_correct_type()`: verify discovered provider is `Z3OracleProvider` instance
- [ ] **TestZ3IsolationStress** class:
  - [ ] `test_150_sequential_mixed_calls()`: run 150 sequential calls alternating SAT/UNSAT formulas with varying temporal depths (depth 0, 1, 2); verify consistent results throughout
  - [ ] `test_memory_growth_bounded()`: use `tracemalloc` to measure memory before and after 200 `find_countermodel()` calls; verify growth < 50% of initial snapshot (generous threshold to avoid noise)
  - [ ] `test_no_state_leakage_between_depths()`: run depth-0 formula, then depth-2 formula, then depth-0 again; verify depth-0 results are identical before and after
- [ ] Run edge case and stress tests
- [ ] Run full test suite to verify no regressions: `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/unit/test_oracle_interface.py -v`
- [ ] Run entire bimodal test suite: `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/ -v`

**Timing**: 1 hour

**Depends on**: 1

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_oracle_interface.py` -- add test classes

**Verification**:
- Timeout test returns None without crashing
- Unsupported frame_class returns None
- Malformed JSON raises exception or returns None (consistent behavior)
- Entry-point discovery succeeds (or skips gracefully if not installed)
- 150+ sequential calls produce consistent results with no state leakage
- Memory growth stays within threshold over 200 calls
- Full bimodal test suite passes with no regressions

## Testing & Validation

- [ ] All tests in `test_oracle_interface.py` pass: `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/unit/test_oracle_interface.py -v`
- [ ] 42+ oracle example regression tests pass via `find_countermodel()` API
- [ ] All 11 enriched operators produce identical SAT/UNSAT as primitive equivalents
- [ ] `formula_folded_json` is present in all SAT results
- [ ] All `task_relation` entries are ternary dicts
- [ ] `boundary_safe == True` for all non-timeout formulas
- [ ] `temporal_depth` is consistent between enriched and primitive forms
- [ ] No regressions in existing test suite: `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/ -v`

## Artifacts & Outputs

- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_oracle_interface.py` -- new integration test file (~140 tests)
- `specs/105_integration_testing_validation/plans/01_integration-testing-plan.md` -- this plan
- `specs/105_integration_testing_validation/summaries/01_integration-testing-summary.md` -- implementation summary (generated after implementation)

## Rollback/Contingency

This is a pure test-writing task with no production code changes. Rollback is trivial: delete `test_oracle_interface.py`. No other files are modified. If individual test categories prove problematic (e.g., memory measurement too noisy), they can be marked `@pytest.mark.skip` with documented reasons without affecting other test categories.
