# Implementation Plan: OracleProvider Implementation with Programmatic Pipeline

- **Task**: 103 - OracleProvider implementation with programmatic pipeline
- **Status**: [NOT STARTED]
- **Effort**: 6 hours
- **Dependencies**: 101 (completed), 102 (completed), 112 (completed)
- **Research Inputs**: reports/01_tiered-oracle-architecture.md, reports/02_oracle-provider-research.md
- **Artifacts**: plans/01_oracle-provider-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: python
- **Lean Intent**: false

## Overview

Implement the Z3OracleProvider class and serialization layer to provide a complete programmatic pipeline from JSON formula input to structured countermodel output. The pipeline wires together already-completed components: `json_to_prefix()` and `temporal_depth()` (task 102), `fold_formula()` (task 112), `BimodalSemantics`, `ModelConstraints`, `BimodalStructure`, and `isolated_z3_context()`. The core work is: (1) serialization helpers for countermodel extraction, (2) the `find_countermodel()` method with Z3 isolation, (3) state-leakage validation, and (4) a 43-example regression test through the oracle interface.

### Research Integration

Report 02 (oracle-provider-research) provided the definitive pipeline correction: Syntax accepts infix strings, not Sentence objects. The actual flow is `json_to_prefix() -> prefix_to_infix() -> Syntax([], [infix], bimodal_operators) -> ModelConstraints -> BimodalStructure`. Report 02 also confirmed: (a) entry point is already registered in pyproject.toml, (b) BimodalStructure's second parameter is named `max_time` but receives the full settings dict, (c) the ternary task_rel extraction loop from ADR Decision 6 iterates O(2^(2N) * (2M-1)) evaluations, (d) `extract_model_elements()` is called automatically in `BimodalStructure.__init__()` so results are available on structure attributes.

Report 01 (tiered-oracle-architecture) proposed a fast QF Tier 1 alongside the quantified Tier 2. This plan implements Tier 2 only (the quantified BimodalSemantics pipeline) per the task description. Tier 1 integration is out of scope.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md found.

## Goals & Non-Goals

**Goals**:
- Implement `Z3OracleProvider` with full `find_countermodel()` pipeline
- Implement countermodel serialization (SimpleCountermodel + StructuredCountermodel)
- Ensure Z3 context isolation (no state leakage across calls)
- Produce correct SAT/UNSAT for all 43 active examples through the oracle interface
- Include `formula_folded_json` in all non-None outputs
- Implement `validate_self()` for spot-check validation

**Non-Goals**:
- Tiered oracle dispatch (Tier 1 QF fast solver) -- that is a future enhancement
- Subformula truth valuations with folded representations (the task mentions this for StructuredCountermodel but implementing full subformula tracking requires deep proposition tree traversal; atom-level truth valuation is implemented, subformula folding is noted for future work)
- Modifying pyproject.toml entry points (already registered)
- Converting all 43 examples from infix to JSON (the oracle pipeline test uses the infix pipeline via Syntax, same as existing tests, but through find_countermodel)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| BimodalStructure max_time parameter confusion | H | M | Pass full settings dict as second arg; research confirmed this pattern |
| Bitvec serialization: world_histories contain Z3 objects | M | L | Use `z3_model.eval(state).as_long()` for int conversion |
| 43-example test needs formula_json format but examples use infix | H | M | Convert infix examples through the standard pipeline (premises+conclusions), not through JSON oracle; create separate JSON-based tests for oracle-specific validation |
| State leakage in 100-call test | M | L | isolated_z3_context already resets AtomSort cache; test will detect any residual leakage |
| Timeout handling in BimodalStructure | M | L | Pass max_time via settings dict; structure.timeout flag captures timeouts |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4 | 3 |
| 5 | 5 | 4 |

Phases within the same wave can execute in parallel.

### Phase 1: Test Infrastructure and Provider Property Tests [COMPLETED]

**Goal**: Create the test file with failing tests for provider properties, basic find_countermodel contracts, and serialization output structure.

**Tasks**:
- [x] Create `code/src/model_checker/theory_lib/bimodal/tests/unit/test_oracle_provider.py`
- [x] Write `TestProviderProperties` class:
  - [x] `test_provider_id` -- assert `provider_id == "bmlogic_z3_base_v1"`
  - [x] `test_supported_frame_classes` -- assert `frozenset({"Base"})`
  - [x] `test_capabilities_dict` -- assert capabilities is a dict with expected keys
  - [x] `test_provider_version_semver` -- assert version matches semver pattern
  - [x] `test_semantics_version` -- assert semantics_version is a non-empty string
- [x] Write `TestFindCountermodelContract` class:
  - [x] `test_unsupported_frame_class_returns_none` -- pass frame_class="Foo", expect None
  - [x] `test_sat_formula_returns_dict` -- pass known-invalid formula, expect dict
  - [x] `test_unsat_formula_returns_none` -- pass a tautology, expect None
  - [x] `test_result_has_required_keys` -- check temporal_depth, boundary_safe, time_bound, semantics_version, formula_folded_json, trueAtoms, falseAtoms, world_histories, task_relation
  - [x] `test_boundary_safe_flag` -- verify M > depth + 1 for simple formulas
  - [x] `test_formula_folded_json_present` -- verify formula_folded_json is dict
  - [x] `test_task_relation_ternary_format` -- verify triples have source/duration/target keys
- [x] Write `TestValidateSelf` class:
  - [x] `test_validate_self_with_known_invalid` -- pass known-invalid formulas, expect True
  - [x] `test_validate_self_with_tautology_fails` -- pass a tautology, expect False
- [x] Define helper JSON formulas for test fixtures (simple SAT and UNSAT cases)
- [x] Run tests, confirm they fail (RED phase) -- confirmed: 32 fail, 2 pass (only non-provider tests)

**Timing**: 1.5 hours

**Depends on**: none

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_oracle_provider.py` - create new test file

**Verification**:
- All tests exist and fail with appropriate import/attribute errors
- `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/unit/test_oracle_provider.py -v` shows all tests collected and failing

---

### Phase 2: Serialization Helpers [COMPLETED]

**Goal**: Implement the countermodel serialization module with helpers for atom extraction, task_rel triples, world history conversion, and truth valuation.

**Tasks**:
- [ ] Implement `extract_true_false_atoms(z3_model, semantics, model_constraints, structure)` in `serialization.py`:
  - [ ] Iterate `model_constraints.sentence_letters`
  - [ ] Get main world state from `structure.world_histories[0][0]`
  - [ ] Evaluate `semantics.truth_condition(main_state, atom_const)` on z3_model
  - [ ] Return `(trueAtoms, falseAtoms)` as lists of `{"name": str}` dicts
- [ ] Implement `extract_task_triples(z3_model, semantics)`:
  - [ ] Loop: `for s in range(2**N): for d in range(-(M-1), M): for u in range(2**N):`
  - [ ] Evaluate `semantics.task_rel(s, d, u)` via `is_true(z3_model.eval(...))`
  - [ ] Return list of `{"source": s, "duration": d, "target": u}` dicts
- [ ] Implement `serialize_world_histories(structure, z3_model)`:
  - [ ] Convert `structure.world_histories` bitvec values to Python ints
  - [ ] Return list of `{"world_id": w, "times": {str(t): int(state)}}` dicts
- [ ] Implement `extract_truth_valuation(z3_model, semantics, model_constraints, structure)`:
  - [ ] For each atom, each world, each time: evaluate truth_condition
  - [ ] Return `{atom_name: {world_id: {time: bool}}}` nested dict
- [ ] Implement `serialize_countermodel(z3_model, semantics, model_constraints, structure, formula_json, formula_folded, depth, M, semantics_version)`:
  - [ ] Assemble full result dict combining SimpleCountermodel + StructuredCountermodel fields
  - [ ] Include: trueAtoms, falseAtoms, formula, world_histories, task_relation, truth_valuation, evaluation_world, evaluation_time, world_count, time_bound, temporal_depth, boundary_safe, semantics_version, formula_folded_json
- [ ] Add imports for `is_true` from `model_checker.solver`
- [ ] Run serialization-related tests from Phase 1 (those testing output structure)

**Timing**: 1.5 hours

**Depends on**: 1

**Files to modify**:
- `code/src/bimodal_logic/serialization.py` - implement all serialization helpers

**Verification**:
- Serialization functions can be imported
- Helper functions produce correctly shaped output when given valid inputs
- `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/unit/test_oracle_provider.py::TestFindCountermodelContract -v` -- serialization-dependent tests may still fail until Phase 3 wires the pipeline

---

### Phase 3: Z3OracleProvider Implementation [COMPLETED]

**Goal**: Implement the full Z3OracleProvider class with find_countermodel(), validate_self(), and all required properties.

**Tasks**:
- [ ] Implement provider properties on `Z3OracleProvider`:
  - [ ] `provider_id = "bmlogic_z3_base_v1"`
  - [ ] `provider_version` -- use `bimodal_logic.__version__` or hardcode `"0.1.0"`
  - [ ] `semantics_version` -- hardcode `"bimodal-logic-v0.1.0"`
  - [ ] `supported_frame_classes = frozenset({"Base"})` (already in stub)
  - [ ] `capabilities` dict with `max_N`, `max_M`, `supports_enriched_tags`, `z3_timeout_configurable`
- [ ] Implement `__init__(self)`:
  - [ ] Set `self._semantics = None` (no persistent reference)
- [ ] Implement `find_countermodel(self, formula_json, frame_class="Base", timeout_ms=5000)`:
  - [ ] Return None if `frame_class not in self.supported_frame_classes`
  - [ ] Compute `depth = temporal_depth(formula_json)`
  - [ ] Compute `M = max(depth + 2, 3)`
  - [ ] Compute `formula_folded = fold_formula(formula_json)`
  - [ ] Convert: `prefix = json_to_prefix(formula_json)`, `infix = prefix_to_infix(prefix)`
  - [ ] Build settings dict: `{'N': 2, 'M': M, 'contingent': False, 'disjoint': False, 'max_time': timeout_ms / 1000.0, 'expectation': True, 'solver': 'z3'}`
  - [ ] Reset: `self._semantics = None`
  - [ ] Wrap in `with isolated_z3_context():`
  - [ ] Create `BimodalSemantics(settings)`
  - [ ] Create `Syntax([], [infix], bimodal_operators)`
  - [ ] Create `ModelConstraints(settings, syntax, semantics, BimodalProposition)`
  - [ ] Create `BimodalStructure(model_constraints, settings)`
  - [ ] Check: if `structure.timeout or not structure.z3_model_status` return None
  - [ ] Call `serialize_countermodel(...)` from serialization module
  - [ ] Return result dict
- [ ] Implement `validate_self(self, spot_check_formulas)`:
  - [ ] Iterate formulas, call `find_countermodel()` for each
  - [ ] Return True only if all produce non-None results
- [ ] Add all required imports:
  - [ ] `from .translation import json_to_prefix, temporal_depth, prefix_to_infix, fold_formula`
  - [ ] `from .serialization import serialize_countermodel`
  - [ ] `from model_checker.utils.context import isolated_z3_context`
  - [ ] `from model_checker import ModelConstraints, Syntax`
  - [ ] `from model_checker.theory_lib.bimodal import BimodalSemantics, BimodalProposition, bimodal_operators`
- [ ] Run all Phase 1 tests -- property tests and contract tests should pass

**Timing**: 1.5 hours

**Depends on**: 2

**Files to modify**:
- `code/src/bimodal_logic/provider.py` - implement full Z3OracleProvider class
- `code/src/bimodal_logic/__init__.py` - verify exports (already exports Z3OracleProvider)

**Verification**:
- `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/unit/test_oracle_provider.py -v` -- all Phase 1 tests pass (GREEN)
- Provider can be instantiated and properties are accessible
- `find_countermodel()` returns dict for SAT formula and None for UNSAT formula

---

### Phase 4: Z3 Isolation and State Leakage Test [COMPLETED]

**Goal**: Verify that 100 sequential `find_countermodel()` calls produce consistent results with no state leakage.

**Tasks**:
- [ ] Add `TestStateIsolation` class to `test_oracle_provider.py`:
  - [ ] `test_100_sequential_sat_calls` -- call `find_countermodel()` 100 times on a simple SAT formula, verify all return non-None with identical structure (same atom sets, same world count)
  - [ ] `test_100_sequential_unsat_calls` -- call `find_countermodel()` 100 times on a tautology, verify all return None
  - [ ] `test_100_mixed_calls` -- interleave SAT and UNSAT formulas, verify correct result for each
  - [ ] `test_no_semantics_reference_leak` -- after find_countermodel(), verify `provider._semantics is None`
- [ ] Add `TestFormulaFoldedJson` class:
  - [ ] `test_folded_json_present_in_sat_result` -- verify formula_folded_json key exists and is a dict
  - [ ] `test_folded_json_is_valid_formula` -- verify formula_folded_json has "tag" key
  - [ ] `test_folded_json_for_primitive_input` -- verify fold_formula produces enriched form for primitive-only input
  - [ ] `test_folded_json_for_enriched_input` -- verify fold_formula is idempotent for enriched input
- [ ] Run the full test file

**Timing**: 0.5 hours

**Depends on**: 3

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_oracle_provider.py` - add isolation tests

**Verification**:
- `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/unit/test_oracle_provider.py::TestStateIsolation -v` -- all 100-call tests pass
- `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/unit/test_oracle_provider.py::TestFormulaFoldedJson -v` -- all folded JSON tests pass
- No memory growth or crashes during sequential execution

---

### Phase 5: 43-Example Regression via Oracle Interface [COMPLETED]

**Goal**: Verify all 43 active examples produce identical SAT/UNSAT through the oracle's `find_countermodel()` as through the direct pipeline. This is the primary gate criterion.

**Tasks**:
- [ ] Add `TestOracleExampleRegression` class to `test_oracle_provider.py`:
  - [ ] Create helper function `example_to_oracle_format(premises, conclusions, settings)` that:
    - Runs the example through the standard pipeline (Syntax + ModelConstraints + BimodalStructure) to determine baseline SAT/UNSAT
    - For oracle testing: converts the conclusion formula(s) to JSON format for oracle input (using the oracle pipeline: conclusion as infix -> oracle checks invalidity)
  - [ ] Note: The oracle tests invalidity of a single formula (no premises). The existing 43 examples use premises+conclusions. The comparison must account for this difference -- we compare the standard pipeline's `check_result()` (which checks premises true + conclusions false) against oracle behavior. For examples with no premises, oracle's `find_countermodel(conclusion_json)` should match. For examples with premises, we run both through the standard pipeline and verify the oracle can at minimum produce correct results for the conclusionOnly case.
  - [ ] Alternative approach: run both the standard pipeline and oracle pipeline in parallel on each example's settings, compare `z3_model_status` (SAT/UNSAT)
  - [ ] `test_regression_all_active_examples` -- parametrized test using `regression_examples` from test_boundary_regression (the same 43-example set)
  - [ ] `test_active_example_count` -- verify 43 examples tested
- [ ] Add `TestOracleOutputCompleteness` class:
  - [ ] `test_all_sat_results_have_complete_output` -- for all SAT examples, verify output has all required keys
  - [ ] `test_temporal_depth_in_output` -- verify temporal_depth is non-negative int
  - [ ] `test_boundary_safe_consistency` -- verify boundary_safe == (M > depth + 1) for all results
  - [ ] `test_world_histories_nonempty` -- verify at least one world in SAT results
  - [ ] `test_task_relation_nonempty` -- verify at least nullity triples in SAT results
- [ ] Run full test suite to confirm no regressions

**Timing**: 1 hour

**Depends on**: 4

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_oracle_provider.py` - add regression tests

**Verification**:
- `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/unit/test_oracle_provider.py -v` -- all tests pass
- `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/ -v` -- full bimodal test suite passes, no regressions
- Gate criteria met: 100 sequential calls, 43 examples correct, formula_folded_json present

## Testing & Validation

- [ ] All tests in `test_oracle_provider.py` pass
- [ ] Provider properties match specification (provider_id, version, frame classes, capabilities)
- [ ] `find_countermodel()` returns correctly shaped dict for SAT and None for UNSAT
- [ ] `formula_folded_json` present and valid in all non-None outputs
- [ ] 100 sequential calls complete without state leakage
- [ ] 43 active examples produce correct SAT/UNSAT through oracle interface
- [ ] `validate_self()` works with known-invalid formulas
- [ ] Full bimodal test suite passes with no regressions
- [ ] `Z3OracleProvider` importable from `bimodal_logic`

## Artifacts & Outputs

- `specs/103_oracle_provider_implementation/plans/01_oracle-provider-plan.md` (this file)
- `code/src/bimodal_logic/provider.py` -- full Z3OracleProvider implementation
- `code/src/bimodal_logic/serialization.py` -- countermodel serialization helpers
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_oracle_provider.py` -- comprehensive test suite

## Rollback/Contingency

The provider.py stub and empty serialization.py are preserved in git. If implementation fails:
1. Revert provider.py to the stub (class with only `supported_frame_classes`)
2. Revert serialization.py to the empty stub
3. Delete test_oracle_provider.py (new file, no pre-existing content)
4. No other files are modified by this task, so rollback is clean
