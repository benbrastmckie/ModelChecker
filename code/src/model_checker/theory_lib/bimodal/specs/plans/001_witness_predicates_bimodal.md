# Bimodal Witness Predicates Implementation Plan

## Metadata
- **Date**: 2025-10-01
- **Feature**: Witness predicates for world_histories in bimodal theory
- **Scope**: Replace direct quantification over world IDs with witness predicate strategy
- **Estimated Phases**: 6
- **Standards File**: `/home/benjamin/Documents/Philosophy/Projects/ModelChecker/CLAUDE.md`
- **Research Reports**: None (based on exclusion theory patterns)
- **Complexity**: High - Complex Z3 integration with intensional semantics

## Overview

Implement witness predicate strategy for world_histories in bimodal theory, adapting the exclusion theory's witness pattern while respecting architectural differences between hyperintensional (exclusion) and intensional (bimodal) semantics.

**Core Challenge**: Bimodal theory quantifies over world IDs (representing temporal histories), while exclusion quantifies over states. This requires adapting the witness function signatures and constraints to handle the intensional temporal dimension.

**Key Architectural Decisions**:
1. **Witness Function Signatures** (different from exclusion):
<!-- NOTE: although the exclusion theory required both h and y witnesses, this was due to the complexity of it semantics for negation. the bimodal theory has a simple and natural theory of negation, so no such complexities are here required. Instead, we need witnesses just for world_histories, nothing else. And so witnesses will appear in the semantics for the modal operators, but nothing else. So we don't need both h and y witnesses, and it would be better to use a different naming convention altogether. -->
   - `h: WorldID × Time → WorldState` - witness state at a time point
   - `y: WorldID → WorldID` - witness world
2. **Primary Use Case**: Negation operator (replaces existential quantification)
3. **Secondary Use Case**: Modal operators Box/Diamond (may benefit from witnesses)
4. **Preserved Elements**: Temporal operators (Future/Past use z3_helpers), array-based world histories, time quantification
<!-- NOTE: it would make sense to define ForAllTime and ExistsTime which quantify specifically over the times which have been defined which are integers (not states) -->

## Success Criteria
- [ ] Witness registry manages predicate lifecycle for bimodal formulas
- [ ] Constraint generator adapts three-condition semantics to intensional context
- [ ] Model wrapper exposes witness values for post-solving queries
- [ ] Negation operator uses witnesses instead of direct world ID quantification
- [ ] All existing bimodal tests pass (regression prevention)
- [ ] New witness-specific tests achieve >85% coverage
- [ ] Modal operators integration evaluated (optional optimization)

## Technical Design

### Architecture Overview

```
bimodal/
├── semantic/
│   ├── __init__.py              # May need witness registry exposure
│   ├── witness_registry.py      # NEW: Centralized witness management
│   ├── witness_constraints.py   # NEW: Constraint generation
│   └── witness_model.py         # NEW: Post-solving witness queries
├── semantic.py                   # MODIFY: Integrate witness semantics
├── operators.py                  # MODIFY: Negation uses witnesses
└── tests/
    └── unit/
        ├── test_witness_registry.py      # NEW
        ├── test_witness_constraints.py   # NEW
        ├── test_witness_model.py         # NEW
        └── test_negation_witnesses.py    # NEW
```

### Witness Function Design

**Exclusion Pattern** (hyperintensional):
```python
h_pred = z3.Function("formula_h", BitVecSort(N), BitVecSort(N))
y_pred = z3.Function("formula_y", BitVecSort(N), BitVecSort(N))
```

**Bimodal Adaptation** (intensional with time):
```python
# h: WorldID × Time → WorldState
h_pred = z3.Function(
    f"{formula_str}_h",
    z3.IntSort(),           # WorldID input
    z3.IntSort(),           # Time input
    z3.BitVecSort(N)        # WorldState output
)

# y: WorldID → WorldID
y_pred = z3.Function(
    f"{formula_str}_y",
    z3.IntSort(),           # WorldID input
    z3.IntSort()            # WorldID output
)
```

### Integration with Negation Operator

**Current Implementation** (lines 392-428 in operators.py):
```python
def false_at(self, argument, eval_point):
    semantics = self.semantics
    eval_time = eval_point["time"]

    other_world = z3.Int('nec_true_world')
    return z3.Exists(
        other_world,
        z3.And(
            semantics.is_world(other_world),
            semantics.is_valid_time_for_world(other_world, eval_time),
            semantics.false_at(argument, {"world": other_world, "time": eval_time})
        )
    )
```

**Witness-Based Implementation**:
```python
def false_at(self, argument, eval_point):
    semantics = self.semantics
    eval_time = eval_point["time"]

    # Get witness predicates
    formula_str = self._get_formula_string(argument)
    h_pred, y_pred = semantics.witness_registry.get_witness_predicates(formula_str)

    # Use witness instead of existential quantification
    witness_world = y_pred(eval_point["world"])
    witness_state = h_pred(witness_world, eval_time)

    return z3.And(
        semantics.is_world(witness_world),
        semantics.is_valid_time_for_world(witness_world, eval_time),
        semantics.false_at(argument, {"world": witness_world, "time": eval_time})
    )
```

### Constraint Generation Pattern

Adapt exclusion's three-condition semantics to intensional context:

**Exclusion Conditions** (hyperintensional):
1. For all verifiers of argument, h and y satisfy requirements
2. All h values are part of verifying state
3. Minimality constraint

**Bimodal Adaptation** (intensional):
1. For all world_ids verifying argument at eval_time, h and y satisfy requirements
2. All h witness states are valid at witness times
3. Minimality constraint (witness world is minimal)

## Implementation Phases

### Phase 1: Type Safety Foundation - Witness Registry
**Objective**: Create centralized witness predicate registry adapted for bimodal signatures
**Complexity**: Medium

**Context**: Adapt exclusion's `WitnessRegistry` (lines 18-126 in exclusion/semantic/registry.py) to bimodal's intensional function signatures. Registry must manage lifecycle of witness predicates with correct Z3 function types.

Tasks:
- [ ] Create `/home/benjamin/Documents/Philosophy/Projects/ModelChecker/code/src/model_checker/theory_lib/bimodal/semantic/` subdirectory
- [ ] Create `witness_registry.py` with `WitnessRegistry` class
  - [ ] `__init__(self, N: int, M: int)` - Store BitVec size and time bound
  - [ ] `register_witness_predicates(formula_str: str) -> Tuple[z3.FuncDeclRef, z3.FuncDeclRef]`
    - Create `h: WorldID × Time → WorldState` function
    - Create `y: WorldID → WorldID` function
    - Store in `self.predicates` dict with keys `{formula_str}_h`, `{formula_str}_y`
    - Add formula mapping to `self.formula_mapping`
    - Cache in `self._predicate_cache` for performance
    - Raise `WitnessRegistryError` if already registered
  - [ ] `get_witness_predicates(formula_str: str) -> Tuple[z3.FuncDeclRef, z3.FuncDeclRef]`
    - Check cache first (fast path)
    - Validate formula exists
    - Raise `WitnessPredicateError` if not registered
  - [ ] `get_all_predicates() -> Dict[str, z3.FuncDeclRef]` - Return copy of predicates
  - [ ] `clear() -> None` - Clear all registries and caches
- [ ] Create error classes in `/home/benjamin/Documents/Philosophy/Projects/ModelChecker/code/src/model_checker/theory_lib/errors.py` if not exist:
  - [ ] `BimodalWitnessRegistryError`
  - [ ] `BimodalWitnessPredicateError`

Testing:
```bash
# TDD: Write tests BEFORE implementation
PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/unit/test_witness_registry.py -v
```

**Test Requirements**:
- [ ] `test_initialization` - Verify N, M stored, dicts empty
- [ ] `test_register_witness_predicates` - Check h/y signatures, storage, mapping
- [ ] `test_register_multiple_formulas` - Multiple registrations work independently
- [ ] `test_register_same_formula_twice` - Raises `BimodalWitnessRegistryError`
- [ ] `test_predicate_function_signatures` - h has (Int, Int, BitVec(N)), y has (Int, Int)
- [ ] `test_get_witness_predicates` - Retrieval works, cache hit on second call
- [ ] `test_get_witness_predicates_not_registered` - Raises `BimodalWitnessPredicateError`
- [ ] `test_clear` - All dicts and cache cleared
- [ ] `test_cache_performance` - Second get_witness_predicates faster than first

**Validation**:
- All tests pass with >90% coverage
- Function signatures match bimodal architecture (h: WorldID×Time→WorldState, y: WorldID→WorldID)
- Error handling follows fail-fast philosophy

---

### Phase 2: Constraint Generation - Intensional Adaptation
**Objective**: Generate Z3 constraints defining witness predicates in intensional temporal context
**Complexity**: High

**Context**: Adapt exclusion's `WitnessConstraintGenerator` (lines 19-175 in exclusion/semantic/constraints.py) to bimodal's intensional semantics. Key difference: constraints must handle temporal dimension and world histories instead of atomic states.

Tasks:
- [ ] Create `witness_constraints.py` with `WitnessConstraintGenerator` class
  - [ ] `__init__(self, semantics)` - Store reference to BimodalSemantics
  - [ ] `generate_witness_constraints(formula_str, formula_ast, h_pred, y_pred, eval_point) -> List[z3.BoolRef]`
    - Validate inputs (formula_str non-empty, predicates non-None)
    - Iterate over potential witness worlds (not states like exclusion)
    - Generate constraints for each world that could witness negation
    - Return list of Z3 constraints
    - Raise `BimodalWitnessConstraintError` on failure
  - [ ] `_could_witness_negation(world_id: int, formula_ast, eval_point) -> bool`
    - Heuristic: consider all worlds as potential witnesses initially
    - Could optimize based on formula structure (future optimization)
  - [ ] `_witness_constraints_for_world(world_id, formula_ast, h_pred, y_pred, eval_point) -> List[z3.BoolRef]`
    - Condition 1: Witness world makes argument true at eval_time
    - Condition 2: Witness state h(witness_world, eval_time) is valid
    - Condition 3: Minimality (witness world is minimal satisfier)
    - Return ForAll implications defining witness behavior
  - [ ] `_minimality_constraint(world_id, argument, h_pred, y_pred, eval_point) -> z3.BoolRef`
    - Ensure no smaller world_id satisfies witness conditions
    - Adapt exclusion's part-of relation to world validity
- [ ] Add error class `BimodalWitnessConstraintError` to errors.py

Testing:
```bash
# TDD: Write tests BEFORE implementation
PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/unit/test_witness_constraints.py -v
```

**Test Requirements**:
- [ ] `test_initialization` - Semantics stored, N/M accessible
- [ ] `test_generate_witness_constraints_simple_formula` - Basic constraint structure
- [ ] `test_generate_witness_constraints_complex_formula` - Nested operators
- [ ] `test_constraint_structure_forall` - ForAll quantifiers present
- [ ] `test_constraint_implies_structure` - Implications structured correctly
- [ ] `test_temporal_dimension_in_constraints` - Time parameter in h_pred calls
- [ ] `test_world_validity_checked` - is_world() and is_valid_time_for_world() used
- [ ] `test_minimality_constraint_structure` - Minimality condition correct
- [ ] `test_empty_formula_string_raises_error` - Validation works
- [ ] `test_invalid_predicates_raise_error` - None predicates rejected

**Validation**:
- All tests pass with >85% coverage
- Constraints reference temporal dimension (h_pred takes time argument)
- Constraints use bimodal's is_world() and is_valid_time_for_world()
- ForAll structure matches intensional semantics pattern

---

### Phase 3: Model Wrapper - Post-Solving Witness Queries
**Objective**: Wrap Z3 model to expose witness values for debugging and analysis
**Complexity**: Medium

**Context**: Adapt exclusion's `WitnessAwareModel` (lines 18-79 in exclusion/semantic/model.py) to bimodal context. Key difference: witness queries must handle world IDs and time parameters, not just states.

Tasks:
- [ ] Create `witness_model.py` with `WitnessAwareModel` class
  - [ ] `__init__(self, z3_model, semantics, witness_predicates)` - Store references
  - [ ] `eval(self, expr) -> z3.ExprRef` - Standard Z3 model evaluation
  - [ ] `has_witness_for(self, formula_str: str) -> bool` - Check if witnesses exist
  - [ ] `get_h_witness(self, formula_str: str, world_id: int, time: int) -> Optional[int]`
    - Query h_pred(world_id, time) from model
    - Return BitVec value as integer (world state)
    - Return None if predicate doesn't exist or evaluation fails
  - [ ] `get_y_witness(self, formula_str: str, world_id: int) -> Optional[int]`
    - Query y_pred(world_id) from model
    - Return witness world ID as integer
    - Return None if predicate doesn't exist
  - [ ] `get_all_witness_values(self, formula_str: str) -> Dict[Tuple[int, int], Tuple[int, int]]`
    - Iterate over all world_ids and times in model
    - Return dict mapping (world_id, time) to (h_value, y_value)
    - Useful for debugging and visualization
- [ ] Add cache mechanism `self._cache` for repeated queries

Testing:
```bash
# TDD: Write tests BEFORE implementation
PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/unit/test_witness_model.py -v
```

**Test Requirements**:
- [ ] `test_initialization` - Z3 model, semantics, predicates stored
- [ ] `test_eval_delegates_to_z3_model` - eval() calls underlying model
- [ ] `test_has_witness_for_existing_formula` - Returns True when registered
- [ ] `test_has_witness_for_nonexistent_formula` - Returns False gracefully
- [ ] `test_get_h_witness_valid_query` - Returns correct witness state
- [ ] `test_get_h_witness_with_time_parameter` - Time dimension handled
- [ ] `test_get_y_witness_valid_query` - Returns correct witness world ID
- [ ] `test_get_witness_nonexistent_formula` - Returns None (not error)
- [ ] `test_get_all_witness_values` - Dict structure correct
- [ ] `test_cache_improves_performance` - Repeated queries use cache

**Validation**:
- All tests pass with >85% coverage
- get_h_witness() accepts time parameter (bimodal-specific)
- get_y_witness() returns world ID (not state)
- Cache reduces repeated Z3 model queries

---

### Phase 4: Negation Operator Integration
**Objective**: Replace direct quantification with witness predicates in negation operator
**Complexity**: High

**Context**: Modify `NegationOperator.false_at()` in `/home/benjamin/Documents/Philosophy/Projects/ModelChecker/code/src/model_checker/theory_lib/bimodal/operators.py` (lines 72-81) and `NecessityOperator.false_at()` (lines 408-428) which use existential quantification.

Tasks:
- [ ] Update `BimodalSemantics.__init__()` in semantic.py to initialize witness components:
  - [ ] Add `self.witness_registry = WitnessRegistry(self.N, self.M)`
  - [ ] Add `self.constraint_generator = WitnessConstraintGenerator(self)`
  - [ ] Import witness modules at top of semantic.py
- [ ] Update `BimodalSemantics.build_frame_constraints()` to include witness constraints:
  - [ ] Register witness predicates for formulas during sentence processing
  - [ ] Add witness constraints to frame_constraints list
  - [ ] Ensure witnesses defined before any quantification over world IDs
- [ ] Create helper in BimodalSemantics: `_get_formula_string(self, formula_ast) -> str`
  - Convert formula AST to unique string identifier
  - Handle nested operators recursively
  - Format: "neg(and(p,q))" style
- [ ] Modify `NegationOperator.false_at()`:
  - [ ] Check if witness predicates available for argument
  - [ ] If available: use witness_world = y_pred(eval_world)
  - [ ] If not: fall back to direct quantification (temporary compatibility)
  - [ ] Replace Exists with witness function calls
  - [ ] Keep eval_time parameter in witness state query: h_pred(witness_world, eval_time)
- [ ] Update `NegationOperator.true_at()` if needed (likely symmetrical change)
- [ ] Do NOT modify `FutureOperator` or `PastOperator` (use z3_helpers as intended)

Testing:
```bash
# TDD: Write tests BEFORE implementation
PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/unit/test_negation_witnesses.py -v
```

**Test Requirements**:
- [ ] `test_witness_registry_initialized` - BimodalSemantics has witness_registry
- [ ] `test_constraint_generator_initialized` - constraint_generator present
- [ ] `test_negation_uses_witnesses` - false_at() calls witness predicates
- [ ] `test_witness_world_validity_checked` - is_world() called on witness
- [ ] `test_witness_state_at_time` - h_pred gets time parameter
- [ ] `test_negation_satisfiable_with_witnesses` - Simple negation formula SAT
- [ ] `test_double_negation_with_witnesses` - ¬¬p behaves correctly
- [ ] `test_formula_string_conversion` - _get_formula_string() produces unique IDs
- [ ] `test_fallback_to_direct_quantification` - Works without witness registration
- [ ] `test_regression_existing_examples` - All existing bimodal examples pass

**Regression Tests**:
```bash
# Run all existing bimodal tests to ensure no breakage
PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/ -v
```

**Validation**:
- Negation operator no longer uses Exists over world IDs
- Witness predicates correctly query temporal dimension
- All existing bimodal tests pass (regression prevention)
- New negation tests pass with witness strategy

---

### Phase 5: Modal Operator Evaluation (Optional Optimization)
**Objective**: Evaluate whether Box/Diamond operators benefit from witness predicates
**Complexity**: Medium

**Context**: `NecessityOperator` (lines 358-406) and `DefPossibilityOperator` (lines 931-970) currently use ForAll/Exists. Determine if witnesses improve performance without changing semantics.

Tasks:
- [ ] Analyze performance bottleneck in `NecessityOperator.false_at()`:
  - [ ] Run benchmark with current Exists implementation
  - [ ] Record Z3 solving time for modal formulas
- [ ] Prototype witness-based `NecessityOperator.false_at()`:
  - [ ] Register modal witness predicates (if not already done)
  - [ ] Replace Exists with witness function call
  - [ ] Test equivalence with original implementation
- [ ] Run performance comparison:
  - [ ] Same modal formulas with witness vs. quantification
  - [ ] Measure solving time difference
  - [ ] Threshold: >20% improvement justifies integration
- [ ] Decision point:
  - [ ] If performance improved: integrate witnesses
  - [ ] If neutral/worse: document findings and keep quantification
  - [ ] Update Phase 5 tasks based on decision
- [ ] If integrating witnesses:
  - [ ] Modify `NecessityOperator.false_at()` to use witnesses
  - [ ] Modify `DefPossibilityOperator` (defined operator, uses NecessityOperator)
  - [ ] Add tests for modal witness behavior
- [ ] Document decision in implementation notes

Testing (if witnesses integrated):
```bash
# Performance benchmarks
PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/unit/test_modal_witnesses.py -v --benchmark
```

**Test Requirements** (if integrated):
- [ ] `test_box_operator_uses_witnesses` - NecessityOperator calls witness predicates
- [ ] `test_box_semantics_unchanged` - Witness version equivalent to quantification
- [ ] `test_diamond_operator_witnesses` - DefPossibilityOperator inherits behavior
- [ ] `test_modal_performance_improvement` - Benchmark shows improvement

**Validation**:
- Decision documented (integrate or skip)
- If integrated: modal operators use witnesses and tests pass
- If skipped: rationale documented for future reference
- No regression in modal operator behavior

---

### Phase 6: Comprehensive Integration Testing
**Objective**: Verify witness predicates work correctly across all bimodal operators and edge cases
**Complexity**: Medium

**Context**: Ensure witness strategy integrates seamlessly with existing bimodal semantics, particularly temporal operators, modal operators, and conjunction/disjunction.

Tasks:
- [ ] Create integration test suite:
  - [ ] `test_complex_formula_witness_registration` - Nested operators register witnesses
  - [ ] `test_conjunction_with_negation_witnesses` - (p ∧ ¬q) uses witnesses
  - [ ] `test_disjunction_with_negation_witnesses` - (p ∨ ¬q) uses witnesses
  - [ ] `test_conditional_with_negation` - (p → ¬q) uses witnesses
  - [ ] `test_modal_negation_interaction` - □¬p uses witnesses correctly
  - [ ] `test_temporal_operators_unchanged` - Future/Past still use z3_helpers
  - [ ] `test_witness_values_in_model` - WitnessAwareModel exposes correct values
  - [ ] `test_multiple_negations_distinct_witnesses` - ¬p and ¬q have separate witnesses
- [ ] Test edge cases:
  - [ ] `test_negation_at_boundary_time` - Witnesses at start/end of world interval
  - [ ] `test_witness_with_world_uniqueness` - Interacts correctly with world_uniqueness constraint
  - [ ] `test_witness_with_task_restriction` - Task relation preserves witness validity
  - [ ] `test_empty_world_interval` - Graceful handling of edge case
- [ ] Run full bimodal test suite:
  ```bash
  PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/ -v --cov=model_checker.theory_lib.bimodal --cov-report=term-missing
  ```
- [ ] Verify coverage targets:
  - [ ] witness_registry.py: >90%
  - [ ] witness_constraints.py: >85%
  - [ ] witness_model.py: >85%
  - [ ] Overall bimodal: maintain >85%
- [ ] Performance regression check:
  - [ ] Run existing examples with witness strategy
  - [ ] Compare solving times to baseline (before witnesses)
  - [ ] Acceptable: <10% slowdown (small overhead for better Z3 behavior)

**Integration Test Requirements**:
- [ ] Complex formulas register and use witnesses correctly
- [ ] Temporal operators unchanged (Future/Past still work)
- [ ] Modal operators work with or without witnesses (Phase 5 dependent)
- [ ] Multiple negations have independent witness predicates
- [ ] Edge cases handled gracefully (boundary times, empty intervals)

**Validation**:
- All integration tests pass
- Coverage targets met (>85% overall, >90% for registry)
- No regression in existing bimodal functionality
- Performance acceptable (<10% slowdown acceptable)
- Witness strategy ready for production use

---

## Testing Strategy

### Test-Driven Development Compliance
**MANDATORY**: All tests written BEFORE implementation code for each phase.

**TDD Checklist per Phase**:
1. Write failing test (RED)
2. Run test to verify failure
3. Write minimal implementation (GREEN)
4. Run test to verify pass
5. Refactor for quality
6. Repeat for next test

### Test Organization

```
bimodal/tests/unit/
├── test_witness_registry.py      # Phase 1: Registry functionality
├── test_witness_constraints.py   # Phase 2: Constraint generation
├── test_witness_model.py         # Phase 3: Model wrapper
├── test_negation_witnesses.py    # Phase 4: Negation integration
├── test_modal_witnesses.py       # Phase 5: Optional modal integration
└── test_witness_integration.py   # Phase 6: Integration tests
```

### Coverage Requirements
- **Per-module targets**:
  - witness_registry.py: >90% (core type safety)
  - witness_constraints.py: >85% (complex logic)
  - witness_model.py: >85% (query interface)
  - Updated operators.py: maintain >85%
- **Overall bimodal theory**: maintain >85%

### Regression Prevention
Every phase must:
1. Run existing bimodal test suite before changes
2. Verify all tests pass after changes
3. No new test failures introduced
4. Performance within acceptable range (<10% slowdown)

### Test Commands

```bash
# Phase-specific unit tests
PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/unit/test_witness_registry.py -v

# All witness tests
PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/unit/test_witness*.py -v

# Full bimodal suite with coverage
PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/ -v --cov=model_checker.theory_lib.bimodal --cov-report=term-missing

# Integration tests only
PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/integration/ -v

# Regression check (all existing tests)
PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/ -v
```

---

## Documentation Requirements

### Code Documentation
- [ ] Docstrings for all new classes (WitnessRegistry, WitnessConstraintGenerator, WitnessAwareModel)
- [ ] Docstrings for all public methods
- [ ] Type hints for all function signatures
- [ ] Inline comments explaining witness semantics adaptation

### Architecture Documentation
- [ ] Update `/home/benjamin/Documents/Philosophy/Projects/ModelChecker/code/src/model_checker/theory_lib/bimodal/README.md` with witness section
- [ ] Document witness function signatures (h and y)
- [ ] Explain intensional vs. hyperintensional differences
- [ ] Add examples of witness-based negation

### User-Facing Documentation
- [ ] Update `/home/benjamin/Documents/Philosophy/Projects/ModelChecker/docs/architecture/README.md` if architecture changes
- [ ] Note: Do NOT create new .md files unless explicitly requested

---

## Dependencies

### External Dependencies
- **Z3 SMT Solver**: Core dependency (already in project)
- **pytest**: Testing framework (already in project)
- **Python 3.8+**: Type hints support

### Internal Dependencies
- `model_checker.models.semantic.SemanticDefaults`: Base class for BimodalSemantics
- `model_checker.syntactic`: Formula AST structures
- `model_checker.utils`: z3_helpers for temporal quantification
- `model_checker.theory_lib.logos`: Base LogosSemantics (reference, not inheritance for bimodal)

### Cross-Theory Dependencies
- **Exclusion theory witness implementation**: Pattern reference (DO NOT import)
- **Imposition theory**: No witness predicates (different architecture)
- **Logos theory**: Base semantics (bimodal inherits from SemanticDefaults, not LogosSemantics)

---

## Notes

### Key Architectural Differences: Bimodal vs. Exclusion

| Aspect | Exclusion (Hyperintensional) | Bimodal (Intensional) |
|--------|------------------------------|------------------------|
| Quantification | Over states (BitVec) | Over world IDs (Int) |
| Witness h | `h: State → State` | `h: WorldID × Time → WorldState` |
| Witness y | `y: State → State` | `y: WorldID → WorldID` |
| Temporal dimension | None | Essential (time parameter in h) |
| Primary use case | Negation (state exclusion) | Negation (world history witnessing) |
| Base class | LogosSemantics | SemanticDefaults (not LogosSemantics) |

### Critical Implementation Notes

1. **Witness Function Signatures**: Bimodal's `h` takes TWO parameters (world_id, time) unlike exclusion's single parameter. This is non-negotiable due to intensional semantics.

2. **Temporal Preservation**: Future/Past operators already use efficient z3_helpers. Do NOT change them to use witnesses - they quantify over times (bounded integers), not world IDs.

3. **Array-Based World Histories**: Preserve `world_function: WorldID → Array(Time, WorldState)`. Witnesses provide alternative to quantifying over world IDs, not replacing arrays.

4. **Performance Expectations**: Witness predicates may initially slow solving (more functions). If >20% slowdown, revisit constraint structure in Phase 2.

5. **Modal Operator Decision**: Phase 5 is evaluation-dependent. If witnesses don't help Box/Diamond, skip integration (document why).

6. **Error Handling**: Use bimodal-specific error classes (`BimodalWitnessRegistryError`, etc.) to distinguish from exclusion errors.

7. **No Backwards Compatibility**: Clean break from direct quantification. Remove old Exists code when witnesses proven working (no compatibility layer).

### Future Optimization Opportunities

- **Lazy Witness Registration**: Only register witnesses for formulas actually used in model
- **Witness Constraint Caching**: Cache generated constraints for repeated formulas
- **Selective Modal Witnesses**: Use witnesses only for deeply nested modal operators
- **Witness Minimality Relaxation**: Experiment with removing minimality constraint if it causes performance issues

### Testing Priorities

1. **Phase 1 (Registry)**: Highest priority - foundation for all other phases
2. **Phase 2 (Constraints)**: High priority - core logic correctness
3. **Phase 4 (Negation)**: High priority - primary use case
4. **Phase 3 (Model)**: Medium priority - nice-to-have for debugging
5. **Phase 5 (Modal)**: Low priority - optional optimization
6. **Phase 6 (Integration)**: High priority - prevents regressions

### Git Commit Strategy

Follow TDD commit pattern:
1. **Test commit**: "test: add witness registry tests for bimodal theory"
2. **Implementation commit**: "feat: implement witness registry for bimodal theory"
3. **Integration commit**: "feat: integrate witnesses with negation operator"
4. **Documentation commit**: "docs: document witness predicate architecture"

Each phase should have 1-2 commits maximum (test + implementation).

---

## Risk Assessment and Mitigation

### High Risks

**Risk**: Witness constraints cause Z3 performance degradation
- **Likelihood**: Medium
- **Impact**: High (defeats purpose of witnesses)
- **Mitigation**: Phase 2 includes constraint structure validation; Phase 6 has performance benchmarks; abort if >20% slowdown

**Risk**: Intensional adaptation introduces semantic errors
- **Likelihood**: Medium
- **Impact**: Critical (incorrect logic)
- **Mitigation**: Comprehensive test suite; equivalence tests between witness and quantification; formal verification of constraint structure

### Medium Risks

**Risk**: Modal operator witnesses don't improve performance
- **Likelihood**: High
- **Impact**: Low (optional optimization)
- **Mitigation**: Phase 5 explicitly evaluates this; skip integration if no benefit; document findings

**Risk**: Temporal operators accidentally modified
- **Likelihood**: Low
- **Impact**: Medium (breaks efficient time handling)
- **Mitigation**: Explicit note in Phase 4 to NOT modify Future/Past; regression tests will catch changes

### Low Risks

**Risk**: Witness model queries have poor performance
- **Likelihood**: Low
- **Impact**: Low (debugging tool only)
- **Mitigation**: Cache mechanism in Phase 3; only affects post-solving analysis

---

## Success Metrics

- [ ] All 6 phases completed with passing tests
- [ ] >85% test coverage for new witness modules
- [ ] No regression in existing bimodal test suite (100% pass rate maintained)
- [ ] Negation operator successfully uses witnesses (Phase 4)
- [ ] Performance within acceptable range (<10% slowdown on existing examples)
- [ ] Modal operator decision made and documented (Phase 5)
- [ ] Integration tests cover complex formulas and edge cases (Phase 6)
- [ ] Documentation updated with witness architecture

---

## Appendix: Reference Files

### Exclusion Theory Reference (Pattern Source)
- `/home/benjamin/Documents/Philosophy/Projects/ModelChecker/code/src/model_checker/theory_lib/exclusion/semantic/registry.py` - Witness registry pattern
- `/home/benjamin/Documents/Philosophy/Projects/ModelChecker/code/src/model_checker/theory_lib/exclusion/semantic/constraints.py` - Constraint generation pattern
- `/home/benjamin/Documents/Philosophy/Projects/ModelChecker/code/src/model_checker/theory_lib/exclusion/semantic/model.py` - Model wrapper pattern
- `/home/benjamin/Documents/Philosophy/Projects/ModelChecker/code/src/model_checker/theory_lib/exclusion/semantic/core.py` - Integration pattern

### Bimodal Theory Files to Modify
- `/home/benjamin/Documents/Philosophy/Projects/ModelChecker/code/src/model_checker/theory_lib/bimodal/semantic.py` - Lines 1-2370, focus on `__init__` and `build_frame_constraints`
- `/home/benjamin/Documents/Philosophy/Projects/ModelChecker/code/src/model_checker/theory_lib/bimodal/operators.py` - Lines 42-105 (NegationOperator), 358-428 (NecessityOperator)

### Testing Reference
- `/home/benjamin/Documents/Philosophy/Projects/ModelChecker/code/src/model_checker/theory_lib/exclusion/tests/unit/test_witness_registry.py` - Test pattern for registry
- `/home/benjamin/Documents/Philosophy/Projects/ModelChecker/code/docs/core/TESTING.md` - TDD requirements and standards
- `/home/benjamin/Documents/Philosophy/Projects/ModelChecker/CLAUDE.md` - Project standards

---

**Plan Status**: Ready for implementation with `/implement` command
**Estimated Total Effort**: High complexity, 6 phases, comprehensive testing required
**Primary Author**: Claude Code (AI Assistant)
**Review Required**: Yes - especially Phase 2 constraint semantics and Phase 5 performance decision
