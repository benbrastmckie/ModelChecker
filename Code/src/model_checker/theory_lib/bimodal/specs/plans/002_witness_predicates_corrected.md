# Bimodal Witness Predicates Implementation Plan (CORRECTED)

## Metadata
- **Date**: 2025-10-01
- **Feature**: Witness predicates for modal operators and ForAllTime/ExistsTime utilities
- **Scope**: Add witness predicates for Box/Diamond operators and clean time quantification utilities
- **Estimated Phases**: 6 (Phase 5 is optional performance comparison)
- **Standards File**: `/home/benjamin/Documents/Philosophy/Projects/ModelChecker/CLAUDE.md`
- **Research Reports**: Deep Research Phase 2 findings
- **Complexity**: High - Complex Z3 integration with modal semantics
- **Status**: CORRECTED - Supersedes plan 001

## Overview

This plan implements witness predicates for world_histories in bimodal theory's **modal operators only** (Box/Diamond), along with ForAllTime/ExistsTime utilities for clean time quantification.

**CRITICAL CORRECTIONS from Plan 001**:
1. **Witnesses ONLY for modal operators** - Negation has simple complement semantics (no quantification over worlds)
2. **Single witness predicate** - `accessible_world(eval_world, eval_time) → witness_world` (not dual h/y)
3. **ForAllTime/ExistsTime first** - Foundation for temporal operators, simpler starting point
4. **Semantic naming** - `accessible_world` instead of cryptic h/y notation
5. **Modal-specific** - Box/Diamond operators, not negation

**Architecture**:
```
Phase 1: ForAllTime/ExistsTime utilities → BimodalSemantics class
Phase 2: Witness Registry → accessible_world predicate management
Phase 3: Witness Constraints → Modal semantics constraints
Phase 4: Modal Integration → NecessityOperator.false_at() (Approach 1 baseline)
Phase 5: Approach 3 Alternative → Modal duality comparison (optional)
Phase 6: Integration Testing → Complex formulas, regression
```

## Success Criteria
- [ ] ForAllTime/ExistsTime utilities added to BimodalSemantics
- [ ] Temporal operators (Future/Past) use new utilities
- [ ] Witness registry manages accessible_world predicates
- [ ] Modal operators (Box/Diamond) use witness predicates
- [ ] Negation operator unchanged (simple complement semantics preserved)
- [ ] All existing bimodal tests pass (100% regression prevention)
- [ ] New witness-specific tests achieve >85% coverage
- [ ] Performance acceptable (<10% slowdown)

## Technical Design

### Why Witnesses for Modal Operators?

**Current Bottleneck** (operators.py lines 408-428):
```python
def false_at(self, argument, eval_point):
    # Returns true if argument is false in ANY world at eval_time
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

**Problem**: Unbounded quantification over `max_world_id = M * (2^(M*N))` potential worlds causes performance issues.

**Solution**: Replace Exists with witness predicate:
```python
def false_at(self, argument, eval_point):
    # Use witness predicate instead of existential quantification
    formula_str = self.semantics._get_formula_string(argument)
    accessible_world_pred = self.semantics.witness_registry.get_witness_predicate(formula_str)
    witness_world = accessible_world_pred(eval_point["world"], eval_point["time"])

    return z3.And(
        semantics.is_world(witness_world),
        semantics.is_valid_time_for_world(witness_world, eval_time),
        semantics.false_at(argument, {"world": witness_world, "time": eval_time})
    )
```

**For Box.true_at()**: Keep existing `ForAll` quantifier unchanged (simplest, standard pattern). Phase 5 will implement alternative approaches for performance comparison.

*Note: See research report `bimodal/specs/reports/001_box_true_at_approaches.md` for detailed analysis of alternative true_at() implementations to be tested in Phase 5.*

### Why NOT Witnesses for Negation?

**Negation Semantics** (operators.py lines 42-105):
- `true_at(argument, eval_point)` → `semantics.false_at(argument, eval_point)`
- `false_at(argument, eval_point)` → `semantics.true_at(argument, eval_point)`
- **Purely extensional**: Simple truth value inversion
- **No quantification**: No ForAll/Exists over worlds
- **find_truth_condition()**: Swaps true_times and false_times

**Conclusion**: Negation doesn't need witnesses. It's a simple complement operation on extensions.

### ForAllTime/ExistsTime Design

**Current Pattern** (operators.py lines 537-578):
```python
def true_at(self, argument, eval_point):
    future_time = z3.Int('future_true_time')
    return z3.ForAll(
        future_time,
        z3.Implies(
            z3.And(
                semantics.is_valid_time_for_world(eval_world, future_time),
                eval_time < future_time,
            ),
            semantics.true_at(argument, {"world": eval_world, "time": future_time}),
        )
    )
```

**Problem**: Repetitive validity checking, verbose quantification.

**Solution**: Utilities that wrap validity checks:
```python
class BimodalSemantics:
    def ForAllTime(self, world, time_var, body):
        """Quantify over all valid times in world's interval."""
        return z3.ForAll(
            time_var,
            z3.Implies(
                self.is_valid_time_for_world(world, time_var),
                body
            )
        )

    def ExistsTime(self, world, time_var, body):
        """Existential quantification over valid times."""
        return z3.Exists(
            time_var,
            z3.And(
                self.is_valid_time_for_world(world, time_var),
                body
            )
        )
```

**Usage**:
```python
def true_at(self, argument, eval_point):
    future_time = z3.Int('future_true_time')
    return semantics.ForAllTime(
        eval_world,
        future_time,
        z3.Implies(
            eval_time < future_time,
            semantics.true_at(argument, {"world": eval_world, "time": future_time})
        )
    )
```

### Witness Predicate Design

**Single Predicate**:
```python
accessible_world = z3.Function(
    f"{formula_str}_accessible_world",
    z3.IntSort(),  # eval_world
    z3.IntSort(),  # eval_time
    z3.IntSort()   # → witness_world
)
```

**NOT dual h/y** like exclusion (different semantics, different structure).

**Naming Rationale**:
- `accessible_world` - Semantic, modal logic terminology
- NOT `h`/`y` - Cryptic, exclusion-specific notation
- NOT `witness_world` - Too generic, confusing with witness_world variable

### Architecture Overview

```
bimodal/
├── semantic/
│   ├── __init__.py                    # Expose witness registry (NEW)
│   ├── witness_registry.py            # NEW: Single predicate management
│   └── witness_constraints.py         # NEW: Modal semantics constraints
├── semantic.py                         # MODIFY: Add ForAllTime/ExistsTime, integrate witnesses
├── operators.py                        # MODIFY: Modal operators use witnesses, temporal use utilities
└── tests/unit/
    ├── test_witness_registry.py       # NEW
    ├── test_witness_constraints.py    # NEW
    ├── test_modal_witnesses.py        # NEW
    └── test_foralltime.py             # NEW
```

## Implementation Phases

### Phase 1: ForAllTime/ExistsTime Utilities (Foundation)
**Objective**: Add clean time quantification utilities to BimodalSemantics
**Complexity**: Low
**Priority**: HIGHEST - Foundation for all temporal operators

**Context**: Temporal operators (Future/Past) currently use repetitive `is_valid_time_for_world()` checks. Utilities will clean up code and make temporal quantification more maintainable.

**Tasks**:
- [ ] Add `ForAllTime()` method to BimodalSemantics in semantic.py (after line 192):
  ```python
  def ForAllTime(self, world, time_var, body):
      """Universal quantification over all valid times in world's interval.

      Args:
          world: World ID (z3.IntSort)
          time_var: Time variable (z3.IntSort) to quantify over
          body: Z3 expression to evaluate for each time

      Returns:
          z3.ForAll expression with validity implications
      """
      return z3.ForAll(
          time_var,
          z3.Implies(
              self.is_valid_time_for_world(world, time_var),
              body
          )
      )
  ```
- [ ] Add `ExistsTime()` method to BimodalSemantics (after ForAllTime):
  ```python
  def ExistsTime(self, world, time_var, body):
      """Existential quantification over valid times in world's interval.

      Args:
          world: World ID (z3.IntSort)
          time_var: Time variable (z3.IntSort) to quantify over
          body: Z3 expression to evaluate

      Returns:
          z3.Exists expression with validity conjunction
      """
      return z3.Exists(
          time_var,
          z3.And(
              self.is_valid_time_for_world(world, time_var),
              body
          )
      )
  ```
- [x] Update `FutureOperator.true_at()` (operators.py line 529-550) to use ForAllTime:
  - Replace `z3.ForAll(future_time, z3.Implies(z3.And(is_valid_time_for_world(...), ...), ...))`
  - With `semantics.ForAllTime(eval_world, future_time, z3.Implies(eval_time < future_time, ...))`
- [x] Update `FutureOperator.false_at()` (operators.py line 552-578) to use ExistsTime:
  - Replace `z3.Exists(future_time, z3.And(is_valid_time_for_world(...), ..., ...))`
  - With `semantics.ExistsTime(eval_world, future_time, z3.And(eval_time < future_time, ...))`
- [x] Update `PastOperator.true_at()` (operators.py line 682-710) to use ForAllTime
- [x] Update `PastOperator.false_at()` (operators.py line 712-738) to use ExistsTime
- [x] Add docstrings to both utilities explaining usage

**Testing**:
```bash
# TDD: Write tests BEFORE implementation
PYTHONPATH=Code/src pytest Code/src/model_checker/theory_lib/bimodal/tests/unit/test_foralltime.py -v
```

**Test Requirements** (`test_foralltime.py`):
- [x] `test_foralltime_signature` - Method exists, correct signature
- [x] `test_foralltime_wraps_validity` - Generates ForAll with Implies(is_valid_time_for_world, body)
- [x] `test_existstime_signature` - Method exists, correct signature
- [x] `test_existstime_wraps_validity` - Generates Exists with And(is_valid_time_for_world, body)
- [x] `test_foralltime_structure` - z3.ForAll quantifier present
- [x] `test_existstime_structure` - z3.Exists quantifier present
- [x] `test_future_operator_structure_uses_quantifier` - FutureOperator.true_at() produces quantified formula
- [x] `test_future_operator_false_structure_uses_quantifier` - FutureOperator.false_at() produces quantified formula
- [x] `test_past_operator_structure_uses_quantifier` - PastOperator.true_at() produces quantified formula
- [x] `test_past_operator_false_structure_uses_quantifier` - PastOperator.false_at() produces quantified formula

**Regression Tests**:
```bash
# Ensure temporal operators still work
PYTHONPATH=Code/src pytest Code/src/model_checker/theory_lib/bimodal/tests/unit/test_bimodal.py -v -k "future or past or temporal"
```

**Validation**:
- [x] ForAllTime/ExistsTime methods added to BimodalSemantics
- [x] All temporal operators (Future/Past) use new utilities
- [x] All existing temporal tests pass (regression prevention)
- [x] Code cleaner, more maintainable

**Status**: ✅ COMPLETED

---

### Phase 2: Witness Registry for Modal Operators
**Objective**: Create registry managing accessible_world predicates
**Complexity**: Medium
**Priority**: HIGH - Foundation for modal witness strategy

**Context**: Unlike exclusion's dual h/y predicates, bimodal needs single `accessible_world` predicate per formula. Registry manages lifecycle: registration, retrieval, cleanup.

**Tasks**:
- [ ] Create `/home/benjamin/Documents/Philosophy/Projects/ModelChecker/Code/src/model_checker/theory_lib/bimodal/semantic/` subdirectory:
  ```bash
  mkdir -p Code/src/model_checker/theory_lib/bimodal/semantic
  ```
- [ ] Create `__init__.py` in semantic/ subdirectory:
  ```python
  """Bimodal semantic components for witness predicates."""
  from .witness_registry import WitnessRegistry
  from .witness_constraints import WitnessConstraintGenerator

  __all__ = ['WitnessRegistry', 'WitnessConstraintGenerator']
  ```
- [ ] Create `witness_registry.py` with `WitnessRegistry` class:
  - [ ] `__init__(self, N: int, M: int)` - Store BitVec size and time bound
  - [ ] `register_witness_predicate(formula_str: str) -> z3.FuncDeclRef`:
    - Create `accessible_world: (Int, Int) → Int` function
    - Naming: `{formula_str}_accessible_world`
    - Store in `self.predicates` dict
    - Add to `self.formula_mapping`
    - Cache in `self._predicate_cache`
    - Raise `BimodalWitnessRegistryError` if already registered
  - [ ] `get_witness_predicate(formula_str: str) -> z3.FuncDeclRef`:
    - Check cache first (performance)
    - Validate formula exists
    - Raise `BimodalWitnessPredicateError` if not registered
  - [ ] `has_witness_predicate(formula_str: str) -> bool` - Check existence without error
  - [ ] `get_all_predicates() -> Dict[str, z3.FuncDeclRef]` - Return copy
  - [ ] `clear() -> None` - Clear all registries and caches
- [ ] Add error classes to `/home/benjamin/Documents/Philosophy/Projects/ModelChecker/Code/src/model_checker/theory_lib/errors.py`:
  ```python
  class BimodalWitnessRegistryError(Exception):
      """Raised when witness registry operations fail."""
      pass

  class BimodalWitnessPredicateError(Exception):
      """Raised when witness predicate operations fail."""
      pass
  ```

**Testing**:
```bash
# TDD: Write tests BEFORE implementation
PYTHONPATH=Code/src pytest Code/src/model_checker/theory_lib/bimodal/tests/unit/test_witness_registry.py -v
```

**Test Requirements** (`test_witness_registry.py`):
- [ ] `test_initialization` - N, M stored, dicts empty
- [ ] `test_register_witness_predicate` - Single predicate created, correct signature
- [ ] `test_register_predicate_naming` - Name format: `{formula}_accessible_world`
- [ ] `test_register_multiple_formulas` - Independent registrations
- [ ] `test_register_same_formula_twice` - Raises `BimodalWitnessRegistryError`
- [ ] `test_predicate_signature` - (IntSort, IntSort) → IntSort
- [ ] `test_get_witness_predicate` - Retrieval works
- [ ] `test_get_witness_predicate_caching` - Second call uses cache
- [ ] `test_get_witness_predicate_not_registered` - Raises `BimodalWitnessPredicateError`
- [ ] `test_has_witness_predicate_existing` - Returns True
- [ ] `test_has_witness_predicate_nonexistent` - Returns False (no error)
- [ ] `test_get_all_predicates` - Returns copy of dict
- [ ] `test_clear` - All dicts and cache cleared

**Validation**:
- [ ] WitnessRegistry class created with correct API
- [ ] Single predicate per formula (not dual h/y)
- [ ] Semantic naming (`accessible_world`)
- [ ] All tests pass with >90% coverage
- [ ] Error handling follows fail-fast philosophy

---

### Phase 3: Witness Constraints for Modal Semantics
**Objective**: Generate Z3 constraints defining accessible_world behavior
**Complexity**: High
**Priority**: HIGH - Core logic correctness

**Context**: Constraints define what `accessible_world(eval_world, eval_time)` returns. For Box operator: witness must be a world where argument is false. Unlike exclusion's three-condition semantics, this is simpler modal semantics.

**Tasks**:
- [ ] Create `witness_constraints.py` with `WitnessConstraintGenerator` class:
  - [ ] `__init__(self, semantics)` - Store BimodalSemantics reference
  - [ ] `generate_witness_constraints(formula_str, formula_ast, accessible_world_pred) -> List[z3.BoolRef]`:
    - Validate inputs (formula_str non-empty, predicate non-None)
    - Generate ForAll constraints over eval_world and eval_time
    - Define accessible_world behavior: must return valid world
    - Return list of Z3 constraints
    - Raise `BimodalWitnessConstraintError` on failure
  - [ ] `_witness_constraint_for_necessity(formula_ast, accessible_world_pred) -> z3.BoolRef`:
    - Pattern: `ForAll eval_world, eval_time: Implies(conditions, witness_valid)`
    - Condition 1: eval_world is valid world
    - Condition 2: eval_time is valid for eval_world
    - Condition 3: argument is false at some world
    - Then: accessible_world(eval_world, eval_time) must be valid world
    - And: argument is false at accessible_world at eval_time
  - [ ] `_minimality_constraint(accessible_world_pred) -> z3.BoolRef`:
    - Optional: Ensure witness is minimal (smallest world ID satisfying conditions)
    - May be omitted initially for simplicity
- [ ] Add error class `BimodalWitnessConstraintError` to errors.py

**Testing**:
```bash
# TDD: Write tests BEFORE implementation
PYTHONPATH=Code/src pytest Code/src/model_checker/theory_lib/bimodal/tests/unit/test_witness_constraints.py -v
```

**Test Requirements** (`test_witness_constraints.py`):
- [ ] `test_initialization` - Semantics stored, accessible
- [ ] `test_generate_witness_constraints_simple` - Basic constraint structure
- [ ] `test_generate_witness_constraints_complex` - Nested modal operators
- [ ] `test_constraint_structure_forall` - ForAll quantifiers present
- [ ] `test_constraint_implies_structure` - Implications correct
- [ ] `test_witness_returns_valid_world` - is_world() constraint present
- [ ] `test_witness_at_valid_time` - is_valid_time_for_world() constraint
- [ ] `test_argument_false_at_witness` - Falsity condition present
- [ ] `test_empty_formula_string_raises_error` - Validation works
- [ ] `test_invalid_predicate_raises_error` - None predicate rejected
- [ ] `test_constraints_list_structure` - Returns list of z3.BoolRef

**Validation**:
- [ ] WitnessConstraintGenerator created
- [ ] Constraints define accessible_world behavior
- [ ] ForAll structure matches modal semantics
- [ ] All tests pass with >85% coverage
- [ ] Constraints reference is_world(), is_valid_time_for_world()

---

### Phase 4: Modal Operator Integration (Approach 1 - Baseline)
**Objective**: Replace Exists quantification with witness predicates in Box.false_at(), keep ForAll in Box.true_at()
**Complexity**: High
**Priority**: HIGH - Primary use case

**Context**: `NecessityOperator.false_at()` (lines 408-428) uses Exists over world IDs. Replace with witness predicate call. Keep `NecessityOperator.true_at()` (lines 384-406) with ForAll for Phase 1 baseline. `DefPossibilityOperator` inherits behavior through composition (dual of necessity).

**Strategy**: Implement Approach 1 (Keep ForAll) from research report `bimodal/specs/reports/001_box_true_at_approaches.md`. This provides the simplest, lowest-risk baseline for testing witness infrastructure.

**Tasks**:
- [ ] Update `BimodalSemantics.__init__()` in semantic.py (after line 56):
  ```python
  # Initialize witness components
  self.witness_registry = WitnessRegistry(self.N, self.M)
  self.constraint_generator = WitnessConstraintGenerator(self)
  ```
- [ ] Add imports to semantic.py (after line 15):
  ```python
  from .semantic.witness_registry import WitnessRegistry
  from .semantic.witness_constraints import WitnessConstraintGenerator
  ```
- [ ] Create helper in BimodalSemantics: `_get_formula_string(formula_ast) -> str`:
  - Convert formula AST to unique string identifier
  - Handle nested operators recursively
  - Format: `"box(p)"`, `"diamond(and(p,q))"` style
  - Add after `define_primitives()` method
- [ ] Update `BimodalSemantics.build_frame_constraints()` to include witness constraints:
  - After building standard constraints, register witnesses for modal formulas
  - Add witness constraints to frame_constraints list
  - Ensure witnesses defined before using in operators
- [ ] Modify `NecessityOperator.false_at()` in operators.py (lines 408-428):
  - [ ] Get formula string: `formula_str = self.semantics._get_formula_string(argument)`
  - [ ] Check if witness registered: `if self.semantics.witness_registry.has_witness_predicate(formula_str):`
  - [ ] If registered: use witness:
    ```python
    accessible_world_pred = self.semantics.witness_registry.get_witness_predicate(formula_str)
    witness_world = accessible_world_pred(eval_point["world"], eval_time)
    return z3.And(
        semantics.is_world(witness_world),
        semantics.is_valid_time_for_world(witness_world, eval_time),
        semantics.false_at(argument, {"world": witness_world, "time": eval_time})
    )
    ```
  - [ ] If not registered: fall back to Exists (temporary compatibility)
- [ ] Keep `NecessityOperator.true_at()` (lines 384-406) UNCHANGED for Phase 1:
  - Continue using ForAll quantifier (Approach 1 from research report)
  - This establishes baseline for comparison with Approach 3 later
  - Document: "Phase 1 baseline: using ForAll for true_at()"
- [ ] Do NOT modify `NegationOperator` (lines 42-105) - simple semantics, no quantification
- [ ] `DefPossibilityOperator` (lines 931-970) inherits behavior (defined as dual of necessity)

**Testing**:
```bash
# TDD: Write tests BEFORE implementation
PYTHONPATH=Code/src pytest Code/src/model_checker/theory_lib/bimodal/tests/unit/test_modal_witnesses.py -v
```

**Test Requirements** (`test_modal_witnesses.py`):
- [ ] `test_witness_registry_initialized` - BimodalSemantics has witness_registry
- [ ] `test_constraint_generator_initialized` - constraint_generator present
- [ ] `test_formula_string_conversion` - _get_formula_string() produces unique IDs
- [ ] `test_necessity_registers_witness` - Box operator triggers registration
- [ ] `test_necessity_uses_witness` - false_at() calls accessible_world predicate
- [ ] `test_witness_world_validity_checked` - is_world() called on witness
- [ ] `test_witness_time_validity_checked` - is_valid_time_for_world() called
- [ ] `test_box_satisfiable_with_witnesses` - Simple □p formula SAT
- [ ] `test_diamond_inherits_witness` - ◇p uses witnesses through composition
- [ ] `test_box_diamond_interaction` - □◇p uses witnesses correctly
- [ ] `test_fallback_to_exists` - Works without witness registration (temporary)
- [ ] `test_negation_unchanged` - Negation operator still uses simple semantics
- [ ] `test_regression_existing_examples` - All existing bimodal examples pass

**Regression Tests**:
```bash
# Run all existing bimodal tests
PYTHONPATH=Code/src pytest Code/src/model_checker/theory_lib/bimodal/tests/ -v
```

**Validation**:
- [ ] NecessityOperator.false_at() uses witness predicates
- [ ] DefPossibilityOperator inherits correct behavior
- [ ] Negation operator unchanged (regression test confirms)
- [ ] All existing bimodal tests pass
- [ ] New modal tests pass with witness strategy

---

### Phase 5: Approach 3 Implementation and Comparison (Optional)
**Objective**: Implement Approach 3 (Modal Duality) and compare with Approach 1
**Complexity**: Low (implementation) / Medium (comparison)
**Priority**: MEDIUM - Performance optimization

**Context**: After Phase 4 establishes baseline with Approach 1, optionally implement Approach 3 (Modal Duality) where `true_at()` is defined as `z3.Not(false_at())`. Compare performance and correctness.

**Tasks**:
- [ ] Create alternative `true_at()` implementation in NecessityOperator:
  ```python
  def true_at_duality(self, argument, eval_point):
      """Approach 3: Modal duality alternative."""
      return z3.Not(self.false_at(argument, eval_point))
  ```
- [ ] Add feature flag or configuration to switch between approaches:
  - [ ] `USE_MODAL_DUALITY = False` (default: Approach 1)
  - [ ] When True, use `true_at_duality()` instead of `true_at()`
- [ ] Create comparison test suite (`test_modal_approach_comparison.py`):
  - [ ] Test semantic equivalence between approaches
  - [ ] Benchmark solving time for both approaches
  - [ ] Test on varying model sizes (N=2,3,4,5; M=2,3,4)
  - [ ] Test nested modals (□□□p, ◇◇◇p)
  - [ ] Test complex formulas (□(p ∧ q) → ◇(r ∨ s))
- [ ] Document findings:
  - [ ] Which approach performs better in practice?
  - [ ] Performance differences by model size
  - [ ] Recommendation for default approach
- [ ] Decision point:
  - [ ] If Approach 3 clearly better: make it default, keep Approach 1 as fallback
  - [ ] If Approach 1 better: keep as default, document why duality isn't better
  - [ ] If similar: choose simpler (likely Approach 1) or more elegant (Approach 3)

**Testing**:
```bash
# Compare approaches with benchmarks
PYTHONPATH=Code/src pytest Code/src/model_checker/theory_lib/bimodal/tests/unit/test_modal_approach_comparison.py -v --benchmark
```

**Test Requirements**:
- [ ] `test_approach_semantic_equivalence` - Both produce same results
- [ ] `test_approach1_baseline_performance` - Benchmark ForAll approach
- [ ] `test_approach3_duality_performance` - Benchmark duality approach
- [ ] `test_nested_modals_comparison` - Compare on □□□p
- [ ] `test_varying_model_sizes` - Performance across N=2-5, M=2-4
- [ ] `test_complex_formulas_comparison` - Real-world formula performance

**Validation**:
- [ ] Both approaches produce semantically equivalent results
- [ ] Performance characteristics documented
- [ ] Clear recommendation for which approach to use
- [ ] Fallback mechanism works if needed

---

### Phase 6: Comprehensive Integration Testing
**Objective**: Verify witness predicates work correctly across all bimodal operators and edge cases
**Complexity**: Medium
**Priority**: HIGH - Prevents regressions

**Context**: Ensure witness strategy integrates seamlessly with existing bimodal semantics. Test complex formulas, modal-temporal interaction, and edge cases. This phase uses whichever Box operator approach was chosen in Phase 5 (or Approach 1 if Phase 5 skipped).

**Tasks**:
- [ ] Create integration test suite in `test_modal_witnesses.py`:
  - [ ] `test_complex_modal_formula` - □(p ∧ q) uses witnesses
  - [ ] `test_nested_modal_operators` - □◇□p uses witnesses
  - [ ] `test_modal_negation_interaction` - □¬p uses witnesses for Box, not negation
  - [ ] `test_modal_temporal_interaction` - □⏵p uses witnesses + ForAllTime
  - [ ] `test_conjunction_with_box` - (p ∧ □q) uses witnesses for Box only
  - [ ] `test_disjunction_with_diamond` - (p ∨ ◇q) uses witnesses for Diamond
  - [ ] `test_conditional_with_modal` - (p → □q) uses witnesses
  - [ ] `test_multiple_boxes_distinct_witnesses` - □p and □q have separate witnesses
- [ ] Test edge cases:
  - [ ] `test_box_at_boundary_time` - Witnesses at start/end of world interval
  - [ ] `test_witness_with_world_uniqueness` - Interacts correctly with world_uniqueness constraint
  - [ ] `test_witness_with_task_restriction` - Task relation preserves witness validity
  - [ ] `test_empty_world_interval` - Graceful handling
- [ ] Run full bimodal test suite with coverage:
  ```bash
  PYTHONPATH=Code/src pytest Code/src/model_checker/theory_lib/bimodal/tests/ -v --cov=model_checker.theory_lib.bimodal --cov-report=term-missing
  ```
- [ ] Verify coverage targets:
  - [ ] witness_registry.py: >90%
  - [ ] witness_constraints.py: >85%
  - [ ] Overall bimodal: maintain >85%
- [ ] Performance regression check:
  - [ ] Run existing examples with witness strategy
  - [ ] Compare solving times to baseline (before witnesses)
  - [ ] Acceptable: <10% slowdown

**Integration Test Requirements**:
- [ ] Complex modal formulas register and use witnesses correctly
- [ ] Temporal operators use ForAllTime/ExistsTime (not witnesses)
- [ ] Negation unchanged (simple complement)
- [ ] Multiple modal operators have independent witnesses
- [ ] Edge cases handled gracefully

**Validation**:
- [ ] All integration tests pass
- [ ] Coverage targets met (>85% overall, >90% for registry)
- [ ] No regression in existing bimodal functionality
- [ ] Performance acceptable (<10% slowdown)
- [ ] Witness strategy ready for production use

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
├── test_foralltime.py              # Phase 1: Time quantification utilities
├── test_witness_registry.py        # Phase 2: Registry functionality
├── test_witness_constraints.py     # Phase 3: Constraint generation
├── test_modal_witnesses.py         # Phase 4 & 5: Modal integration + integration tests
└── (existing test files unchanged)
```

### Coverage Requirements
- **Per-module targets**:
  - witness_registry.py: >90% (core type safety)
  - witness_constraints.py: >85% (complex logic)
  - Updated semantic.py: maintain >85%
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
# Phase 1: ForAllTime/ExistsTime tests
PYTHONPATH=Code/src pytest Code/src/model_checker/theory_lib/bimodal/tests/unit/test_foralltime.py -v

# Phase 2: Witness registry tests
PYTHONPATH=Code/src pytest Code/src/model_checker/theory_lib/bimodal/tests/unit/test_witness_registry.py -v

# Phase 3: Witness constraints tests
PYTHONPATH=Code/src pytest Code/src/model_checker/theory_lib/bimodal/tests/unit/test_witness_constraints.py -v

# Phase 4 & 5: Modal witnesses tests
PYTHONPATH=Code/src pytest Code/src/model_checker/theory_lib/bimodal/tests/unit/test_modal_witnesses.py -v

# Full bimodal suite with coverage
PYTHONPATH=Code/src pytest Code/src/model_checker/theory_lib/bimodal/tests/ -v --cov=model_checker.theory_lib.bimodal --cov-report=term-missing

# Regression check (all existing tests)
PYTHONPATH=Code/src pytest Code/src/model_checker/theory_lib/bimodal/tests/ -v
```

---

## Documentation Requirements

### Code Documentation
- [ ] Docstrings for ForAllTime/ExistsTime utilities
- [ ] Docstrings for WitnessRegistry class
- [ ] Docstrings for WitnessConstraintGenerator class
- [ ] Type hints for all function signatures
- [ ] Inline comments explaining modal witness semantics

### Architecture Documentation
- [ ] Update `/home/benjamin/Documents/Philosophy/Projects/ModelChecker/Code/src/model_checker/theory_lib/bimodal/README.md` with:
  - ForAllTime/ExistsTime utility section
  - Witness predicate section (modal operators only)
  - Accessible_world function signature
  - Explanation of why negation doesn't use witnesses
- [ ] Document differences from exclusion theory (single vs. dual witnesses)

### User-Facing Documentation
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
- `model_checker.utils`: z3_helpers (ForAll/Exists from utils, not our utilities)

### Cross-Theory Dependencies
- **Exclusion theory witness implementation**: Pattern reference ONLY (DO NOT import)
- **Imposition theory**: No witness predicates (different architecture)
- **Logos theory**: Base semantics reference

---

## Notes

### Key Architectural Decisions: CORRECTED

**Witnesses for Modal Operators ONLY**:
- Box (□): Witness world where argument is false
- Diamond (◇): Inherits through composition (dual of Box)
- NOT for Negation: Simple complement semantics, no quantification

**Single Witness Predicate**:
- `accessible_world(eval_world, eval_time) → witness_world`
- NOT dual h/y (exclusion-specific, different semantics)
- Semantic naming (modal logic terminology)

**ForAllTime/ExistsTime Utilities**:
- Clean up temporal operator code
- Wrap `is_valid_time_for_world()` checks
- NOT related to witnesses (different quantification domain)

### Differences from Exclusion Theory

| Aspect | Exclusion (Hyperintensional) | Bimodal (Corrected) |
|--------|------------------------------|---------------------|
| Witness use case | Negation (state exclusion) | Modal operators (Box/Diamond) |
| Witness count | Dual (h and y) | Single (accessible_world) |
| Witness signature | `h: State → State`, `y: State → State` | `accessible_world: (WorldID, Time) → WorldID` |
| Negation semantics | Complex (hyperintensional) | Simple (complement) |
| Temporal dimension | None | Essential (time parameter) |

### Critical Implementation Notes

1. **Negation Does NOT Need Witnesses**: Purely extensional, simple complement semantics. No quantification over worlds. Do not modify NegationOperator.

2. **Modal Operators Are Target**: NecessityOperator.false_at() currently uses Exists over world IDs. This is the bottleneck. Replace with witness predicate.

3. **ForAllTime/ExistsTime First**: Simpler feature, foundational for temporal operators. Implement Phase 1 before complex witness strategy.

4. **Single Witness Predicate**: Not dual h/y. Different semantics from exclusion. Use semantic naming: `accessible_world`.

5. **Performance Expectations**: Witness predicates may initially slow solving. If >10% slowdown, revisit constraint structure in Phase 3.

6. **Error Handling**: Use bimodal-specific error classes (`BimodalWitnessRegistryError`, etc.).

7. **No Backwards Compatibility**: Clean break from direct quantification. Remove old Exists code when witnesses proven working.

### Future Optimization Opportunities

- **Lazy Witness Registration**: Only register witnesses for formulas actually used
- **Witness Constraint Caching**: Cache generated constraints for repeated formulas
- **Witness Minimality Relaxation**: Experiment with removing minimality if it causes performance issues
- **NecessityOperator.true_at() Witnesses**: Currently uses ForAll, may benefit from witnesses too

### Testing Priorities

1. **Phase 1 (ForAllTime/ExistsTime)**: Highest priority - foundation, simpler
2. **Phase 2 (Registry)**: High priority - foundation for witnesses
3. **Phase 3 (Constraints)**: High priority - core logic correctness
4. **Phase 4 (Modal Integration)**: High priority - primary use case (Approach 1)
5. **Phase 5 (Approach Comparison)**: Medium priority - optional optimization
6. **Phase 6 (Integration)**: High priority - prevents regressions

### Git Commit Strategy

Follow TDD commit pattern:
1. **Test commit**: "test: add ForAllTime/ExistsTime tests for bimodal theory"
2. **Implementation commit**: "feat: implement ForAllTime/ExistsTime utilities"
3. **Test commit**: "test: add witness registry tests for bimodal theory"
4. **Implementation commit**: "feat: implement witness registry for bimodal modal operators"
5. **Integration commit**: "feat: integrate witnesses with Box/Diamond operators"
6. **Documentation commit**: "docs: document witness predicate architecture"

Each phase should have 1-2 commits maximum (test + implementation).

---

## Risk Assessment and Mitigation

### High Risks

**Risk**: Witness constraints cause Z3 performance degradation
- **Likelihood**: Medium
- **Impact**: High (defeats purpose of witnesses)
- **Mitigation**: Phase 3 includes constraint structure validation; Phase 5 has performance benchmarks; abort if >10% slowdown

**Risk**: Modal semantics adaptation introduces errors
- **Likelihood**: Medium
- **Impact**: Critical (incorrect logic)
- **Mitigation**: Comprehensive test suite; equivalence tests between witness and Exists; formal verification of constraint structure

### Medium Risks

**Risk**: ForAllTime/ExistsTime introduce bugs in temporal operators
- **Likelihood**: Low
- **Impact**: Medium (breaks temporal logic)
- **Mitigation**: Phase 1 has thorough regression tests; simple wrapper implementation; existing tests will catch changes

**Risk**: Confusion between witnesses and temporal utilities
- **Likelihood**: Low
- **Impact**: Low (documentation issue)
- **Mitigation**: Clear separation in docs; different naming conventions; different purposes explained

### Low Risks

**Risk**: Witness registration overhead
- **Likelihood**: Low
- **Impact**: Low (caching mitigates)
- **Mitigation**: Cache mechanism in Phase 2; registration happens once per formula

---

## Success Metrics

- [ ] All phases completed with passing tests (Phase 5 optional)
- [ ] ForAllTime/ExistsTime utilities added and used by temporal operators
- [ ] >90% test coverage for witness registry
- [ ] >85% test coverage for witness constraints
- [ ] No regression in existing bimodal test suite (100% pass rate maintained)
- [ ] Modal operators (Box/Diamond) successfully use witnesses (Phase 4)
- [ ] Box operator true_at() approach chosen and documented (Phase 5 if done, else Approach 1)
- [ ] Negation operator unchanged (confirmed by regression tests)
- [ ] Performance within acceptable range (<10% slowdown on existing examples)
- [ ] Integration tests cover complex formulas and edge cases (Phase 6)
- [ ] Documentation updated with witness architecture and utilities

---

## Appendix A: Research Reports

### Box Operator true_at() Approaches Analysis
- **Location**: `/home/benjamin/Documents/Philosophy/Projects/ModelChecker/Code/src/model_checker/theory_lib/bimodal/specs/reports/001_box_true_at_approaches.md`
- **Content**: Comprehensive analysis of 5 different approaches for implementing Box operator `true_at()` with witnesses
- **Recommendations**:
  - Phase 1: Approach 1 (Keep ForAll) - Simplest, lowest risk baseline
  - Phase 2: Approach 3 (Modal Duality) - Alternative for performance comparison
  - Rejected: Approaches 2, 5 (high complexity, unclear benefits)
  - Future: Approach 4 (Hybrid) if profiling shows need

## Appendix B: Reference Files

### Bimodal Theory Files to Modify
- `/home/benjamin/Documents/Philosophy/Projects/ModelChecker/Code/src/model_checker/theory_lib/bimodal/semantic.py` - Lines 1-2370
  - Add ForAllTime/ExistsTime utilities (after line 192)
  - Initialize witness components in __init__ (after line 56)
  - Add _get_formula_string helper
  - Update build_frame_constraints to include witness constraints
- `/home/benjamin/Documents/Philosophy/Projects/ModelChecker/Code/src/model_checker/theory_lib/bimodal/operators.py`
  - Update FutureOperator (lines 503-653) to use ForAllTime/ExistsTime
  - Update PastOperator (lines 655-820) to use ForAllTime/ExistsTime
  - Modify NecessityOperator.false_at() (lines 408-428) to use witnesses
  - Do NOT modify NegationOperator (lines 42-105)

### Bimodal Theory Files to Create
- `/home/benjamin/Documents/Philosophy/Projects/ModelChecker/Code/src/model_checker/theory_lib/bimodal/semantic/` - NEW subdirectory
- `/home/benjamin/Documents/Philosophy/Projects/ModelChecker/Code/src/model_checker/theory_lib/bimodal/semantic/__init__.py` - NEW
- `/home/benjamin/Documents/Philosophy/Projects/ModelChecker/Code/src/model_checker/theory_lib/bimodal/semantic/witness_registry.py` - NEW
- `/home/benjamin/Documents/Philosophy/Projects/ModelChecker/Code/src/model_checker/theory_lib/bimodal/semantic/witness_constraints.py` - NEW

### Testing Files to Create
- `/home/benjamin/Documents/Philosophy/Projects/ModelChecker/Code/src/model_checker/theory_lib/bimodal/tests/unit/test_foralltime.py` - NEW
- `/home/benjamin/Documents/Philosophy/Projects/ModelChecker/Code/src/model_checker/theory_lib/bimodal/tests/unit/test_witness_registry.py` - NEW
- `/home/benjamin/Documents/Philosophy/Projects/ModelChecker/Code/src/model_checker/theory_lib/bimodal/tests/unit/test_witness_constraints.py` - NEW
- `/home/benjamin/Documents/Philosophy/Projects/ModelChecker/Code/src/model_checker/theory_lib/bimodal/tests/unit/test_modal_witnesses.py` - NEW

### Exclusion Theory Reference (Pattern Source - DO NOT IMPORT)
- `/home/benjamin/Documents/Philosophy/Projects/ModelChecker/Code/src/model_checker/theory_lib/exclusion/semantic/registry.py` - Witness registry pattern (NOTE: dual predicates, different signatures)
- `/home/benjamin/Documents/Philosophy/Projects/ModelChecker/Code/src/model_checker/theory_lib/exclusion/semantic/constraints.py` - Constraint generation pattern

### Project Standards
- `/home/benjamin/Documents/Philosophy/Projects/ModelChecker/CLAUDE.md` - Project standards
- `/home/benjamin/Documents/Philosophy/Projects/ModelChecker/Code/docs/core/TESTING.md` - TDD requirements

---

**Plan Status**: Ready for implementation with `/implement` command
**Estimated Total Effort**: High complexity, 5 phases, comprehensive testing required
**Primary Correction**: Witnesses for modal operators ONLY, single accessible_world predicate
**Primary Author**: Claude Code (AI Assistant)
**Review Required**: Yes - especially Phase 3 constraint semantics and modal operator integration
