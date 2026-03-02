# Complete Witness Predicate Implementation with Fail-Fast Error Handling

## Metadata
- **Date**: 2025-10-01
- **Feature**: Complete witness predicate implementation following fail-fast standards (no fallbacks)
- **Scope**: Fix incomplete witness registration, remove fallback code, implement proper error handling
- **Estimated Phases**: 4
- **Standards File**: `/home/benjamin/Documents/Philosophy/Projects/ModelChecker/code/docs/core/CODE_STANDARDS.md`
- **Research Reports**: `/home/benjamin/Documents/Philosophy/Projects/ModelChecker/specs/reports/bimodal/001_debug_missing_countermodels.md`
- **Related Plan**: `002_witness_predicates_corrected.md` (Phases 1-4 completed with fallback code)
- **Status**: REVISED with explicit implementation details from exclusion architecture analysis
- **Complexity**: High - Requires architectural changes matching exclusion pattern

## Overview

Plan 002 successfully implemented witness predicate **infrastructure** (Phases 1-4), but left the implementation incomplete with fallback code that violates project standards. This plan completes the implementation properly by following the proven exclusion theory architecture pattern.

### Current State

**What Works**:
- ✅ Phase 1-3: WitnessRegistry and WitnessConstraintGenerator classes exist and are correct
- ✅ Phase 4 Part 1: BimodalSemantics initializes witness components (`__init__` lines 67-68)
- ✅ Helper method `_get_formula_string()` exists (semantic.py:241-270)
- ✅ NecessityOperator has witness predicate usage code (operators.py:423-435)

**What's Broken**:
- ❌ **Missing Registration Phase**: Witness predicates are NEVER registered (no `_register_witness_predicates_recursive()`)
- ❌ **Missing Constraint Injection**: Witness constraints never added to solver (no `_generate_all_witness_constraints()`)
- ❌ **Standards Violation**: NecessityOperator.false_at() uses fallback pattern (lines 422-449)
- ❌ **Bug**: BM_CM_1, BM_CM_2, BM_CM_3 fail to find countermodels (UNSAT with zero constraints)

### Root Cause Analysis

**Architectural Gap**: Bimodal is missing the **two-phase witness architecture** that exclusion uses:

```
EXCLUSION (WORKING):                  BIMODAL (BROKEN):
------------------                    -----------------
1. build_model()                      1. __init__()
2.   solver = z3.Solver()            2.   witness_registry = WitnessRegistry()  ← Empty!
3.   solver.add(frame_constraints)   3.   frame_constraints = build_frame_constraints()
4.   _register_witnesses(formulas)   4.   ← MISSING REGISTRATION PHASE
5.   witness_constraints = generate  5.   ← MISSING CONSTRAINT GENERATION
6.   solver.add(witness_constraints) 6.   ← MISSING CONSTRAINT INJECTION
7.   solver.check()                  7.   (Framework calls solver elsewhere)
```

The framework calls semantic methods but bimodal never registers witnesses or adds their constraints.

### Standards Compliance Issues

**CODE_STANDARDS.md lines 57-72**: Fail-fast philosophy - "No silent failures"
- **Current**: `if has_witness: use_witness else: fallback` ← WRONG
- **Required**: `accessible_world_pred = get_witness_predicate(formula_str)` ← Raises error if missing

**TESTING_FRAMEWORK.md**: "Deterministic Behavior: No fallbacks"
- **Current**: Conditional fallback creates non-deterministic behavior
- **Required**: Fail-fast with clear error if witness not registered

## Success Criteria

- [ ] Witness predicates automatically registered for all Box formulas during model building
- [ ] Witness constraints generated and added to Z3 solver
- [ ] NO fallback code - fail-fast with clear errors if witness missing
- [ ] NecessityOperator.false_at() REQUIRES witness predicate (no optional behavior)
- [ ] DefPossibilityOperator inherits correct behavior (it's defined as `¬Box¬`)
- [ ] BM_CM_1, BM_CM_2, BM_CM_3 find countermodels successfully
- [ ] All bimodal tests pass (60+ passing, 21 skipped)
- [ ] UNSAT core shows non-zero constraint counts (proving constraints are valid)

## Technical Design

### Architectural Pattern: Following Exclusion

**Exclusion Theory** (PROVEN WORKING):
```
Location: code/src/model_checker/theory_lib/exclusion/semantic/

WitnessRegistry:
- register_witness_predicates(formula_str) → (h_pred, y_pred)
- BitVec(N) → BitVec(N) signatures

ExclusionSemantics:
- _register_witness_predicates_recursive(formula)  ← Traverses formula tree
- _is_processed(formula) → bool                     ← Prevents re-registration
- _get_witness_predicates(formula_str) → tuple      ← Retrieves from registry
- _generate_all_witness_constraints(eval_point)     ← Creates constraints
- build_model(eval_point):                           ← Orchestrates two-phase flow
    1. solver.add(frame_constraints)
    2. _register_witness_predicates_recursive(premises + conclusions)
    3. witness_constraints = _generate_all_witness_constraints(eval_point)
    4. solver.add(witness_constraints)  ← KEY: Inject constraints here
    5. solver.check()
```

**Bimodal Adaptation**:
```
Location: code/src/model_checker/theory_lib/bimodal/semantic.py

WitnessRegistry:
- register_witness_predicate(formula_str) → accessible_world_pred
- (Int, Int) → Int signature (eval_world, eval_time → witness_world)

BimodalSemantics (NEEDS THESE METHODS):
- _register_witness_predicates_recursive(formula)   ← ADD THIS
- _is_processed(formula) → bool                      ← ADD THIS
- _get_witness_predicate(formula_str) → FuncDeclRef ← ADD THIS
- _generate_all_witness_constraints() → List        ← ADD THIS
- build_model(eval_point):                            ← ADD THIS
    1. solver.add(frame_constraints)
    2. _register_witness_predicates_recursive(premises + conclusions)
    3. witness_constraints = _generate_all_witness_constraints()
    4. solver.add(witness_constraints)
    5. solver.check()
```

### Why Registration Must Happen During Model Building

**Problem**: Can't register during `build_frame_constraints()` because formulas aren't known yet.

**Solution**: Registration happens in `build_model()` after receiving premises/conclusions:

```
Timeline:
1. BimodalSemantics.__init__(settings)     ← Frame constraints built, registry empty
2. Framework calls build_model(eval_point) ← NOW we know premises/conclusions
3. Traverse formulas, register Box witnesses
4. Generate witness constraints
5. Add all constraints to solver
6. solver.check()
```

### Fail-Fast Error Handling

**Remove Conditional Fallback**:
```python
# BEFORE (WRONG - violates standards):
if semantics.witness_registry.has_witness_predicate(formula_str):
    # Use witness
else:
    # Fallback to Exists  ← REMOVE THIS

# AFTER (CORRECT - fail-fast):
accessible_world_pred = semantics.witness_registry.get_witness_predicate(formula_str)
# If witness doesn't exist, registry raises WitnessPredicateError with clear message
```

**Error Messages**:
```python
raise WitnessPredicateError(
    formula_str,
    "retrieval",
    context={'available_formulas': list(self.formula_mapping.keys())},
    suggestion="Register predicate first using register_witness_predicate() during build_model phase"
)
```

## Implementation Phases

### Phase 1: Add State Tracking and Helper Methods [COMPLETED]
**Objective**: Implement formula tracking and witness registration infrastructure
**Complexity**: Medium
**Priority**: CRITICAL
**File**: `code/src/model_checker/theory_lib/bimodal/semantic.py`

#### Tasks

**Task 1.1: Add state tracking fields to `__init__`**
- [x] Add formula tracking fields after line 68:
  ```python
  # Track processed formulas for witness registration (Phase 1)
  self._processed_formulas: Set[str] = set()
  self._formula_ast_mapping: Dict[str, Any] = {}
  ```
- [ ] Add necessary imports at top of file:
  ```python
  from typing import Set, Dict, Any
  ```

**Task 1.2: Implement `_register_witness_predicates_recursive()`**
- [x] Add method after `_get_formula_string()` (after line 270):
  ```python
  def _register_witness_predicates_recursive(self, formula: Any) -> None:
      """
      Recursively register witness predicates for all Box subformulas.

      This method traverses the formula AST and creates accessible_world
      witness predicates for each Box operator encountered.

      Args:
          formula: Sentence object or AST node to process

      Note: Only Box operators get witnesses. Diamond is a defined operator
      (¬Box¬) and will inherit witnesses from its constituent Box.
      """
      # Skip if already processed
      if self._is_processed(formula):
          return

      # Check if this is a Box operator
      if hasattr(formula, 'operator') and formula.operator and formula.operator.name == "\\Box":
          # Register witness predicate for this Box formula
          formula_str = self._get_formula_string(formula)
          self.witness_registry.register_witness_predicate(formula_str)
          self._processed_formulas.add(formula_str)
          self._formula_ast_mapping[formula_str] = formula

      # Recurse on arguments if they exist
      if hasattr(formula, 'arguments') and formula.arguments:
          for arg in formula.arguments:
              self._register_witness_predicates_recursive(arg)
  ```

**Task 1.3: Implement `_is_processed()`**
- [x] Add method after `_register_witness_predicates_recursive()`:
  ```python
  def _is_processed(self, formula: Any) -> bool:
      """Check if formula already has witness predicate registered."""
      try:
          formula_str = self._get_formula_string(formula)
          return formula_str in self._processed_formulas
      except:
          # If we can't get formula string, it's not processed
          return False
  ```

**Task 1.4: Implement `_get_witness_predicate()`**
- [x] Add method after `_is_processed()`:
  ```python
  def _get_witness_predicate(self, formula_str: str) -> z3.FuncDeclRef:
      """
      Get accessible_world witness predicate for a formula.

      Args:
          formula_str: String identifier for the formula

      Returns:
          z3.FuncDeclRef: The accessible_world predicate

      Raises:
          KeyError: If predicate not found in registry (shouldn't happen if registration worked)
      """
      pred_name = f"{formula_str}_accessible_world"
      return self.witness_registry.predicates[pred_name]
  ```

**Task 1.5: Implement `_generate_all_witness_constraints()`**
- [x] Add method after `_get_witness_predicate()`:
  ```python
  def _generate_all_witness_constraints(self) -> List[z3.BoolRef]:
      """
      Generate witness constraints for all registered witness predicates.

      For each Box formula that was registered, this generates constraints
      ensuring the accessible_world witness predicate returns valid worlds.

      Returns:
          List of Z3 constraints defining witness behavior

      Note: These constraints don't specify that the argument is false at
      the witness world - that's handled by the operator's false_at() method.
      These constraints only ensure the witness world itself is valid.
      """
      constraints = []

      for formula_str in self._processed_formulas:
          # Get the formula AST
          formula_ast = self._formula_ast_mapping.get(formula_str)

          # Only generate constraints for Box operators
          if formula_ast and hasattr(formula_ast, 'operator') and formula_ast.operator.name == "\\Box":
              accessible_world_pred = self._get_witness_predicate(formula_str)

              # Generate witness validity constraints
              formula_constraints = self.constraint_generator.generate_witness_constraints(
                  formula_str,
                  formula_ast,
                  accessible_world_pred
              )
              constraints.extend(formula_constraints)

      return constraints
  ```

**Task 1.6: Fix `_get_formula_string()` Z3 boolean cast bug**
- [x] Replace line 254:
  ```python
  # BEFORE (causes Z3Exception):
  if hasattr(formula_ast, 'sentence_letter') and formula_ast.sentence_letter:

  # AFTER (safe check):
  if hasattr(formula_ast, 'sentence_letter') and formula_ast.sentence_letter is not None:
  ```

#### Testing

```bash
# Test state tracking (new tests needed)
PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/unit/ -k "witness" -v

# Test that _get_formula_string doesn't raise Z3Exception
PYTHONPATH=code/src python -c "
from model_checker.theory_lib.bimodal.semantic import BimodalSemantics
sem = BimodalSemantics({'N': 2, 'M': 2, 'contingent': False, 'disjoint': False, 'max_time': 5, 'expectation': True, 'iterate': 1})
# Should not raise exception
"
```

#### Expected Outcomes

- [ ] State tracking fields exist in BimodalSemantics instances
- [ ] `_register_witness_predicates_recursive()` can traverse formula trees
- [ ] `_is_processed()` prevents duplicate registration
- [ ] `_get_witness_predicate()` retrieves registered predicates
- [ ] `_generate_all_witness_constraints()` creates valid Z3 constraints
- [ ] No Z3Exception from `_get_formula_string()`

#### Validation

- [ ] Create BimodalSemantics instance, verify `_processed_formulas` exists
- [ ] Call `_register_witness_predicates_recursive()` on Box(p), verify predicate registered
- [ ] Call `_is_processed()` on same formula, verify returns True
- [ ] Call `_get_witness_predicate()` with formula_str, verify returns Z3 function
- [ ] Call `_generate_all_witness_constraints()`, verify returns List[z3.BoolRef]

---

### Phase 2: Implement build_model() Method
**Objective**: Add two-phase model building following exclusion pattern
**Complexity**: High
**Priority**: CRITICAL
**File**: `code/src/model_checker/theory_lib/bimodal/semantic.py`

#### Context

**Critical Decision**: Where should `build_model()` be called from?

**Investigation needed**: Check `/home/benjamin/Documents/Philosophy/Projects/ModelChecker/code/src/model_checker/iterate/build_example.py` to see how framework integrates with semantic classes.

**Likely patterns**:
1. Framework calls `semantics.build_model(eval_point)` directly
2. Framework uses `ModelConstraints` which we need to bypass for witness injection
3. May need to override framework methods to hook into model building

#### Tasks

**Task 2.1: Research framework integration**
- [ ] Examine how BuildExample calls semantic methods
- [ ] Identify where solver is created and constraints are added
- [ ] Determine if `build_model()` is called or if we need different hook

**Task 2.2: Implement `build_model()` method**
- [ ] Add method after `build_frame_constraints()` (around line 400):
  ```python
  def build_model(self, eval_point: Dict[str, Any]) -> Optional[z3.ModelRef]:
      """
      Build a Z3 model for the given evaluation point using two-phase witness architecture.

      This method follows the exclusion pattern:
      1. Create solver
      2. Add frame constraints
      3. Register witness predicates (traverse formulas)
      4. Generate and add witness constraints
      5. Add premise/conclusion constraints
      6. Check satisfiability

      Args:
          eval_point: Dictionary containing:
              - "world": Int (evaluation world ID)
              - "time": Int (evaluation time)
              - "premises": List[Sentence] (formulas to make true)
              - "conclusions": List[Sentence] (formulas to make false)

      Returns:
          z3.ModelRef if satisfiable, None if unsatisfiable

      Note: This method creates its own solver to inject witness constraints.
      It bypasses the standard ModelConstraints approach to have full control
      over constraint injection order.
      """
      solver = z3.Solver()

      # PHASE 1: Add frame constraints (world structure, validity, etc.)
      for constraint in self.frame_constraints:
          solver.add(constraint)

      # Extract evaluation parameters
      world = eval_point["world"]
      time = eval_point["time"]
      premises = eval_point.get("premises", [])
      conclusions = eval_point.get("conclusions", [])

      # PHASE 2: Register witness predicates
      # First pass: identify all Box formulas and create witness predicates
      all_formulas = premises + conclusions
      for formula in all_formulas:
          self._register_witness_predicates_recursive(formula)

      # PHASE 3: Generate and add witness constraints
      witness_constraints = self._generate_all_witness_constraints()
      for constraint in witness_constraints:
          solver.add(constraint)

      # PHASE 4: Add premise constraints (must be true at eval point)
      for premise in premises:
          premise_constraint = self.true_at(premise, {"world": world, "time": time})
          solver.add(premise_constraint)

      # PHASE 5: Add conclusion constraints (must be false at eval point for countermodel)
      for conclusion in conclusions:
          conclusion_constraint = self.false_at(conclusion, {"world": world, "time": time})
          solver.add(conclusion_constraint)

      # PHASE 6: Check satisfiability
      check_result = solver.check()

      if check_result == z3.sat:
          return solver.model()
      else:
          return None
  ```

**Task 2.3: Integrate with framework (if needed)**
- [ ] If framework doesn't call `build_model()`, override appropriate methods
- [ ] Ensure witness constraint injection happens before solver.check()
- [ ] Test that both frame and witness constraints reach solver

#### Testing

```bash
# Test build_model() creates model with witnesses
PYTHONPATH=code/src python -c "
from model_checker.theory_lib.bimodal.semantic import BimodalSemantics
from model_checker.syntactic.sentence import Sentence

sem = BimodalSemantics({'N': 2, 'M': 2, 'contingent': False, 'disjoint': False, 'max_time': 5, 'expectation': True, 'iterate': 1})

# Parse formulas (you'll need actual parser integration)
# For now, test that method exists and runs
eval_point = {
    'world': 0,
    'time': 0,
    'premises': [],
    'conclusions': []
}

model = sem.build_model(eval_point)
print('build_model() executed successfully')
"
```

#### Expected Outcomes

- [ ] `build_model()` method exists and is callable
- [ ] Creates Z3 solver internally
- [ ] Adds frame constraints to solver
- [ ] Registers witnesses for all Box formulas in premises/conclusions
- [ ] Generates witness constraints
- [ ] Adds witness constraints to solver
- [ ] Returns satisfiable model when appropriate

#### Validation

- [ ] Method signature matches: `build_model(self, eval_point: Dict) -> Optional[z3.ModelRef]`
- [ ] Solver receives both frame and witness constraints
- [ ] Witnesses are registered before constraint generation
- [ ] Method returns None for UNSAT, ModelRef for SAT

---

### Phase 3: Remove Fallback Code and Enforce Fail-Fast
**Objective**: Remove conditional fallback logic, enforce witnesses are required
**Complexity**: Low
**Priority**: CRITICAL
**File**: `code/src/model_checker/theory_lib/bimodal/operators.py`

#### Tasks

**Task 3.1: Add error import**
- [ ] Add to imports at top of file (around line 10):
  ```python
  from ..errors import WitnessPredicateError
  ```

**Task 3.2: Remove fallback from `NecessityOperator.false_at()`**
- [ ] Replace lines 408-449 with:
  ```python
  def false_at(self, argument, eval_point):
      """
      Returns true if argument is false in any possible world at the eval_time.

      Uses witness predicate (accessible_world) which must be registered during
      the build_model phase. Fails fast if witness not registered.

      Args:
          argument: The formula to evaluate
          eval_point: Dict with "world" and "time" keys

      Returns:
          z3.BoolRef: Constraint that is true iff argument is false in some accessible world

      Raises:
          WitnessPredicateError: If witness predicate not registered (indicates bug in build_model)
      """
      semantics = self.semantics

      # Extract world and time from eval_point
      eval_world = eval_point["world"]
      eval_time = eval_point["time"]

      # Get formula string for witness lookup
      formula_str = semantics._get_formula_string(argument)

      # Witness predicate MUST be registered (fail-fast)
      if not semantics.witness_registry.has_witness_predicate(formula_str):
          raise WitnessPredicateError(
              formula_str,
              "evaluation",
              context={
                  'operation': 'NecessityOperator.false_at',
                  'available_formulas': list(semantics.witness_registry.formula_mapping.keys()),
                  'eval_point': str(eval_point)
              },
              suggestion=(
                  "Ensure witness predicates are registered during build_model phase. "
                  "This error indicates _register_witness_predicates_recursive() was not called "
                  "or did not process this formula."
              )
          )

      # Get witness predicate (will raise if missing, but we checked above for better error)
      accessible_world_pred = semantics.witness_registry.get_witness_predicate(formula_str)
      witness_world = accessible_world_pred(eval_world, eval_time)

      # Return constraint using witness
      return z3.And(
          # Witness must be a valid world
          semantics.is_world(witness_world),
          # And eval_time must be valid for witness_world
          semantics.is_valid_time_for_world(witness_world, eval_time),
          # And the argument is false in witness_world at eval_time
          semantics.false_at(argument, {"world": witness_world, "time": eval_time})
      )
  ```

**Task 3.3: Update docstring**
- [ ] Ensure docstring no longer mentions "fallback"
- [ ] Document fail-fast behavior and error conditions

#### Testing

```bash
# Test fail-fast behavior
PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/unit/test_modal_witness_integration.py -v

# Test that unregistered witness raises error
PYTHONPATH=code/src python -c "
from model_checker.theory_lib.bimodal.operators import NecessityOperator
from model_checker.theory_lib.bimodal.semantic import BimodalSemantics
from model_checker.syntactic.sentence import Sentence

sem = BimodalSemantics({'N': 2, 'M': 2, 'contingent': False, 'disjoint': False, 'max_time': 5, 'expectation': True, 'iterate': 1})
op = NecessityOperator(sem)

# This should raise WitnessPredicateError
try:
    result = op.false_at(Sentence('p'), {'world': 0, 'time': 0})
    print('ERROR: Should have raised WitnessPredicateError')
except Exception as e:
    print(f'Correctly raised: {type(e).__name__}')
"
```

#### Expected Outcomes

- [ ] No conditional fallback code remains
- [ ] Attempting to use unregistered witness raises `WitnessPredicateError`
- [ ] Error message includes formula string and helpful context
- [ ] Error suggests checking registration phase

#### Validation

- [ ] `false_at()` with registered witness succeeds
- [ ] `false_at()` with unregistered witness raises `WitnessPredicateError`
- [ ] Error message includes available formulas and suggestion
- [ ] No `if/else` conditional remains checking `has_witness_predicate`

---

### Phase 4: Integration Testing and BM_CM_X Fix Verification
**Objective**: Verify BM_CM_1/2/3 now find countermodels and all tests pass
**Complexity**: Low
**Priority**: CRITICAL
**Files**: All test files and examples

#### Tasks

**Task 4.1: Run unit tests**
- [ ] Run full bimodal test suite:
  ```bash
  PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/unit/ -v --tb=short
  ```
- [ ] Expected: 60+ passing, 21 skipped, 0 failures

**Task 4.2: Run BM_CM examples**
- [ ] Execute all bimodal examples:
  ```bash
  PYTHONPATH=code/src code/dev_cli.py code/src/model_checker/theory_lib/bimodal/examples.py
  ```
- [ ] Verify each BM_CM example finds countermodel:
  - BM_CM_1 (∀Future A ⊬ □A): Should find countermodel
  - BM_CM_2 (∀Past A ⊬ □A): Should find countermodel
  - BM_CM_3 (◇A ⊬ ∃future A): Should find countermodel
  - BM_CM_4 (◇A ⊬ ∃past A): Should find countermodel (already works)

**Task 4.3: Verify UNSAT core analysis**
- [ ] For each example, check that UNSAT core shows non-zero constraints
- [ ] Previously showed "Frame constraints: 0, Model constraints: 0, Premise constraints: 0, Conclusion constraints: 0"
- [ ] After fix, should show actual constraint counts proving they were used

**Task 4.4: Performance regression check**
- [ ] Run examples and measure solve times
- [ ] Compare with baseline (before witness predicates)
- [ ] Acceptable: <10% slowdown (per plan 002 Phase 6)
- [ ] Record timings in test output

**Task 4.5: Update debug report**
- [ ] Add resolution section to `specs/reports/bimodal/001_debug_missing_countermodels.md`
- [ ] Document what was fixed and how
- [ ] Include test results showing success

#### Testing

```bash
# Comprehensive test suite
PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/ -v --cov=model_checker.theory_lib.bimodal.semantic.witness_registry --cov=model_checker.theory_lib.bimodal.semantic.witness_constraints --cov-report=term-missing

# Specific BM_CM countermodel tests
PYTHONPATH=code/src code/dev_cli.py code/src/model_checker/theory_lib/bimodal/examples.py | grep -A 20 "BM_CM"
```

#### Expected Outcomes

- [ ] BM_CM_1: Countermodel found ✓
- [ ] BM_CM_2: Countermodel found ✓
- [ ] BM_CM_3: Countermodel found ✓
- [ ] BM_CM_4: Countermodel found ✓ (regression test)
- [ ] All unit tests pass (60+ passing, 21 skipped)
- [ ] UNSAT cores show non-zero constraint counts
- [ ] Witness constraints appear in solver
- [ ] Performance within acceptable range (<10%)

#### Validation

- [ ] All four BM_CM examples find countermodels symmetrically
- [ ] No test regressions introduced
- [ ] Coverage targets met: witness_registry.py >90%, witness_constraints.py >85%
- [ ] Debug report updated with resolution

---

## Testing Strategy

### Unit Tests

**Existing Tests** (verify still pass):
- `test_modal_witness_integration.py`: Witness component initialization
- `test_witness_registry.py`: Registration and retrieval (20 tests)
- `test_witness_constraints.py`: Constraint generation (13 tests)
- `test_foralltime.py`: ForAllTime/ExistsTime utilities (10 tests)

**New Tests Needed**:
- Test `_register_witness_predicates_recursive()` recursion depth
- Test `_is_processed()` duplicate prevention
- Test `build_model()` witness constraint injection
- Test fail-fast behavior when witness not registered

### Integration Tests

**Examples to Verify**:
- All BM_CM examples (modal operators in conclusions)
- Compare with BM_CM_4 (modal operator in premise) for symmetry
- Complex nested Box formulas: `Box(Box(p))`, `Box(And(p, Box(q)))`

### Coverage Targets

- `witness_registry.py`: >90% (currently 80%, need error handling tests)
- `witness_constraints.py`: >85% (currently 85%, maintain)
- Overall bimodal: maintain >85%

## Dependencies

**External**:
- Z3 SMT solver (already integrated)
- Python typing module (for type hints)

**Internal**:
- BimodalSemantics (semantic.py) - Modified extensively
- NecessityOperator (operators.py) - Fallback removed
- WitnessRegistry (semantic/witness_registry.py) - Used as-is
- WitnessConstraintGenerator (semantic/witness_constraints.py) - Used as-is
- WitnessPredicateError (errors.py) - For fail-fast

**Framework Integration**:
- BuildExample (iterate/build_example.py) - May need investigation
- ModelConstraints (models/constraints.py) - May need bypass

## Notes

### Architectural Decisions

**Why Follow Exclusion Pattern?**
- Proven working architecture (exclusion has 100% passing tests)
- Two-phase approach (register → constrain) is clean and deterministic
- Matches ModelChecker framework expectations

**Why Not Auto-Register in `_get_formula_string()`?**
- Formula evaluation happens during constraint building
- Registration must happen BEFORE constraint building
- Circular dependency if we register during evaluation

**Why Separate `build_model()` Method?**
- Needs control over constraint injection order
- Frame constraints → Witness registration → Witness constraints → Premise/Conclusion constraints
- Bypasses ModelConstraints to inject witness constraints explicitly

### Risk Mitigation

**Risk**: Breaking existing tests that depend on fallback
- **Mitigation**: Phase 4 comprehensive regression testing
- **Likelihood**: Low (fallback was never truly needed, witnesses just weren't registered)
- **Impact**: Medium (tests would fail immediately, easy to detect)

**Risk**: Framework integration issues with `build_model()`
- **Mitigation**: Phase 2 Task 2.1 investigates framework integration first
- **Likelihood**: Medium (unknown how framework calls semantic methods)
- **Impact**: High (could require refactoring framework integration)

**Risk**: Performance regression from witness constraints
- **Mitigation**: Phase 4 performance benchmarking
- **Likelihood**: Low (witness predicates should IMPROVE performance by avoiding unbounded quantification)
- **Impact**: Low (<10% slowdown is acceptable per plan 002)

**Risk**: Edge cases where registration fails
- **Mitigation**: Comprehensive unit tests for recursive registration
- **Likelihood**: Low (pattern proven in exclusion theory)
- **Impact**: Medium (would fail-fast with clear error, easy to debug)

### Edge Cases to Watch

1. **Nested Box Operators**: `Box(Box(p))` - Both levels need witnesses
   - Solution: Recursive traversal handles this correctly

2. **Diamond Operator**: `Diamond(p)` is defined as `¬Box(¬p)`
   - Solution: Only register for `\Box`, Diamond inherits

3. **Box in Negation**: `¬Box(p)`
   - Solution: Recursion traverses through negation, finds Box

4. **Complex Arguments**: `Box(And(p, Box(q)))`
   - Solution: Recursive traversal processes both Box operators

5. **Formula String Uniqueness**: Different AST structures generating same string
   - Current: Uses argument order (correct for AST identity)
   - Future: May need normalization for semantic equivalence

### Future Enhancements (Out of Scope)

From plan 002:
- Phase 5: Implement Approach 3 (Modal Duality: `true_at() = Not(false_at())`)
- Performance comparison between approaches
- Optimization of witness constraint generation
- Minimality constraints for deterministic witness selection

These remain optional performance enhancements, not required for correctness.

---

## Commit Messages

Each phase should be committed separately with descriptive messages:

**Phase 1**:
```
feat(bimodal): add witness predicate registration infrastructure

Implement state tracking and helper methods for witness predicate
registration following exclusion theory pattern.

Changes:
- Add _processed_formulas and _formula_ast_mapping to BimodalSemantics
- Implement _register_witness_predicates_recursive() for Box formula traversal
- Implement _is_processed() to prevent duplicate registration
- Implement _get_witness_predicate() to retrieve registered predicates
- Implement _generate_all_witness_constraints() for constraint generation
- Fix _get_formula_string() Z3 boolean cast bug (line 254)

Infrastructure:
- State tracking prevents re-registration
- Recursive traversal handles nested Box operators
- Constraint generation uses WitnessConstraintGenerator

Testing:
- test_modal_witness_integration.py: Registration tests pass
- No Z3Exception from boolean cast

Standards: Implements fail-fast infrastructure (CODE_STANDARDS.md:57-72)
Ref: Plan 003 Phase 1
```

**Phase 2**:
```
feat(bimodal): implement two-phase witness model building

Add build_model() method following exclusion's two-phase architecture:
1. Add frame constraints
2. Register witness predicates (traverse formulas)
3. Generate witness constraints
4. Add witness constraints to solver
5. Add premise/conclusion constraints
6. Check satisfiability

Changes:
- Implement BimodalSemantics.build_model(eval_point)
- Inject witness constraints into Z3 solver explicitly
- Bypass ModelConstraints for full control over constraint order

Architecture:
- Follows exclusion theory proven pattern
- Frame constraints → Registration → Witness constraints → Evaluation
- Deterministic constraint injection order

Testing:
- build_model() creates models with witness constraints
- Witnesses registered before constraint generation
- Both frame and witness constraints reach solver

Ref: Plan 003 Phase 2
```

**Phase 3**:
```
feat(bimodal): remove fallback code and enforce fail-fast witness usage

Remove conditional fallback to Exists quantification in NecessityOperator,
enforcing fail-fast principle from CODE_STANDARDS.md.

Changes:
- Remove if/else fallback in NecessityOperator.false_at() (lines 408-449)
- Add WitnessPredicateError import
- Enforce witness predicates are REQUIRED (no optional behavior)
- Raise WitnessPredicateError with helpful context if witness missing
- Update docstring to document fail-fast behavior

BREAKING CHANGE: Witness predicates now required for Box operators.
Unregistered witnesses raise WitnessPredicateError with clear guidance.

Error Messages:
- Include formula string and available registered formulas
- Suggest checking build_model registration phase
- Provide context about evaluation point

Testing:
- test_modal_witness_integration.py: Fail-fast tests pass
- Unregistered witness access raises WitnessPredicateError
- Error messages include helpful debugging context

Standards: Implements fail-fast philosophy (CODE_STANDARDS.md:57-72)
Ref: Plan 003 Phase 3
```

**Phase 4**:
```
fix(bimodal): resolve BM_CM_1/2/3 countermodel failures

Complete witness predicate implementation fixes missing countermodels in
BM_CM_1, BM_CM_2, BM_CM_3 by ensuring witnesses are properly registered
and constraints are added to solver following exclusion architecture.

Fixes:
- BM_CM_1 (∀Future A ⊬ □A): Now finds countermodel ✓
- BM_CM_2 (∀Past A ⊬ □A): Now finds countermodel ✓
- BM_CM_3 (◇A ⊬ ∃future A): Now finds countermodel ✓
- BM_CM_4 (◇A ⊬ ∃past A): Countermodel found (regression test) ✓

Testing:
- All bimodal unit tests pass (60+ passing, 21 skipped)
- All BM_CM examples find countermodels successfully
- UNSAT cores show non-zero constraint counts (proving constraints valid)
- No performance regression (<10% overhead)

Coverage:
- witness_registry.py: >90%
- witness_constraints.py: >85%
- Overall bimodal: >85%

Closes: specs/reports/bimodal/001_debug_missing_countermodels.md
Ref: Plan 003 Phase 4

🤖 Generated with [Claude Code](https://claude.com/claude-code)

Co-Authored-By: Claude <noreply@anthropic.com>
```

---

## Implementation Checklist

### Phase 1: Registration Infrastructure
- [ ] Add `_processed_formulas` and `_formula_ast_mapping` to `__init__` (semantic.py:68)
- [ ] Add typing imports (`Set`, `Dict`, `Any`)
- [ ] Implement `_register_witness_predicates_recursive()` (after line 270)
- [ ] Implement `_is_processed()` (after recursive method)
- [ ] Implement `_get_witness_predicate()` (after is_processed)
- [ ] Implement `_generate_all_witness_constraints()` (after get_witness)
- [ ] Fix `_get_formula_string()` Z3 cast bug (line 254)
- [ ] Run unit tests, verify no regressions

### Phase 2: Model Building
- [ ] Research framework integration (BuildExample investigation)
- [ ] Implement `build_model(eval_point)` method (after line 400)
- [ ] Test that method creates solver and adds constraints
- [ ] Verify witnesses registered before constraints generated
- [ ] Confirm constraint injection works

### Phase 3: Fail-Fast Enforcement
- [ ] Add `WitnessPredicateError` import to operators.py
- [ ] Remove fallback code from `false_at()` (lines 408-449)
- [ ] Add fail-fast error check
- [ ] Update docstring
- [ ] Test error raising behavior

### Phase 4: Validation
- [ ] Run full test suite (pytest)
- [ ] Run BM_CM examples (dev_cli.py)
- [ ] Verify all countermodels found
- [ ] Check UNSAT core analysis
- [ ] Measure performance
- [ ] Update debug report

---

**Ready for Implementation**: This plan provides exact code locations, complete method implementations, and step-by-step instructions following the proven exclusion architecture pattern.
