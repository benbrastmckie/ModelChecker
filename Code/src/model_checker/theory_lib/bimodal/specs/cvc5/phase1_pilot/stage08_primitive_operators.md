# Stage 8: Primitive Operators

## Metadata
- **Stage**: 8/12 | **Est. Duration**: 2 hours (complex, witness predicates involved)
- **Complexity**: High (quantifiers + witness predicates)
- **Dependencies**: Stage 2 (quantifiers), Stage 3 (witness registry)
- **Files**: `operators.py` (classes NegationOperator through PastOperator)
- **Coverage Target**: >85%

## Objective

Migrate primitive modal/temporal operators from Z3 to CVC5, focusing on witness predicate handling with MBQI+enum-inst instead of pattern hints.

**CRITICAL**: This stage validates that CVC5's MBQI+enum-inst can replace Z3's pattern hints for witness predicates. If performance degrades, may need solver tuning.

## Actual Operators to Migrate

Based on code inspection (operators.py):

1. **NegationOperator** (line 42) - Simple negation, no witnesses
2. **AndOperator** (line 107) - Binary conjunction, no witnesses
3. **OrOperator** (line 199) - Binary disjunction, no witnesses
4. **BotOperator** (line 295) - Contradiction, no witnesses
5. **NecessityOperator** (line 358) - Modal Box, **uses witnesses**
6. **FutureOperator** (line 538) - Temporal F, **uses witnesses**
7. **PastOperator** (line ~685) - Temporal P, **uses witnesses**

**Migration Strategy**: Start with simple (1-4), then migrate witness operators (5-7) carefully.

## Key CVC5 Pattern: Witness Predicates Without Hints

### Z3 Pattern (uses pattern hints)
```python
# Z3 NecessityOperator.true_at (simplified)
accessible_world_var = z3.Int('accessible_world')

# Pattern hint guides instantiation
accessible_world_pred = registry.get_witness_predicate(formula_str)
pattern = z3.Pattern(accessible_world_pred(world, time))

constraint = z3.ForAll(
    [accessible_world_var],
    z3.Implies(
        # Accessibility condition
        accessible_world_pred(world, time) == accessible_world_var,
        # Body: argument true at accessible world
        argument.true_at(semantics, accessible_world_var, time)
    ),
    patterns=[pattern]  # CRITICAL FOR Z3 PERFORMANCE
)
```

### CVC5 Pattern (MBQI replaces patterns)
```python
# CVC5 NecessityOperator.true_at (MBQI+enum-inst)
accessible_world_var = solver.mkVar(WorldIdSort, 'accessible_world')

# Get witness predicate (CVC5 Term from Stage 3)
accessible_world_pred = registry.get_witness_predicate(formula_str)

# Build accessibility condition (APPLY_UF)
world_term = solver.mkInteger(world) if isinstance(world, int) else world
time_term = solver.mkInteger(time) if isinstance(time, int) else time
accessibility = solver.mkTerm(Kind.APPLY_UF, accessible_world_pred, world_term, time_term)
equality = solver.mkTerm(Kind.EQUAL, accessibility, accessible_world_var)

# Body: argument true at accessible world
body_constraint = argument.true_at(semantics, accessible_world_var, time)

# Build quantified formula
implies_body = solver.mkTerm(Kind.IMPLIES, equality, body_constraint)
var_list = solver.mkTerm(Kind.VARIABLE_LIST, accessible_world_var)
constraint = solver.mkTerm(Kind.FORALL, var_list, implies_body)

# NO PATTERNS! MBQI+enum-inst handles instantiation automatically
```

**CRITICAL DIFFERENCE**: CVC5 does NOT use pattern hints. Solver options (mbqi=true, enum-inst=true) enable quantifier instantiation.

## Implementation Tasks

### Task 1: TDD - Write Tests First (RED State)
**Duration**: 30 minutes

```python
class TestOperatorsCVC5Stage08(unittest.TestCase):
    def setUp(self):
        self.solver = cvc5.Solver()
        self.solver.setLogic("ALL")
        self.solver.setOption("produce-models", "true")
        self.solver.setOption("mbqi", "true")  # CRITICAL
        self.solver.setOption("enum-inst", "true")  # CRITICAL

        # ... setup semantics, operators ...

    def test_negation_returns_cvc5_term(self):
        """Test NegationOperator.true_at returns CVC5 Term."""
        # Create dummy argument
        # ...
        result = negation_op.true_at(arg, eval_point)
        self.assertIsInstance(result, cvc5.Term)

    def test_necessity_uses_forall_no_patterns(self):
        """Test NecessityOperator uses FORALL without pattern hints."""
        result = necessity_op.true_at(arg, eval_point)

        # Should contain FORALL
        # ...
        # Should NOT contain any z3.Pattern references
        # ...
```

**Test Strategy**:
- Test each operator individually (7 operators = 7+ tests)
- For witness operators, test FORALL structure
- Verify NO Z3 patterns remain

### Task 2: Migrate Simple Operators (Negation, And, Or, Bot)
**Duration**: 30 minutes

**Pattern**:
```python
# NegationOperator.true_at
def true_at(self, argument, eval_point):
    """Return constraint for negation true at eval_point."""
    # Get argument's true_at constraint
    arg_constraint = argument.true_at(self.semantics, eval_point)

    # Return negation using CVC5 NOT
    return self.semantics.solver.mkTerm(Kind.NOT, arg_constraint)
```

**For And/Or**: Use `Kind.AND` / `Kind.OR` with multiple arguments

**Checklist**:
- [ ] NegationOperator migrated
- [ ] AndOperator migrated
- [ ] OrOperator migrated
- [ ] BotOperator migrated
- [ ] Tests pass for simple operators

### Task 3: Migrate NecessityOperator (Modal Box with Witness)
**Duration**: 30 minutes

**This is the CRITICAL migration** - validates MBQI approach

**Full Pattern** (semantic.py has similar code to reference):
```python
def true_at(self, argument, eval_point):
    """Modal necessity: Box(argument) true at eval_point.

    Uses witness predicate with MBQI+enum-inst (no patterns).
    """
    world, time = eval_point.world, eval_point.time

    # Register witness predicate (if not already)
    formula_str = f"Box_{argument}"  # Unique identifier
    if not self.semantics.witness_registry.has_witness_predicate(formula_str):
        self.semantics.witness_registry.register_witness_predicate(formula_str)

    # Get witness predicate (CVC5 Term)
    accessible_world_pred = self.semantics.witness_registry.get_witness_predicate(formula_str)

    # Create quantified variable
    accessible_world_var = self.semantics.solver.mkVar(
        self.semantics.WorldIdSort,
        f'accessible_world_{formula_str}'
    )

    # Build accessibility condition
    world_term = (self.semantics.solver.mkInteger(world)
                  if isinstance(world, int) else world)
    time_term = (self.semantics.solver.mkInteger(time)
                 if isinstance(time, int) else time)

    # accessible_world_pred(world, time) application
    accessibility_term = self.semantics.solver.mkTerm(
        Kind.APPLY_UF,
        accessible_world_pred,
        world_term,
        time_term
    )

    # accessible_world_pred(world, time) == accessible_world_var
    equality = self.semantics.solver.mkTerm(
        Kind.EQUAL,
        accessibility_term,
        accessible_world_var
    )

    # Argument must be true at accessible world
    body_constraint = argument.true_at(self.semantics, accessible_world_var, time)

    # FORALL accessible_world_var: accessibility => body
    implies_body = self.semantics.solver.mkTerm(Kind.IMPLIES, equality, body_constraint)

    # Quantify
    var_list = self.semantics.solver.mkTerm(Kind.VARIABLE_LIST, accessible_world_var)
    forall_constraint = self.semantics.solver.mkTerm(Kind.FORALL, var_list, implies_body)

    return forall_constraint
```

**Apply Patterns**:
- Witness registry (Stage 3)
- APPLY_UF for witness predicate
- VARIABLE_LIST + FORALL (Stage 2)
- NO pattern hints

**Verify MBQI**: After implementation, test satisfiability. If slow, check solver options.

### Task 4: Migrate FutureOperator (Temporal with Witness)
**Duration**: 20 minutes

**Pattern**: Very similar to NecessityOperator, but:
- Witness predicate: `F_{argument}`
- Quantify over future times, not worlds
- Use `ForAllTime` helper from Stage 2

**Reference**: Necessity pattern above, adapt for temporal logic

### Task 5: Migrate PastOperator (Temporal with Witness)
**Duration**: 20 minutes

**Pattern**: Similar to FutureOperator
- Witness predicate: `P_{argument}`
- Quantify over past times

### Task 6: Test Integration and Performance
**Duration**: 10 minutes

**CRITICAL**: Validate MBQI performance

```python
def test_necessity_performance_mbqi(self):
    """Test NecessityOperator solves in reasonable time with MBQI."""
    # Create simple Box(p) formula
    # ...
    self.solver.assertFormula(constraint)

    start = time.time()
    result = self.solver.checkSat()
    duration = time.time() - start

    self.assertTrue(result.isSat() or result.isUnsat())
    self.assertLess(duration, 1.0)  # Should be fast
```

**If slow**: Check solver options, may need tuning

### Task 7: Coverage and Commit
**Duration**: 10 minutes

- [ ] Check coverage >85%
- [ ] All 7 operators migrated
- [ ] Performance validated
- [ ] Commit

## Success Criteria Checklist

- [ ] All 7 primitive operators migrated
- [ ] NO Z3 pattern hints remain
- [ ] Witness operators use MBQI+enum-inst
- [ ] All tests pass
- [ ] Performance acceptable (<1s for simple cases)
- [ ] Coverage >85%
- [ ] Ready for Stage 9 (derived operators)

## Common Issues & Solutions

### Issue: MBQI timeout or slow

**Cause**: MBQI needs more instantiations

**Solution**: Increase enum-inst or try additional options:
```python
solver.setOption("finite-model-find", "true")
solver.setOption("fmf-bound", "true")
```

### Issue: Witness predicate not working

**Cause**: Witness not properly registered or applied

**Solution**: Verify Stage 3 WitnessRegistry works correctly. Test in isolation.

## Performance Target

**From Phase 0**: Critical examples (BM_CM_1, etc.) solved in ~6ms with CVC5

**Stage 8 Validation**: Test simple Box/Future/Past formulas solve quickly (<100ms for unit tests)

**Full Validation**: Stage 11 will test critical examples end-to-end

## Adaptive Scoping

**Minimum Viable**: Migrate operators 1-5 (up to NecessityOperator). If Necessity works, Future/Past will follow same pattern.

**Stretch Goal**: Complete all 7 operators in one go.

**Don't Rush**: Necessity is critical. Take time to get it right. Future/Past can be quick once Necessity works.

---

**Stage 8 Status**: ☑ Complete

**Completion Summary** (2025-10-03):
- ✅ All 7 primitive operators migrated to CVC5:
  1. ✅ NegationOperator - Delegates to semantic methods
  2. ✅ AndOperator - Uses Kind.AND
  3. ✅ OrOperator - Uses Kind.OR
  4. ✅ BotOperator - Uses Kind.DISTINCT/EQUAL
  5. ✅ NecessityOperator - MBQI quantification (CRITICAL - no pattern hints!)
  6. ✅ FutureOperator - ForAllTime/ExistsTime helpers
  7. ✅ PastOperator - ForAllTime/ExistsTime helpers
- ✅ TDD tests written: 14 tests in test_operators_cvc5_stage08.py
- ✅ All tests passing (GREEN state)
- ✅ CVC5 imports added (cvc5, Kind)
- ✅ MBQI+enum-inst pattern validated
- ✅ Dependency migration: semantic.py true_at()/false_at() methods
- ✅ Sentence letter caching system implemented
- ✅ Fixed is_valid_time_for_world method calls
- ✅ Committed (f4949add)

**Files Modified**:
- `operators.py`: All 7 primitive operators migrated + NecessityOperator fixes
- `semantic.py`: true_at(), false_at(), _sentence_letter_to_term() migrated
- `test_operators_cvc5_stage08.py`: Comprehensive test suite (14 tests)

**Duration**: ~2 hours (including dependency migrations)
**Tests**: 14/14 passing
**Commit**: f4949add

**Ready for Stage 9 (Derived Operators)**
