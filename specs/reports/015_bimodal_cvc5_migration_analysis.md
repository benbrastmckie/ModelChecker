# Bimodal Theory CVC5 Migration Analysis

## Metadata
- **Date**: 2025-10-02
- **Phase**: Phase 1 - Bimodal Theory CVC5 Pilot
- **Scope**: Direct migration of bimodal theory from Z3 to CVC5 (no abstraction)
- **Purpose**: Learn API patterns empirically to inform Phase 2 abstraction design

## Migration Scope

### Files to Migrate

| File | Lines | Complexity | Priority | Z3 Usage |
|------|-------|------------|----------|----------|
| semantic.py | 2,593 | Very High | 1 | Heavy (24x And, 14x ForAll, 8x Function) |
| operators.py | 1,083 | High | 2 | Medium (operator semantics) |
| witness_constraints.py | 257 | High | 3 | Critical (ForAll patterns) |
| witness_registry.py | 177 | Medium | 4 | Medium (witness management) |
| examples.py | 671 | Medium | 5 | Light (entry point) |
| iterate.py | 602 | Medium | 6 | Medium (model iteration) |

**Total**: ~5,600 lines of code

### Z3 API Usage Analysis (semantic.py)

From frequency analysis:
- `z3.And`: 24 uses (logical conjunction)
- `z3.Int`: 19 uses (integer variables)
- `z3.IntVal`: 18 uses (integer constants)
- `z3.Implies`: 17 uses (logical implication)
- `z3.ForAll`: 14 uses (universal quantification) **CRITICAL**
- `z3.Select`: 13 uses (array indexing)
- `z3.Not`: 8 uses (negation)
- `z3.Function`: 8 uses (uninterpreted functions) **CRITICAL**
- `z3.IntSort`: 7 uses (sort definitions)
- `z3.Exists`: 6 uses (existential quantification)
- `z3.BitVec`: 6 uses (bitvector variables)

**Critical Patterns**:
1. Uninterpreted functions with complex signatures
2. ForAll quantifiers with pattern hints
3. Array operations (Select)
4. BitVec for world states
5. Nested quantifiers

## CVC5 API Translation Patterns

### Pattern 1: Sort Definitions

**Z3**:
```python
self.WorldStateSort = z3.BitVecSort(self.N)
self.TimeSort = z3.IntSort()
self.WorldIdSort = z3.IntSort()
```

**CVC5**:
```python
self.WorldStateSort = solver.mkBitVectorSort(self.N)
self.TimeSort = solver.getIntegerSort()
self.WorldIdSort = solver.getIntegerSort()
```

### Pattern 2: Function Declarations

**Z3**:
```python
self.task = z3.Function(
    'task',
    self.WorldIdSort,    # Input: world ID
    self.TimeSort,       # Input: time
    z3.BoolSort()        # Output: boolean
)
```

**CVC5**:
```python
from cvc5 import Kind
self.task = solver.mkConst(
    solver.mkFunctionSort(
        [self.WorldIdSort, self.TimeSort],  # Input sorts
        solver.getBooleanSort()              # Output sort
    ),
    'task'
)
```

### Pattern 3: Array Sorts

**Z3**:
```python
z3.ArraySort(self.TimeSort, self.WorldStateSort)
```

**CVC5**:
```python
solver.mkArraySort(self.TimeSort, self.WorldStateSort)
```

### Pattern 4: ForAll Quantifiers

**Z3**:
```python
time_var = z3.Int('t')
body = z3.Implies(
    validity_check(time_var),
    constraint_body(time_var)
)
return z3.ForAll([time_var], body)
```

**CVC5**:
```python
time_var = solver.mkVar(self.TimeSort, 't')
body = solver.mkTerm(
    Kind.IMPLIES,
    validity_check(time_var),
    constraint_body(time_var)
)
return solver.mkTerm(
    Kind.FORALL,
    solver.mkTerm(Kind.VARIABLE_LIST, time_var),
    body
)
```

### Pattern 5: Logical Operators

**Z3**:
```python
z3.And(a, b, c)
z3.Or(a, b)
z3.Not(a)
z3.Implies(a, b)
```

**CVC5**:
```python
solver.mkTerm(Kind.AND, a, b, c)
solver.mkTerm(Kind.OR, a, b)
solver.mkTerm(Kind.NOT, a)
solver.mkTerm(Kind.IMPLIES, a, b)
```

### Pattern 6: Function Application

**Z3**:
```python
self.truth_condition(world, time, atom)  # Operator overloading
```

**CVC5**:
```python
solver.mkTerm(Kind.APPLY_UF, self.truth_condition, world, time, atom)
```

### Pattern 7: Integer Constants

**Z3**:
```python
z3.IntVal(0)
z3.Int('variable')
```

**CVC5**:
```python
solver.mkInteger(0)
solver.mkConst(solver.getIntegerSort(), 'variable')  # Constant
solver.mkVar(solver.getIntegerSort(), 'variable')    # For quantifiers
```

### Pattern 8: BitVectors

**Z3**:
```python
z3.BitVec('world_state', self.N)
```

**CVC5**:
```python
solver.mkConst(solver.mkBitVectorSort(self.N), 'world_state')
```

### Pattern 9: Array Select

**Z3**:
```python
z3.Select(array, index)
```

**CVC5**:
```python
solver.mkTerm(Kind.SELECT, array, index)
```

### Pattern 10: Substitution

**Z3**:
```python
z3.substitute(expr, [(old_var, new_var)])
```

**CVC5**:
```python
# CVC5 uses different approach - may need term reconstruction
# Or use solver.mkTerm with substituted subterms
# Pattern TBD during migration
```

## Migration Strategy

### Phase 1.1: Semantic Core (Days 1-2)

**Objective**: Migrate semantic.py core definitions

**Tasks**:
1. Write comprehensive tests for semantic.py (TDD RED)
   - Test sort definitions
   - Test primitive function declarations
   - Test frame constraints
2. Migrate define_sorts()
3. Migrate define_primitives()
4. Migrate build_frame_constraints()
5. Run tests (TDD GREEN)
6. Document patterns learned

**Success Criteria**:
- All sort definitions work with CVC5
- All primitive functions declared correctly
- Frame constraints compile without errors
- Tests pass

### Phase 1.2: Operators (Day 2-3)

**Objective**: Migrate operators.py

**Tasks**:
1. Write tests for operators (TDD RED)
   - Test extensional operators (negation, and, or)
   - Test modal operators (Box, Diamond)
   - Test temporal operators (Future, Past)
2. Migrate NegationOperator, AndOperator, OrOperator
3. Migrate NecessityOperator (Box) - uses witnesses
4. Migrate FutureOperator, PastOperator
5. Run tests (TDD GREEN)

**Critical**: Modal and temporal operators use witness predicates

### Phase 1.3: Witness System (Day 3-4)

**Objective**: Migrate witness predicate system

**Tasks**:
1. Write tests for witness_constraints.py (TDD RED)
2. Migrate WitnessConstraintGenerator
3. Migrate witness ForAll patterns **CRITICAL**
4. Write tests for witness_registry.py (TDD RED)
5. Migrate WitnessRegistry
6. Run tests (TDD GREEN)

**Critical**: ForAll with witness predicates is core to CVC5 success

### Phase 1.4: Integration (Day 4-5)

**Objective**: Integrate all components and test examples

**Tasks**:
1. Update examples.py to use CVC5 solver
2. Run BM_CM_1 with migrated code
3. Run BM_CM_2 with migrated code
4. Run TN_CM_1, TN_CM_2 with migrated code
5. Run MD_CM_1, MD_CM_2 with migrated code
6. Compare results with standalone tests
7. Debug any discrepancies

**Success Criteria**:
- All 6 critical tests pass through bimodal theory
- Results match standalone CVC5 tests
- Performance maintained (~6ms for BM_*, ~0.2ms for others)

### Phase 1.5: Documentation (Day 5)

**Objective**: Document all API patterns learned

**Tasks**:
1. Update specs/reports/011_z3_to_cvc5_api_translation.md
2. Create migration guide with examples
3. Document pain points encountered
4. Document performance observations
5. Create specs/reports/014_bimodal_cvc5_pilot_results.md

## Known Challenges

### Challenge 1: Pattern Hints

**Z3**: Uses pattern hints in ForAll for quantifier instantiation
**CVC5**: Uses MBQI + enum-inst instead

**Resolution**: Remove pattern hints, rely on CVC5 options

### Challenge 2: Operator Overloading

**Z3**: `a + b`, `a & b`, function calls work directly
**CVC5**: All operations must use `mkTerm(Kind.*, ...)`

**Resolution**: Explicit term construction everywhere

### Challenge 3: Variable vs Constant

**Z3**: Less strict about mkConst vs mkVar
**CVC5**: Strict distinction:
- `mkConst`: For constants (uninterpreted functions, atoms)
- `mkVar`: For quantified variables only

**Resolution**: Careful tracking of variable contexts

### Challenge 4: Array Operations

**Z3**: `z3.Select`, `z3.Store` work naturally
**CVC5**: `mkTerm(Kind.SELECT, ...)`, `mkTerm(Kind.STORE, ...)`

**Resolution**: Wrap in helper functions if needed

### Challenge 5: Substitution

**Z3**: `z3.substitute(expr, [(old, new)])`
**CVC5**: No direct substitute API

**Resolution**: TBD - may need term reconstruction

### Challenge 6: Type Checking

**Z3**: More forgiving
**CVC5**: Strict type checking

**Resolution**: Ensure all sorts match exactly

## Test Strategy

### Unit Tests

Per TDD requirements:
1. Write test FIRST for each component
2. Verify RED state (test fails)
3. Implement minimal code to pass
4. Verify GREEN state
5. Refactor while maintaining GREEN

### Integration Tests

Run through full bimodal theory:
- BM_CM_1: \Future A ⊬ \Box A
- BM_CM_2: \Past A ⊬ \Box A
- TN_CM_1: A ⊬ \Future A
- TN_CM_2: \future A, \future B ⊬ \future (A ∧ B)
- MD_CM_1: \Box (A ∨ B) ⊬ \Box A, \Box B
- MD_CM_2: \Diamond (A ∨ B) ⊬ (\Diamond A ∧ \Diamond B)

### Regression Tests

Ensure existing Z3 unit tests still pass on main branch.

## Risk Mitigation

### Risk 1: Breaking Changes

**Mitigation**: Keep Z3 version on main branch, CVC5 on feature branch

### Risk 2: Incomplete Migration

**Mitigation**: Component-by-component approach with testing at each step

### Risk 3: Performance Regression

**Mitigation**: Benchmark after each component migration

### Risk 4: Unforeseen API Gaps

**Mitigation**: Document blockers immediately, seek workarounds or CVC5 community help

## Success Metrics

### Functional
- ✅ All 6 critical tests pass
- ✅ sat/unsat results match standalone tests
- ✅ Deterministic results (5/5 runs identical)

### Performance
- ✅ BM_* examples: <100ms (target ~6ms)
- ✅ TN_* examples: <10ms (target ~0.2ms)
- ✅ MD_* examples: <10ms (target ~0.2ms)

### Quality
- ✅ >85% test coverage overall
- ✅ >90% test coverage for witness system
- ✅ TDD compliance throughout
- ✅ No decorators
- ✅ Relative imports for local modules

## Next Steps

1. **Immediate**: Start Phase 1.1 - Write semantic.py tests (TDD RED)
2. **Day 1-2**: Complete semantic.py migration
3. **Day 2-3**: Complete operators.py migration
4. **Day 3-4**: Complete witness system migration
5. **Day 4-5**: Integration and documentation

## References

- [CVC5 Configuration Guide](../../Code/docs/development/CVC5_CONFIGURATION.md)
- [CVC5 Feasibility Results](012_cvc5_feasibility_results.md)
- [Z3 to CVC5 API Translation](011_z3_to_cvc5_api_translation.md)
- [Implementation Plan Phase 1](../plans/105_smt_solver_abstraction_REVISED.md)
