# Stage 10: Witness Constraint Generation

## Metadata
- **Stage**: 10/12 | **Est. Duration**: 2 hours (CRITICAL - do not rush)
- **Complexity**: **HIGH** (nested quantifiers, performance-critical)
- **Dependencies**: Stage 3 (witness registry), Stage 8 (operators with witnesses)
- **Files**: `semantic/witness_constraints.py` (257 lines)
- **Coverage Target**: **>90%** (CRITICAL PATH REQUIREMENT)
- **Risk**: HIGH - nested quantifiers may need solver tuning

## Objective

Migrate witness constraint generation from Z3 pattern hints to CVC5 MBQI+enum-inst. This is the most complex and performance-critical stage.

**CRITICAL SUCCESS FACTOR**: Nested quantifiers must work efficiently with MBQI+enum-inst. If performance degrades significantly, may need CVC5-specific optimization.

## Actual Code to Migrate

File: `semantic/witness_constraints.py`

**Key Method**: `create_witness_constraints()` or similar (check actual file)

**Typical Pattern**: Generate constraints ensuring witness predicates satisfy modal/temporal properties.

## Z3 → CVC5 Pattern: Nested Quantifiers

### Z3 Nested Pattern (with hints)
```python
# Z3: ForAll x: ForAll y: body
x_var = z3.Int('x')
y_var = z3.Int('y')

inner_pattern = z3.Pattern(witness(y_var))
inner_forall = z3.ForAll(
    [y_var],
    body(x_var, y_var),
    patterns=[inner_pattern]
)

outer_pattern = z3.Pattern(predicate(x_var))
outer_forall = z3.ForAll(
    [x_var],
    inner_forall,
    patterns=[outer_pattern]
)
```

### CVC5 Nested Pattern (MBQI)
```python
# CVC5: ForAll x: ForAll y: body (NO PATTERNS)
x_var = solver.mkVar(XSort, 'x')
y_var = solver.mkVar(YSort, 'y')

# Build inner quantifier
inner_body = build_body(x_var, y_var)
inner_var_list = solver.mkTerm(Kind.VARIABLE_LIST, y_var)
inner_forall = solver.mkTerm(Kind.FORALL, inner_var_list, inner_body)

# Build outer quantifier
outer_var_list = solver.mkTerm(Kind.VARIABLE_LIST, x_var)
outer_forall = solver.mkTerm(Kind.FORALL, outer_var_list, inner_forall)

# NO PATTERNS! MBQI+enum-inst handles nested quantifiers
```

**CRITICAL**: CVC5's MBQI must discover instantiations without pattern hints.

## Implementation Tasks

### Task 1: Understand Existing Constraints
**Duration**: 20 minutes

**Before writing ANY code**:
1. Read `witness_constraints.py` thoroughly
2. Identify all methods that generate constraints
3. Map which methods use nested quantifiers
4. Identify witness predicate usage

**Document**:
```
Method X:
- Uses witness predicate Y
- Nested quantifiers: world, time
- Z3 patterns: [witness(world), predicate(time)]
```

### Task 2: TDD - Write Tests First (RED State)
**Duration**: 30 minutes

**CRITICAL**: Test each constraint type separately

```python
class TestWitnessConstraintsCVC5Stage10(unittest.TestCase):
    def test_witness_constraint_no_patterns(self):
        """Test witness constraints use FORALL without patterns."""
        # Generate constraint
        # ...
        # Verify NO z3.Pattern in result
        # Verify uses CVC5 FORALL

    def test_nested_quantifier_structure(self):
        """Test nested quantifiers have correct VARIABLE_LIST structure."""
        # Generate nested constraint
        # ...
        # Verify outer FORALL contains inner FORALL

    def test_witness_constraint_satisfiable(self):
        """Test witness constraints are satisfiable (MBQI works)."""
        # Create simple witness constraint
        self.solver.assertFormula(constraint)

        result = self.solver.checkSat()
        # Should be sat or unsat, not unknown/timeout
        self.assertTrue(result.isSat() or result.isUnsat())
```

**Test Strategy**:
- Test constraint generation structure
- Test satisfiability (MBQI validation)
- Test performance (should not timeout)

### Task 3: Migrate Constraint Generation Methods
**Duration**: 45 minutes

**Pattern for Each Method**:
1. Identify Z3 `ForAll` with patterns
2. Remove pattern parameter
3. Build VARIABLE_LIST explicitly
4. Use FORALL with var_list and body
5. Ensure APPLY_UF for witness predicates

**Example Migration**:
```python
# Z3 Original
def generate_accessibility_constraint(self, witness_pred, world_var, time_var):
    pattern = z3.Pattern(witness_pred(world_var, time_var))
    return z3.ForAll(
        [world_var, time_var],
        z3.Implies(..., body),
        patterns=[pattern]
    )

# CVC5 Migrated
def generate_accessibility_constraint(self, witness_pred, world_var, time_var):
    # Build body using APPLY_UF
    witness_app = self.solver.mkTerm(Kind.APPLY_UF, witness_pred, world_var, time_var)
    body = self.solver.mkTerm(Kind.IMPLIES, ..., ...)

    # Build quantifier with VARIABLE_LIST
    var_list = self.solver.mkTerm(Kind.VARIABLE_LIST, world_var, time_var)
    return self.solver.mkTerm(Kind.FORALL, var_list, body)
```

**Apply Established Patterns**:
- VARIABLE_LIST (Stage 2)
- APPLY_UF (Stages 4, 5, 8)
- No patterns

### Task 4: Test Each Constraint Individually
**Duration**: 15 minutes

**CRITICAL**: Don't test all constraints together initially

For each constraint method:
1. Generate constraint
2. Assert in solver
3. Call checkSat()
4. Verify sat/unsat (not unknown)
5. Measure time (<1s for simple cases)

**If timeout**: Likely MBQI issue, may need solver tuning

### Task 5: Performance Validation
**Duration**: 20 minutes

**CRITICAL VALIDATION**: Compare performance to Phase 0 baseline

```python
def test_witness_constraint_performance(self):
    """Test witness constraints solve efficiently with MBQI."""
    # Generate multiple witness constraints
    for formula in test_formulas:
        constraint = generate_witness_constraint(formula)
        self.solver.assertFormula(constraint)

    start = time.time()
    result = self.solver.checkSat()
    duration = time.time() - start

    # Should be fast (within 2× of Phase 0)
    self.assertLess(duration, 0.1)  # 100ms for unit test
```

**Performance Targets**:
- Unit tests: <100ms per constraint
- Integration (Stage 11): ~6ms for critical examples

**If slow**: See "Performance Tuning" section below

### Task 6: Coverage and Commit
**Duration**: 10 minutes

- [ ] Check coverage >90% (STRICT)
- [ ] All constraint methods migrated
- [ ] Performance validated
- [ ] Commit

## Success Criteria Checklist

- [x] ALL witness constraints migrated ✅
- [x] NO Z3 patterns remain ✅
- [x] Nested quantifiers use VARIABLE_LIST correctly ✅
- [x] All tests pass (12/12 GREEN) ✅
- [x] Performance acceptable (no timeouts, <1s) ✅
- [x] **Coverage >90%** (CRITICAL) ✅
- [x] Ready for Stage 11 (integration) ✅

## Performance Tuning (If Needed)

### If MBQI times out:

**Option 1**: Increase instantiation bounds
```python
solver.setOption("quant-cf", "true")
solver.setOption("quant-cf-mode", "conflict")
```

**Option 2**: Enable finite model finding
```python
solver.setOption("finite-model-find", "true")
solver.setOption("fmf-bound", "true")
```

**Option 3**: Adjust enumeration
```python
solver.setOption("enum-inst-interleave", "true")
solver.setOption("full-saturate-quant", "true")
```

**Option 4**: Consult CVC5 documentation for quantifier options

### If performance degraded from Z3:

**Acceptable**: Within 2-3× of Z3 (MBQI overhead)
**Concerning**: >10× slower or timeouts
**Action**: Document performance, may need CVC5 expert consultation

## Common Issues & Solutions

### Issue: Nested quantifiers timeout

**Cause**: MBQI struggles with deep nesting

**Solution**:
- Simplify constraint structure if possible
- Use helper methods to flatten nesting
- Adjust solver options (above)

### Issue: Witness predicate not instantiated

**Cause**: MBQI not discovering instantiations

**Solution**:
- Verify witness predicate registered (Stage 3)
- Check APPLY_UF correct
- Add bounds with finite-model-find

### Issue: Unknown result (not sat/unsat)

**Cause**: Solver cannot decide with current configuration

**Solution**: Increase timeout or adjust quantifier options

## Critical Decision Point

**If witness constraints work efficiently**: Proceed to Stage 11 with confidence

**If performance issues**: Document issues, may need:
1. CVC5-specific optimization (Phase 1.5)
2. Abstraction layer to support both Z3 and CVC5 dynamically
3. Expert consultation on CVC5 quantifier configuration

**Don't Compromise Quality**: Better to spend extra time here than discover problems in Stage 11.

## Adaptive Scoping

**Minimum Viable**: Migrate all constraint generation methods with >90% coverage. Performance validation is REQUIRED.

**No Shortcuts**: This stage is critical. Allocate full 2 hours. Don't rush.

**Success Definition**: All tests pass AND performance acceptable AND coverage >90%

---

**Stage 10 Status**: ✅ COMPLETE (2025-10-03, commit 51cba769)

**Performance Result**: All constraints solve <1s, MBQI+enum-inst validated successfully. No timeouts. Ready for Stage 11 integration.
