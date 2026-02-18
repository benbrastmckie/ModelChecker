# Stage 11: Examples Integration

## Metadata
- **Stage**: 11/12 | **Est. Duration**: 1.5 hours (first end-to-end validation)
- **Complexity**: Medium (integration complexity)
- **Dependencies**: ALL STAGES 1-10 (full pipeline required)
- **Files**: `examples.py` (671 lines)
- **Performance Target**: ~6ms for critical examples (within 2× of Phase 0)

## Objective

Migrate all example definitions from Z3 to CVC5, validating that the complete migration works end-to-end. This is the first full test of the migrated bimodal theory.

**CRITICAL VALIDATION**: 6 critical examples (BM_CM_1, BM_CM_2, TN_CM_*, MD_CM_*) must solve deterministically in ~6ms.

## Actual Changes Needed

File: `examples.py`

### Change 1: Solver Setup
```python
# Z3 (OLD)
def create_solver():
    return z3.Solver()

# CVC5 (NEW)
def create_solver():
    solver = cvc5.Solver()
    solver.setLogic("ALL")
    solver.setOption("produce-models", "true")
    solver.setOption("mbqi", "true")  # CRITICAL
    solver.setOption("enum-inst", "true")  # CRITICAL
    return solver
```

### Change 2: BimodalSemantics Initialization
```python
# Z3 (OLD)
semantics = BimodalSemantics(N=3, M=10)

# CVC5 (NEW)
solver = create_solver()
semantics = BimodalSemantics(N=3, M=10, solver=solver)
```

### Change 3: Result Checking
```python
# Z3 (OLD)
result = solver.check()
if result == z3.sat:
    model = solver.model()
    # ...

# CVC5 (NEW)
result = solver.checkSat()
if result.isSat():
    # Extract directly from solver (no separate model object)
    # ...
```

### Change 4: Model Extraction (if used in examples)
```python
# Z3 (OLD)
value = model.eval(term)

# CVC5 (NEW)
value = solver.getValue(term)
```

## Implementation Tasks

### Task 1: Understand Example Structure
**Duration**: 15 minutes

**Before changing code**:
1. Read examples.py to understand structure
2. Identify how many examples exist
3. Map which examples use which operators
4. Identify the 6 critical examples

**Critical Examples** (from Phase 0):
- BM_CM_1: Bimodal countermodel 1
- BM_CM_2: Bimodal countermodel 2
- TN_CM_1: Temporal necessity countermodel 1
- TN_CM_2: Temporal necessity countermodel 2
- MD_CM_1: Modal diamond countermodel 1
- MD_CM_2: Modal diamond countermodel 2

### Task 2: Create Solver Setup Function
**Duration**: 10 minutes

```python
import cvc5
from cvc5 import Kind

def create_cvc5_solver():
    """Create CVC5 solver with bimodal-optimized configuration.

    Returns:
        cvc5.Solver: Configured solver instance
    """
    solver = cvc5.Solver()
    solver.setLogic("ALL")
    solver.setOption("produce-models", "true")

    # CRITICAL: MBQI+enum-inst for witness predicates
    solver.setOption("mbqi", "true")
    solver.setOption("enum-inst", "true")

    return solver
```

### Task 3: Update All Example Definitions
**Duration**: 30 minutes

**Pattern for Each Example**:
```python
# OLD Z3
def example_BM_CM_1():
    solver = z3.Solver()
    semantics = BimodalSemantics(N=3, M=10)
    # ... build formula ...
    solver.add(constraint)
    result = solver.check()
    if result == z3.sat:
        print("Satisfiable")
    return result

# NEW CVC5
def example_BM_CM_1():
    solver = create_cvc5_solver()
    semantics = BimodalSemantics(N=3, M=10, solver=solver)
    # ... build formula (no changes needed) ...
    solver.assertFormula(constraint)
    result = solver.checkSat()
    if result.isSat():
        print("Satisfiable")
    return result
```

**Changes Per Example**:
1. Create CVC5 solver
2. Pass solver to BimodalSemantics
3. Change `solver.add()` → `solver.assertFormula()`
4. Change `solver.check()` → `solver.checkSat()`
5. Change `result == z3.sat` → `result.isSat()`

**Estimate**: ~2 minutes per example × 22 examples = 44 minutes (but many may be similar)

### Task 4: Test Critical Examples
**Duration**: 20 minutes

**CRITICAL VALIDATION**: Test 6 critical examples first

```bash
cd Code
./dev_cli.py src/model_checker/theory_lib/bimodal/examples.py
```

**For Each Critical Example**:
1. Run example
2. Verify result (sat/unsat as expected from Phase 0)
3. Measure solve time
4. Compare to Phase 0 baseline (~6ms)

**Expected Results**:
```
BM_CM_1: sat in ~6ms ✓
BM_CM_2: sat in ~8ms ✓
TN_CM_1: unsat in ~5ms ✓
# etc.
```

**If any example fails or times out**: CRITICAL ISSUE - debug before proceeding

### Task 5: Test All Examples
**Duration**: 15 minutes

**Run Full Test Suite**:
```bash
# Run all examples
./dev_cli.py src/model_checker/theory_lib/bimodal/examples.py

# Or run unit tests if examples have tests
PYTHONPATH=src pytest src/model_checker/theory_lib/bimodal/tests/ -v
```

**Verify**:
- [ ] All examples that were sat are still sat
- [ ] All examples that were unsat are still unsat
- [ ] No unknown results
- [ ] No timeouts

### Task 6: Performance Validation
**Duration**: 10 minutes

**CRITICAL METRICS**:

| Example | Phase 0 (Z3) | Stage 11 (CVC5) | Ratio |
|---------|--------------|-----------------|-------|
| BM_CM_1 | 5s+ (timeout) | ~6ms | 850× faster ✓ |
| BM_CM_2 | 5s+ (timeout) | ~7ms | ~700× faster ✓ |
| TN_CM_1 | ~50ms | ~6ms | 8× faster ✓ |
| TN_CM_2 | ~60ms | ~8ms | 7× faster ✓ |
| MD_CM_1 | ~40ms | ~5ms | 8× faster ✓ |
| MD_CM_2 | ~45ms | ~6ms | 7× faster ✓ |

**Acceptance Criteria**:
- CVC5 must maintain ~6ms performance on critical examples
- CVC5 should be faster or comparable to Z3 on all examples
- No regressions (slower than Phase 0 Z3)

**If performance degrades**: See Stage 10 performance tuning

### Task 7: Commit
**Duration**: 5 minutes

- [ ] All examples migrated
- [ ] All critical examples validated
- [ ] Performance meets targets
- [ ] Commit with performance results

## Success Criteria Checklist

- [ ] All 22 examples migrated to CVC5
- [ ] 6 critical examples solve correctly
- [ ] Critical examples: ~6ms performance (within 2× acceptable)
- [ ] No Z3 dependencies remain in examples.py
- [ ] All results match Phase 0 expectations
- [ ] No timeouts or unknown results
- [ ] Ready for Stage 12 (iteration)

## Common Issues & Solutions

### Issue: Example times out

**Cause**: Likely witness constraint or operator issue from earlier stages

**Solution**:
1. Isolate which operator/constraint is slow
2. Test that specific operator in isolation
3. Review Stage 8 or Stage 10 implementation
4. Check solver options

### Issue: Result differs from Phase 0

**Cause**: Logic error in migration

**Solution**:
1. Compare Z3 vs CVC5 constraints visually
2. Check operator implementations (Stage 8)
3. Verify semantics match
4. May need to fix earlier stage

### Issue: Unknown result

**Cause**: Solver cannot decide with current configuration

**Solution**: Add timeout, check quantifier configuration

## Performance Tuning (If Needed)

If critical examples >12ms (2× target):

### Option 1: Profile which constraints are slow
```python
import time

start = time.time()
solver.assertFormula(constraint)
print(f"Constraint added in {time.time() - start:.3f}s")
```

### Option 2: Adjust solver options (see Stage 10)

### Option 3: Simplify constraints if possible

**Don't Compromise Correctness**: Slower but correct > fast but wrong

## Critical Decision Point

**If all examples pass with acceptable performance**: Phase 1 is essentially complete! Stage 12 is minor.

**If performance issues**: May need Phase 1.5 for optimization before Phase 2.

**If correctness issues**: Fix before Stage 12. Iteration depends on correct solving.

## Adaptive Scoping

**Minimum Viable**: All 6 critical examples work with ~6ms performance. Other examples can be marked "TODO" if needed.

**Full Success**: All 22 examples migrated and validated.

**Don't Rush**: This is validation of ALL prior work. Take time to ensure correctness.

---

**Stage 11 Status**: ☐ Not Started | ☐ In Progress | ☐ Complete

**Performance Results**: ___ (to be filled)
