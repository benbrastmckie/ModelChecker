# Stage 1: Integration Test Setup

## Metadata
- **Stage**: 1/6 (Phase 3 - Bimodal Abstraction Integration)
- **Estimated Duration**: 1 day (8 hours)
- **Complexity**: Medium
- **Dependencies**: Phase 2 complete (abstraction layer ready)
- **Files**: 
  - `tests/integration/test_bimodal_solver_interface.py` (new)
  - `Code/tests/integration/test_solver_equivalence.py` (new)
  - `tests/integration/test_performance_validation.py` (new)
- **Coverage Target**: Integration tests for all 22 examples
- **Risk**: Medium - Setting up comprehensive test infrastructure

## Objective

Write integration tests BEFORE migrating bimodal theory to SolverInterface (TDD approach). These tests will initially FAIL, proving the RED state, then guide the migration implementation in subsequent stages.

**Success Criteria**: 
- All integration tests written and failing as expected
- Test fixtures ready for dual-solver validation
- Performance baselines established

## Implementation Tasks

### Task 1: [TDD-RED] Write test_bimodal_solver_interface.py
**Duration**: 3 hours

- [ ] Create test file: `tests/integration/test_bimodal_solver_interface.py`
- [ ] Write tests for bimodal theory using SolverInterface
- [ ] Test all 6 critical examples (BM_CM_1, BM_CM_2, TN_CM_2, etc.)
- [ ] Verify tests FAIL (bimodal currently uses direct CVC5)

**Implementation Pattern**:
```python
import unittest
from model_checker.solver import SolverFactory
from model_checker.theory_lib.bimodal import BimodalSemantics

class TestBimodalSolverInterface(unittest.TestCase):
    def setUp(self):
        factory = SolverFactory()
        self.cvc5_adapter = factory.create("cvc5")
        self.z3_adapter = factory.create("z3")
    
    def test_BM_CM_1_with_cvc5(self):
        # This will FAIL until bimodal migrated
        solver = self.cvc5_adapter.create_solver()
        semantics = BimodalSemantics(self.cvc5_adapter)
        # ... test logic
```

**Testing Command**:
```bash
PYTHONPATH=Code/src pytest Code/src/model_checker/theory_lib/bimodal/tests/integration/test_bimodal_solver_interface.py -v
# Expected: FAIL (ImportError or usage errors - bimodal doesn't use abstraction yet)
```

**Expected**: Tests FAIL with import/usage errors

### Task 2: [TDD-RED] Write test_solver_equivalence.py
**Duration**: 3 hours

- [ ] Create test file: `Code/tests/integration/test_solver_equivalence.py`
- [ ] Write Z3 vs CVC5 equivalence tests
- [ ] Cover all 22 bimodal examples
- [ ] Compare sat/unsat results between solvers
- [ ] Verify tests FAIL (bimodal not using abstraction)

**Implementation Pattern**:
```python
def test_example_equivalence(self):
    """Test Z3 and CVC5 produce same sat/unsat on example."""
    factory = SolverFactory()
    
    # Run with Z3
    z3_adapter = factory.create("z3")
    z3_result = run_example(z3_adapter, "BM_CM_1")
    
    # Run with CVC5  
    cvc5_adapter = factory.create("cvc5")
    cvc5_result = run_example(cvc5_adapter, "BM_CM_1")
    
    # Should agree
    self.assertEqual(z3_result, cvc5_result)
```

**Testing Command**:
```bash
PYTHONPATH=Code/src pytest Code/tests/integration/test_solver_equivalence.py -v
# Expected: FAIL (bimodal not migrated to abstraction)
```

### Task 3: [TDD-RED] Write test_performance_validation.py
**Duration**: 2 hours

- [ ] Create test file: `tests/integration/test_performance_validation.py`
- [ ] Write performance tests for 6 critical examples
- [ ] Measure CVC5 solve times (~6ms target)
- [ ] Establish baseline measurements
- [ ] Verify tests FAIL (no abstraction yet)

**Implementation Pattern**:
```python
import time

def test_cvc5_performance_BM_CM_1(self):
    """Test CVC5 maintains ~6ms performance."""
    adapter = factory.create("cvc5")
    
    start = time.time()
    result = run_example(adapter, "BM_CM_1")
    duration = (time.time() - start) * 1000  # ms
    
    self.assertEqual(result, "sat")
    self.assertLess(duration, 10)  # <10ms target
```

### Task 4: Create Test Fixtures
**Duration**: 1 hour

- [ ] Create fixture utilities for adapter creation
- [ ] Add result comparison helpers
- [ ] Add performance measurement utilities
- [ ] Document fixture usage

## Testing Strategy

**TDD Verification (RED State)**:
1. Run all integration tests
2. Verify they FAIL as expected
3. Document failure modes (ImportError, usage errors, etc.)
4. This proves tests are correctly written for post-migration code

**Commands**:
```bash
# Verify TDD RED state
PYTHONPATH=Code/src pytest Code/src/model_checker/theory_lib/bimodal/tests/integration/ -v
# Expected: All FAIL (bimodal not using abstraction yet)

# Verify test structure
grep -r "SolverInterface" Code/src/model_checker/theory_lib/bimodal/tests/integration/
# Should find test references to abstraction layer
```

## Success Criteria Checklist

- [ ] test_bimodal_solver_interface.py created and failing
- [ ] test_solver_equivalence.py created and failing  
- [ ] test_performance_validation.py created and failing
- [ ] Test fixtures created
- [ ] All tests documented
- [ ] RED state verified (tests fail as expected)

## Common Issues & Solutions

### Issue 1: Tests Pass Instead of Failing
**Problem**: Tests unexpectedly pass in RED state
**Solution**: Verify test imports are correct and tests actually use SolverInterface (not direct solvers)

### Issue 2: Import Errors
**Problem**: Cannot import SolverInterface or adapters
**Solution**: Expected in RED state - document for use after migration

### Issue 3: Performance Baseline Unclear
**Problem**: Don't know what performance to expect
**Solution**: Reference Phase 1 measurements (~6ms for BM_CM_* with CVC5)

## Risk Mitigation

**Risk**: Tests too tightly coupled to implementation
**Mitigation**: Focus on behavioral tests (sat/unsat results, not internal APIs)

**Risk**: Performance tests flaky
**Mitigation**: Use generous time bounds, run multiple iterations

## Dependencies for Next Stage

Stage 2 (Semantic Core Migration) requires:
- ✅ Integration tests written (failing)
- ✅ Test infrastructure ready
- ✅ Clear understanding of expected behavior

## Notes

**TDD Philosophy**: These tests represent the *desired* state after migration. They should fail now and guide the implementation in Stages 2-4.

**Reference**: Phase 2 equivalence tests (`test_adapter_equivalence.py`) provide patterns for dual-solver testing.

---

## Stage 1 Completion Metadata

**Status**: ✅ **COMPLETE**
**Completion Date**: 2025-10-03
**Actual Duration**: ~2 hours (vs 8 hours estimated)

### Completed Deliverables

1. **test_bimodal_solver_interface.py** ✅
   - Location: `Code/src/model_checker/theory_lib/bimodal/tests/integration/`
   - Lines: 351
   - Test cases: 11 (6 CVC5, 3 Z3, 2 fixtures)
   - Coverage: All 6 critical examples

2. **test_solver_equivalence.py** ✅
   - Location: `Code/tests/integration/`
   - Lines: 380
   - Test cases: 22 (all bimodal examples)
   - Coverage: Z3/CVC5 equivalence validation

3. **test_performance_validation.py** ✅
   - Location: `Code/src/model_checker/theory_lib/bimodal/tests/integration/`
   - Lines: 356
   - Test cases: 7 performance tests
   - Coverage: 6 critical examples + baseline

4. **Test Fixtures** ✅
   - SolverFactory fixtures
   - Example runner helpers
   - Performance measurement utilities
   - Equivalence validation helpers

### TDD RED State Verification

**Failure Modes Documented**:
- TypeError: BimodalSemantics expects cvc5.Solver, receives SolverInterface
- AttributeError: Z3 Solver lacks CVC5-specific methods
- Segmentation fault: Global state conflicts between solvers

**Test Execution Results**:
- Fixture tests: PASSING (expected - factory already works)
- Integration tests: FAILING (expected - BimodalSemantics not migrated)
- All failures intentional and documented

### Success Criteria Validation

- [x] test_bimodal_solver_interface.py created and failing
- [x] test_solver_equivalence.py created and failing
- [x] test_performance_validation.py created and failing
- [x] Test fixtures created
- [x] All tests documented
- [x] RED state verified (tests fail as expected)

**Total Deliverables**: 1,087 lines of code, 40 test cases

---

**Stage 1 Status**: ✅ **COMPLETE** (2025-10-03)
**Previous Stage**: N/A (First stage)
**Next Stage**: [Stage 2: Semantic Core Migration](stage02_semantic_core_migration.md)
