# Stage 1: BimodalSemantics Core Setup

## Metadata
- **Stage**: 1 of 12 (Phase 1 - Bimodal CVC5 Pilot)
- **Estimated Duration**: 1.5 hours
- **Complexity**: Medium
- **Dependencies**: None (foundation stage)
- **Files Modified**: `semantic/semantic.py` (lines 30-223)
- **Lines of Code**: 193 lines
- **Test Coverage Target**: >85%

## Objective

Initialize the BimodalSemantics class foundation with CVC5, including:
- Import statements (Z3 → CVC5)
- Class initialization
- Sort definitions (Bool, Int, BitVec, Array, Function sorts)
- Primitive function declarations
- Witness registry initialization

**Success Criteria**: BimodalSemantics instance can be created with CVC5 solver, all sorts and primitives are accessible.

## Current State (Z3)

**File**: `Code/src/model_checker/theory_lib/bimodal/semantic/semantic.py`
**Lines**: 30-223

```python
import z3
from typing import Dict, List, Optional

class BimodalSemantics:
    def __init__(self, N: int, T_max: int):
        # Z3-specific initialization
        self.solver = z3.Solver()

        # Sort definitions using Z3
        self.BoolSort = z3.BoolSort()
        self.IntSort = z3.IntSort()
        self.WorldSort = z3.BitVecSort(N)
        self.TimeSort = z3.IntSort()

        # Function declarations using Z3
        self.V = z3.Function('V', self.WorldSort, self.TimeSort, z3.BoolSort())
        self.R = z3.Function('R', self.WorldSort, self.WorldSort, z3.BoolSort())
        # ... more functions
```

## Target State (CVC5)

**File**: `Code/src/model_checker/theory_lib/bimodal/semantic/semantic.py`
**Lines**: 30-223

```python
import cvc5
from cvc5 import Kind
from typing import Dict, List, Optional

class BimodalSemantics:
    def __init__(self, N: int, T_max: int, solver: cvc5.Solver):
        # CVC5 solver (passed in, not created here)
        self.solver = solver

        # Sort definitions using CVC5
        self.BoolSort = solver.getBooleanSort()
        self.IntSort = solver.getIntegerSort()
        self.WorldSort = solver.mkBitVectorSort(N)
        self.TimeSort = solver.getIntegerSort()

        # Function declarations using CVC5
        v_sort = solver.mkFunctionSort([self.WorldSort, self.TimeSort], self.BoolSort)
        self.V = solver.mkConst(v_sort, 'V')

        r_sort = solver.mkFunctionSort([self.WorldSort, self.WorldSort], self.BoolSort)
        self.R = solver.mkConst(r_sort, 'R')
        # ... more functions
```

## Z3→CVC5 Translation Patterns

### 1. Import Statements
```python
# Z3
import z3

# CVC5
import cvc5
from cvc5 import Kind
```

### 2. Solver Initialization
```python
# Z3 (created internally)
self.solver = z3.Solver()

# CVC5 (passed as parameter)
def __init__(self, N: int, T_max: int, solver: cvc5.Solver):
    self.solver = solver
```

### 3. Sort Definitions
```python
# Z3
self.BoolSort = z3.BoolSort()
self.IntSort = z3.IntSort()
self.WorldSort = z3.BitVecSort(N)

# CVC5
self.BoolSort = solver.getBooleanSort()
self.IntSort = solver.getIntegerSort()
self.WorldSort = solver.mkBitVectorSort(N)
```

### 4. Function Declarations
```python
# Z3 (simple)
self.V = z3.Function('V', z3.BitVecSort(N), z3.IntSort(), z3.BoolSort())

# CVC5 (two-step)
v_sort = solver.mkFunctionSort([self.WorldSort, self.TimeSort], self.BoolSort)
self.V = solver.mkConst(v_sort, 'V')
```

### 5. Array Sorts
```python
# Z3
self.WorldArray = z3.ArraySort(z3.IntSort(), z3.BitVecSort(N))

# CVC5
self.WorldArray = solver.mkArraySort(self.IntSort, self.WorldSort)
```

## Implementation Tasks

### Task 1: TDD - Write Test First (RED State)
**Duration**: 20 minutes

- [ ] Create test file: `tests/unit/test_semantic_cvc5_stage01.py`
- [ ] Import cvc5 and test framework
- [ ] Write test for BimodalSemantics initialization with CVC5
- [ ] Write test for sort definitions
- [ ] Write test for primitive function declarations
- [ ] Run tests - verify they FAIL (semantic.py still uses Z3)

**Test Structure**:
```python
import unittest
import cvc5
from cvc5 import Kind
from model_checker.theory_lib.bimodal.semantic.semantic import BimodalSemantics

class TestBimodalSemanticsCVC5Stage01(unittest.TestCase):
    def setUp(self):
        """Set up CVC5 solver for tests."""
        self.solver = cvc5.Solver()
        self.solver.setLogic("ALL")
        self.solver.setOption("produce-models", "true")
        self.solver.setOption("mbqi", "true")
        self.solver.setOption("enum-inst", "true")

    def test_bimodal_semantics_initialization(self):
        """Test BimodalSemantics initializes with CVC5 solver."""
        N = 3
        T_max = 10
        semantics = BimodalSemantics(N, T_max, self.solver)

        self.assertIsNotNone(semantics)
        self.assertEqual(semantics.solver, self.solver)

    def test_sort_definitions(self):
        """Test all sorts defined correctly with CVC5."""
        semantics = BimodalSemantics(3, 10, self.solver)

        # Verify sorts exist
        self.assertIsNotNone(semantics.BoolSort)
        self.assertIsNotNone(semantics.IntSort)
        self.assertIsNotNone(semantics.WorldSort)
        self.assertIsNotNone(semantics.TimeSort)

    def test_function_declarations(self):
        """Test primitive functions declared with CVC5."""
        semantics = BimodalSemantics(3, 10, self.solver)

        # Verify functions exist and are CVC5 Terms
        self.assertIsNotNone(semantics.V)
        self.assertIsNotNone(semantics.R)
        # Check they are CVC5 Terms (not Z3 objects)
        self.assertIsInstance(semantics.V, cvc5.Term)
```

### Task 2: Update Import Statements
**Duration**: 5 minutes

- [ ] Replace `import z3` with `import cvc5`
- [ ] Add `from cvc5 import Kind`
- [ ] Keep typing imports unchanged
- [ ] Verify no other Z3 imports in this section

### Task 3: Update Class Initialization
**Duration**: 10 minutes

- [ ] Change `__init__` signature to accept `solver: cvc5.Solver`
- [ ] Remove internal `z3.Solver()` creation
- [ ] Store passed solver: `self.solver = solver`
- [ ] Update docstring to reflect CVC5 usage

### Task 4: Migrate Sort Definitions
**Duration**: 15 minutes

- [ ] Replace `z3.BoolSort()` → `solver.getBooleanSort()`
- [ ] Replace `z3.IntSort()` → `solver.getIntegerSort()`
- [ ] Replace `z3.BitVecSort(N)` → `solver.mkBitVectorSort(N)`
- [ ] Update array sorts: `z3.ArraySort()` → `solver.mkArraySort()`
- [ ] Store all sorts as instance variables

**Critical**: Note argument changes for BitVec operations later (Stage 6).

### Task 5: Migrate Function Declarations
**Duration**: 30 minutes

- [ ] Identify all `z3.Function()` calls in lines 30-223
- [ ] For each function:
  - Create function sort using `solver.mkFunctionSort([domain_sorts], range_sort)`
  - Create constant using `solver.mkConst(function_sort, name)`
- [ ] Update primitive functions: V, R, S_past, S_future, etc.
- [ ] Maintain same variable names for compatibility

**Pattern**:
```python
# Z3
self.V = z3.Function('V', WorldSort, TimeSort, BoolSort)

# CVC5
v_sort = self.solver.mkFunctionSort([self.WorldSort, self.TimeSort], self.BoolSort)
self.V = self.solver.mkConst(v_sort, 'V')
```

### Task 6: Initialize Witness Registry
**Duration**: 10 minutes

- [ ] Locate witness registry initialization (if in lines 30-223)
- [ ] Update to use CVC5 if needed
- [ ] Ensure witness registry aware of CVC5 solver

### Task 7: Run Tests (GREEN State)
**Duration**: 5 minutes

- [ ] Run `test_semantic_cvc5_stage01.py`
- [ ] Verify all tests PASS
- [ ] Check for any CVC5-specific errors
- [ ] Validate sort and function types

**Test Command**:
```bash
PYTHONPATH=Code/src pytest Code/src/model_checker/theory_lib/bimodal/tests/unit/test_semantic_cvc5_stage01.py -v
```

### Task 8: Refactor and Code Quality
**Duration**: 10 minutes

- [ ] Add inline comments explaining CVC5 patterns
- [ ] Ensure no decorators (CODE_STANDARDS.md compliance)
- [ ] Use relative imports for local modules
- [ ] Clean up any temporary variables
- [ ] Ensure user-friendly error messages

### Task 9: Coverage Check
**Duration**: 5 minutes

- [ ] Run coverage analysis for this stage
- [ ] Target: >85% coverage for modified lines
- [ ] Identify any untested paths
- [ ] Add tests if coverage < 85%

**Coverage Command**:
```bash
PYTHONPATH=Code/src pytest Code/src/model_checker/theory_lib/bimodal/tests/unit/test_semantic_cvc5_stage01.py \
    --cov=model_checker.theory_lib.bimodal.semantic.semantic \
    --cov-report=term-missing
```

### Task 10: Update Documentation and Commit
**Duration**: 10 minutes

- [ ] Update this stage plan with completion checkboxes
- [ ] Mark Stage 1 complete in STAGE_INDEX.md
- [ ] Update Phase 1 plan progress
- [ ] Create git commit with structured message

**Commit Message Template**:
```
feat(phase1-stage01): BimodalSemantics core setup with CVC5

Migrated BimodalSemantics initialization, sorts, and primitive
functions from Z3 to CVC5 API.

Changes:
- Updated imports: z3 → cvc5
- Modified __init__ to accept CVC5 solver parameter
- Migrated sort definitions to CVC5 API
- Migrated function declarations to two-step CVC5 pattern
- All tests passing with >85% coverage

Stage: 1/12 (Phase 1 - Bimodal CVC5 Pilot)
Tests: 5/5 passing
Coverage: 87%
Duration: 1.5 hours
Plan: bimodal/specs/cvc5/phase1_pilot/stage01_core_setup.md

Co-Authored-By: Claude <noreply@anthropic.com>
```

## Testing Strategy

### Unit Tests (test_semantic_cvc5_stage01.py)

**Test Cases**:
1. `test_bimodal_semantics_initialization` - Verify class creates with CVC5
2. `test_sort_definitions` - Verify all sorts created correctly
3. `test_function_declarations` - Verify all primitives are CVC5 Terms
4. `test_witness_registry_initialization` - Verify registry initialized
5. `test_solver_configuration` - Verify CVC5 solver has MBQI+enum-inst

**Assertions**:
- Sorts are CVC5 Sort objects
- Functions are CVC5 Term objects
- No Z3 objects remain
- Solver properly configured

### Integration Validation

**After Stage 1**:
- BimodalSemantics can be instantiated with CVC5
- All instance variables populated
- No runtime errors
- Ready for Stage 2 (quantifier helpers)

## Success Criteria Checklist

- [ ] All imports updated (Z3 → CVC5)
- [ ] __init__ accepts CVC5 solver parameter
- [ ] All sort definitions use CVC5 API
- [ ] All function declarations use CVC5 two-step pattern
- [ ] Witness registry initialized (if applicable)
- [ ] All tests written BEFORE code changes
- [ ] All tests passing (GREEN state)
- [ ] Coverage >85% for modified code
- [ ] Code refactored for quality
- [ ] No decorators used
- [ ] Relative imports for local modules
- [ ] Git commit created
- [ ] Stage plan updated
- [ ] STAGE_INDEX.md updated
- [ ] Ready for Stage 2

## Risk Mitigation

### Risk 1: Function Declaration Complexity
**Risk**: CVC5's two-step function declaration more verbose than Z3
**Mitigation**: Create helper method if many functions
**Fallback**: Accept verbosity, document pattern clearly

### Risk 2: Sort Mismatches
**Risk**: CVC5 sort requirements differ from Z3
**Mitigation**: Validate sorts in tests
**Fallback**: Adjust sort definitions as needed

### Risk 3: Solver Parameter Threading
**Risk**: Need to thread solver through all method calls
**Mitigation**: Store solver as instance variable
**Fallback**: Design decision for future stages

## Dependencies for Next Stage

**Stage 2 Requirements**:
- BimodalSemantics initialized with CVC5
- All sorts accessible (especially BoolSort, IntSort, WorldSort, TimeSort)
- Solver instance available for quantifier creation
- No Z3 dependencies remaining in core setup

## Notes

### API Translation Learnings
- CVC5 requires solver instance for sort creation (Z3 has global functions)
- Function declarations are two-step: mkFunctionSort + mkConst
- Array sorts use different argument order
- All sorts obtained from solver, not global module

### Time Tracking
- Actual duration: ~1.5 hours
- Variance from estimate: On target
- Lessons for future estimates: Test-first approach worked well. Creating minimal test helper was key.

### Blockers Encountered
- **AtomSort dependency**: syntactic.AtomSort is Z3-based. Created local CVC5 AtomSort_cvc5 as workaround.
- **Full __init__ calls unmigrated methods**: Tests use `_create_minimal_semantics()` helper to bypass build_frame_constraints() and define_invalidity() which will be migrated in Stages 4-10.
- **Z3 import kept temporarily**: Type hints in later methods reference z3. Will remove in Stage 10.

---

**Stage 1 Status**: ☑ Complete
**Completion Date**: 2025-10-02
**Completed By**: Claude Code (with human guidance)
**Commit**: bceb98d0
