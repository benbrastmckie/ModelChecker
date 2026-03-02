# Stage 4: Examples & Iteration Migration

## Metadata
- **Stage**: 4/6 (Phase 3 - Bimodal Abstraction Integration)
- **Estimated Duration**: 0.5 days (4 hours)
- **Complexity**: Medium
- **Dependencies**: Stage 3 complete (operators & witness migrated)
- **Files**:
  - `examples.py` (671 lines) - MODIFY
  - `iterate.py` (602 lines) - MODIFY
  - Settings configuration - UPDATE
- **Coverage Target**: >85% maintained
- **Risk**: Low - Entry points and iteration logic

## Objective

Complete bimodal theory migration by updating examples.py (entry point) and iterate.py (model iteration) to use SolverInterface. Enable runtime solver selection via settings.

**Success Criteria**:
- examples.py uses SolverFactory for solver creation
- iterate.py uses SolverInterface methods
- Runtime solver selection works via `settings.smt_solver`
- All 22 examples work with both Z3 and CVC5
- Integration tests fully passing (GREEN state achieved)

## Implementation Tasks

### Task 1: Migrate examples.py Imports
**Duration**: 30 minutes

- [ ] Remove CVC5 imports: `import cvc5`
- [ ] Add factory imports: `from model_checker.solver import SolverFactory`
- [ ] Add settings imports: `from model_checker.settings import settings`
- [ ] Update example imports if needed

**Before**:
```python
import cvc5
```

**After**:
```python
from model_checker.solver import SolverFactory
from model_checker.settings import settings
```

### Task 2: Update Solver Creation in examples.py
**Duration**: 1 hour

- [ ] Replace direct CVC5 solver creation with factory
- [ ] Load solver choice from settings: `settings.smt_solver`
- [ ] Remove manual MBQI+enum-inst configuration (adapter handles)
- [ ] Create adapter once, reuse for all examples

**Before**:
```python
def run_examples():
    solver = cvc5.Solver()
    solver.setLogic("ALL")
    solver.setOption("produce-models", "true")
    solver.setOption("mbqi", "true")  # CRITICAL
    solver.setOption("enum-inst", "true")  # CRITICAL
    # ... run examples
```

**After**:
```python
def run_examples():
    factory = SolverFactory()
    adapter = factory.create(settings.smt_solver)  # "z3" or "cvc5"
    solver = adapter.create_solver()
    # Adapter auto-configures MBQI+enum-inst for CVC5
    # ... run examples with adapter
```

### Task 3: Update Example Execution with Adapter
**Duration**: 1 hour

- [ ] Pass adapter to semantic definition functions
- [ ] Pass adapter to operator functions
- [ ] Update all solver operations to use adapter methods
- [ ] Ensure solver instance passed correctly

**Pattern**:
```python
# Before:
result = define_bimodal_semantics(solver)
check = solver.checkSat()

# After:
result = define_bimodal_semantics(adapter)
check = adapter.check_sat(solver)
```

### Task 4: Migrate iterate.py
**Duration**: 1 hour

- [ ] Add adapter parameter to `iterate_models()` function
- [ ] Update function signature: `iterate_models(adapter: SolverInterface, solver)`
- [ ] Replace `solver.checkSat()` with `adapter.check_sat(solver)`
- [ ] Replace `solver.getModel()` with `adapter.get_model(solver)`
- [ ] Update result checking: `isSat()` → `== "sat"`

**Before**:
```python
def iterate_models(solver):
    result = solver.checkSat()
    if result.isSat():
        model = solver.getModel()
        # Extract values...
```

**After**:
```python
def iterate_models(adapter: SolverInterface, solver):
    result = adapter.check_sat(solver)
    if result == "sat":
        model = adapter.get_model(solver)
        # Extract values using adapter...
```

### Task 5: Configure Settings for Testing
**Duration**: 30 minutes

- [ ] Set default: `settings.smt_solver = "cvc5"` for Phase 3
- [ ] Document how to switch: `SMT_SOLVER=z3 ./dev_cli.py ...`
- [ ] Test environment variable override works
- [ ] Verify settings loaded correctly

**Settings Test**:
```python
# Test settings loading
from model_checker.settings import settings
print(f"Current solver: {settings.smt_solver}")

# Override via environment
import os
os.environ['SMT_SOLVER'] = 'z3'
# Reload settings...
```

### Task 6: Run All Examples with CVC5
**Duration**: 30 minutes

- [ ] Execute: `./dev_cli.py bimodal/examples.py` with CVC5
- [ ] Verify all 22 examples work
- [ ] Validate 6 critical examples solve correctly (BM_CM_*, TN_CM_*, MD_CM_*)
- [ ] Check performance: BM_CM_* should solve in ~6ms

**Testing Command**:
```bash
cd Code
PYTHONPATH=src SMT_SOLVER=cvc5 ./dev_cli.py src/model_checker/theory_lib/bimodal/examples.py

# Expected: All 22 examples solve, 6 critical examples ~6ms
```

### Task 7: Run All Examples with Z3 (Regression)
**Duration**: 30 minutes

- [ ] Execute: `./dev_cli.py bimodal/examples.py` with Z3
- [ ] Verify all 22 examples work (backward compatibility)
- [ ] Document any Z3-specific timeouts (expected from Phase 1)
- [ ] Confirm no new regressions

**Testing Command**:
```bash
cd Code
PYTHONPATH=src SMT_SOLVER=z3 ./dev_cli.py src/model_checker/theory_lib/bimodal/examples.py

# Expected: All examples work (some may timeout as in Phase 0 baseline)
```

## Testing Strategy

**Integration Tests - Should All Pass Now (GREEN)**:
```bash
# Integration tests written in Stage 1 should now pass
PYTHONPATH=Code/src pytest Code/src/model_checker/theory_lib/bimodal/tests/integration/test_bimodal_solver_interface.py -v

# Expected: All tests PASS (GREEN state achieved)
```

**Example Execution - CVC5**:
```bash
cd Code
PYTHONPATH=src SMT_SOLVER=cvc5 ./dev_cli.py src/model_checker/theory_lib/bimodal/examples.py

# Verify output shows:
# - All 22 examples
# - BM_CM_1, BM_CM_2: sat (~6ms each)
# - TN_CM_2, TN_CM_3: sat (~0.2ms each)
# - MD_CM_*: sat (fast)
```

**Example Execution - Z3 (Regression)**:
```bash
cd Code
PYTHONPATH=src SMT_SOLVER=z3 ./dev_cli.py src/model_checker/theory_lib/bimodal/examples.py

# Expected: Same results as Z3 baseline (some timeouts OK)
```

**Unit Tests - Iteration**:
```bash
# Test iterate.py functionality
PYTHONPATH=Code/src pytest Code/src/model_checker/theory_lib/bimodal/tests/unit/test_iterate.py -v

# Expected: All tests pass with adapter
```

**Import Verification**:
```bash
# Ensure no direct CVC5 imports
grep -n "import cvc5" Code/src/model_checker/theory_lib/bimodal/examples.py
grep -n "import cvc5" Code/src/model_checker/theory_lib/bimodal/iterate.py

# Expected: No matches
```

**Settings Verification**:
```bash
# Test solver selection
PYTHONPATH=Code/src python3 -c "
from model_checker.settings import settings
from model_checker.solver import SolverFactory
import os

# Test CVC5
os.environ['SMT_SOLVER'] = 'cvc5'
factory = SolverFactory()
adapter = factory.create(settings.smt_solver)
print(f'CVC5 adapter: {adapter.__class__.__name__}')

# Test Z3
os.environ['SMT_SOLVER'] = 'z3'
adapter = factory.create('z3')
print(f'Z3 adapter: {adapter.__class__.__name__}')
"
```

## Success Criteria Checklist

- [ ] examples.py uses SolverFactory (no direct CVC5)
- [ ] iterate.py uses SolverInterface methods
- [ ] Settings-based solver selection works
- [ ] All 22 examples work with CVC5
- [ ] All 22 examples work with Z3
- [ ] 6 critical examples maintain performance (~6ms with CVC5)
- [ ] Integration tests all pass (GREEN state)
- [ ] No direct CVC5 imports remain
- [ ] Coverage >85% maintained

## Common Issues & Solutions

### Issue 1: Settings Not Loading
**Problem**: `settings.smt_solver` not recognized
**Cause**: Settings module not properly initialized
**Solution**: Verify Phase 2 settings integration complete, reload settings

### Issue 2: Factory Returns Wrong Adapter
**Problem**: Requesting "cvc5" but get Z3 adapter
**Cause**: Factory configuration issue or settings override
**Solution**: Check factory registration, verify settings value

### Issue 3: Examples Fail with "unknown"
**Problem**: CVC5 returns "unknown" on some examples
**Cause**: MBQI+enum-inst not configured by adapter
**Solution**: Verify adapter's `create_solver()` sets required options

### Issue 4: Result Checking Fails
**Problem**: `result == "sat"` doesn't work
**Cause**: Adapter returning non-standard result format
**Solution**: Verify adapter returns "sat"/"unsat"/"unknown" strings

### Issue 5: Performance Regression
**Problem**: Examples slower than Phase 1
**Cause**: Adapter overhead or incorrect configuration
**Solution**: Profile, verify MBQI settings, optimize hot paths

## Risk Mitigation

**Risk**: Examples fail due to incomplete migration
**Impact**: Cannot validate end-to-end functionality
**Mitigation**: Ensure Stages 2-3 fully complete before starting Stage 4

**Risk**: Settings override doesn't work
**Impact**: Cannot test dual-solver support
**Mitigation**: Test settings early, verify environment variable handling

**Risk**: Performance lost through abstraction
**Impact**: Slower than Phase 1 direct CVC5
**Mitigation**: Performance validation in Stage 5

## Dependencies for Next Stage

Stage 5 (Dual-Solver Validation) requires:
- ✅ examples.py fully migrated to SolverFactory
- ✅ iterate.py fully migrated to SolverInterface
- ✅ All 22 examples working with both solvers
- ✅ Settings-based solver selection functional
- ✅ Integration tests passing (GREEN)

## Notes

**Settings Configuration**: The `settings.smt_solver` should default to "cvc5" for Phase 3 to validate abstraction with CVC5. Z3 validation comes in Stage 5.

**Integration Test Completion**: By end of Stage 4, all integration tests from Stage 1 should be GREEN (passing).

**Example Count**: 22 total bimodal examples - all must work with both solvers.

---

**Stage 4 Status**: ☐ Pending
**Previous Stage**: [Stage 3: Operators & Witness Migration](stage03_operators_witness_migration.md)
**Next Stage**: [Stage 5: Dual-Solver Validation](stage05_dual_solver_validation.md)
