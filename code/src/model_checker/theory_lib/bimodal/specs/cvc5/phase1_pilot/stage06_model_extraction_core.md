# Stage 6: Model Extraction Core

## Metadata
- **Stage**: 6/12 | **Est. Duration**: 1.5 hours (conservative, may be faster)
- **Complexity**: Medium (new CVC5 API, but straightforward pattern)
- **Dependencies**: Stage 1 (sorts), Stage 4 (helper methods)
- **Files**: `semantic.py` (lines ~1212-1340)
- **Coverage Target**: >85%

## Objective

Migrate core model extraction methods from Z3's `model.eval()` API to CVC5's `solver.getValue()` API.

**Key Insight**: CVC5 extracts values directly from solver after checkSat(), not from separate model object.

## Actual Methods to Migrate

Based on code inspection (semantic.py:1212-1340):

### Primary Methods (migrate these)
1. **`extract_model_elements(z3_model)`** (line 1212) - Main extraction coordinator
2. **`_extract_valid_world_ids(z3_model)`** (line 1260) - Extract world IDs using is_world()
3. **`_extract_world_arrays(z3_model, all_worlds)`** (line 1291) - Extract world arrays
4. **`_extract_time_intervals(z3_model, all_worlds)`** (line ~1310) - Extract time intervals

**Scope Note**: Focus on simple value extraction. Skip complex methods if dependencies not ready.

## Z3 → CVC5 Pattern: Model Extraction

### Z3 Pattern
```python
def extract_method(self, z3_model):
    # Get model object from solver
    value = z3_model.eval(term, model_completion=True)

    # Check truth value
    if z3.is_true(value):
        return True

    # Extract integer
    int_val = value.as_long()
```

### CVC5 Pattern
```python
def extract_method(self):
    # No separate model object - extract from solver directly
    # Assumes solver.checkSat() returned isSat()

    value = self.solver.getValue(term)

    # Check truth value (Boolean terms)
    if value.getBooleanValue():
        return True

    # Extract integer
    int_val = value.getIntegerValue()
```

**CRITICAL DIFFERENCES**:
1. No separate `model` parameter - use `self.solver` directly
2. Call `getValue(term)` instead of `model.eval(term)`
3. Use `getBooleanValue()` / `getIntegerValue()` instead of `z3.is_true()` / `.as_long()`
4. **MUST call checkSat() and verify isSat() BEFORE calling getValue()**

## Implementation Tasks

### Task 1: TDD - Write Tests First (RED State)
**Duration**: 20 minutes

```python
class TestModelExtractionCVC5Stage06(unittest.TestCase):
    def setUp(self):
        self.solver = cvc5.Solver()
        self.solver.setLogic("ALL")
        self.solver.setOption("produce-models", "true")
        # ... setup minimal semantics ...

    def test_extract_valid_world_ids_returns_list(self):
        """Test _extract_valid_world_ids returns list of ints."""
        # Set up satisfiable constraints
        # ...
        result = self.solver.checkSat()
        self.assertTrue(result.isSat())

        world_ids = self.semantics._extract_valid_world_ids()
        self.assertIsInstance(world_ids, list)

    def test_extract_uses_solver_get_value(self):
        """Test extraction uses solver.getValue(), not model.eval()."""
        # Ensure no z3.ModelRef used anywhere
        # ...
```

**Checklist**:
- [ ] Test for `_extract_valid_world_ids()` returning list
- [ ] Test for Boolean value extraction
- [ ] Test for integer value extraction
- [ ] Test for getValue() usage (not z3 model.eval)
- [ ] Run tests - verify ALL FAIL with expected errors

### Task 2: Update Method Signatures
**Duration**: 10 minutes

**Change**:
```python
# OLD Z3
def extract_model_elements(self, z3_model):
def _extract_valid_world_ids(self, z3_model):

# NEW CVC5
def extract_model_elements(self):
def _extract_valid_world_ids(self):
```

**Rationale**: CVC5 doesn't use separate model object. Extract from `self.solver` directly.

### Task 3: Migrate `_extract_valid_world_ids()`
**Duration**: 15 minutes

**Current Z3 (semantic.py:1260-1289)**:
```python
def _extract_valid_world_ids(self, z3_model):
    all_worlds = []
    for i in range(self.max_world_id):
        try:
            is_world_expr = self.is_world(i)
            is_valid_expr = z3_model.eval(is_world_expr)
            is_valid = z3.is_true(is_valid_expr)

            if is_valid:
                all_worlds.append(i)
        except z3.Z3Exception:
            continue
```

**Target CVC5**:
```python
def _extract_valid_world_ids(self):
    """Extract valid world IDs from CVC5 solver.

    Returns:
        list: List of valid world IDs
    """
    all_worlds = []
    for i in range(self.max_world_id):
        try:
            # Create is_world term (uses Stage 1 primitives)
            is_world_expr = self.is_world(i)

            # Extract value from CVC5 solver
            is_valid_term = self.solver.getValue(is_world_expr)
            is_valid = is_valid_term.getBooleanValue()

            if is_valid:
                all_worlds.append(i)
        except Exception:  # CVC5 may throw if term not in model
            continue

    # Ensure main world included
    if 0 not in all_worlds:
        all_worlds.append(0)

    return all_worlds
```

**Apply Patterns**:
- Remove `z3_model` parameter
- Replace `z3_model.eval()` with `self.solver.getValue()`
- Replace `z3.is_true()` with `.getBooleanValue()`
- Use generic `Exception` instead of `z3.Z3Exception`

### Task 4: Migrate `_extract_world_arrays()` (if time permits)
**Duration**: 20 minutes

**Pattern**:
```python
# OLD
array_value = z3_model.eval(self.world_function(world_id))

# NEW
world_id_term = self.solver.mkInteger(world_id)
array_term = self.solver.mkTerm(Kind.APPLY_UF, self.world_function, world_id_term)
array_value = self.solver.getValue(array_term)
```

**Note**: Array extraction may be complex. Start simple, test incrementally.

### Task 5: Migrate `extract_model_elements()` coordinator
**Duration**: 15 minutes

**Pattern**:
```python
def extract_model_elements(self):
    """Extract all model elements from CVC5 solver.

    MUST be called after solver.checkSat() returns isSat().

    Returns:
        Tuple: (world_histories, main_world_history, world_arrays, time_shift_relations)
    """
    # Call migrated helper methods (no model parameter)
    all_worlds = self._extract_valid_world_ids()
    world_arrays = self._extract_world_arrays(all_worlds)
    # ... etc
```

### Task 6: Test Integration
**Duration**: 10 minutes

- [ ] Run all Stage 6 tests
- [ ] Verify GREEN state (all tests pass)
- [ ] Test with satisfiable constraints (need checkSat() first)

### Task 7: Coverage and Commit
**Duration**: 10 minutes

- [ ] Check coverage >85%
- [ ] Refactor for clarity
- [ ] Create git commit

## Success Criteria Checklist

- [ ] No `z3_model` parameters remain
- [ ] All extraction uses `self.solver.getValue()`
- [ ] Boolean extraction uses `.getBooleanValue()`
- [ ] Integer extraction uses `.getIntegerValue()` (if needed)
- [ ] Tests pass with satisfiable constraints
- [ ] Coverage >85%
- [ ] Ready for Stage 7 (advanced extraction)

## Common Issues & Solutions

### Issue: "Cannot get value for term not in model"

**Cause**: Trying to extract value before checkSat() or for unconstrained term

**Solution**:
```python
# MUST call checkSat first
result = self.solver.checkSat()
if result.isSat():
    value = self.solver.getValue(term)
```

### Issue: Array value extraction

**Cause**: CVC5 array values are not simple Python objects

**Solution**: Extract array elements individually:
```python
for time in range(start, end+1):
    time_term = self.solver.mkInteger(time)
    array_term = self.solver.mkTerm(Kind.SELECT, array, time_term)
    value = self.solver.getValue(array_term)
```

## Adaptive Scoping

**If extraction is complex**: Focus on `_extract_valid_world_ids()` only. This is the simplest and most testable method. Mark stage as "complete (partial)" and continue.

**Don't block**: If arrays/intervals are difficult, skip them. They can be migrated in Stage 7 or later.

---

**Stage 6 Status**: ☐ Not Started | ☐ In Progress | ☑ Complete

## Completion Summary

**Date**: 2025-10-03
**Commit**: aecebf33
**Duration**: ~45 minutes (faster than 1.5h estimate)

### Migrated Methods
- ✅ `_extract_valid_world_ids()` - Core extraction method migrated to CVC5

### Tests
- 6/6 tests passing (100%)
- All tests verify CVC5 API usage (getValue(), getBooleanValue())
- No Z3 dependencies remain in migrated code

### Key Patterns Applied
1. Function application: `mkTerm(Kind.APPLY_UF, is_world, world_id_term)`
2. Value extraction: `solver.getValue(term)` instead of `model.eval(term)`
3. Boolean conversion: `.getBooleanValue()` instead of `z3.is_true()`
4. Exception handling: Generic `Exception` instead of `z3.Z3Exception`
5. No model parameter: Extract directly from `self.solver`

### Deferred Work (Adaptive Scoping)
Per plan's adaptive scoping strategy, the following methods were **not** migrated in Stage 6:
- `_extract_world_arrays()` - Deferred to Stage 7
- `_extract_time_intervals()` - Deferred to Stage 7
- `_extract_world_histories()` - Deferred to Stage 7
- `_extract_time_shift_relations()` - Deferred to Stage 7

**Rationale**: Focus on most critical, self-contained method first. Other methods have dependencies that may need additional pattern development.
