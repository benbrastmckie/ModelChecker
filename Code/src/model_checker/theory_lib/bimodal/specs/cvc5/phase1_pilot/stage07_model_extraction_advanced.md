# Stage 7: Model Extraction Advanced

## Metadata
- **Stage**: 7/12 | **Est. Duration**: 1 hour (may be faster with Stage 6 patterns)
- **Complexity**: Medium (builds on Stage 6)
- **Dependencies**: Stage 6 (core extraction)
- **Files**: `semantic.py` (lines ~1310-1400)
- **Coverage Target**: >85%

## Objective

Complete model extraction by migrating advanced helper methods for time intervals, world histories, and time-shift relations.

## Actual Methods to Migrate

Based on code inspection:

1. **`_extract_time_intervals(all_worlds)`** - Extract world time intervals
2. **`_extract_world_histories(all_worlds, world_arrays, intervals)`** - Build time→state mappings
3. **`_extract_time_shift_relations(all_worlds, world_histories)`** - Identify shifted worlds

**Scope**: Complete the extraction pipeline started in Stage 6.

## CVC5 Patterns Established (Stage 6)

From Stage 6, we know:
- No separate `model` parameter - use `self.solver`
- `solver.getValue(term)` for extraction
- `.getBooleanValue()` for booleans
- `.getIntegerValue()` for integers

**New Pattern for Stage 7**: Array element extraction

```python
# Extract array[index]
index_term = self.solver.mkInteger(index)
array_element = self.solver.mkTerm(Kind.SELECT, array, index_term)
value = self.solver.getValue(array_element)
```

## Implementation Tasks

### Task 1: TDD - Write Tests First (RED State)
**Duration**: 15 minutes

```python
def test_extract_time_intervals_returns_dict(self):
    """Test _extract_time_intervals returns world_id → (start, end) dict."""
    # Set up satisfiable world with interval
    # ...
    result = self.solver.checkSat()
    self.assertTrue(result.isSat())

    world_ids = [0, 1]
    intervals = self.semantics._extract_time_intervals(world_ids)

    self.assertIsInstance(intervals, dict)
    self.assertIn(0, intervals)
    # Each interval is (start, end) tuple
    self.assertIsInstance(intervals[0], tuple)

def test_extract_world_histories_builds_time_state_map(self):
    """Test _extract_world_histories builds {world: {time: state}} mapping."""
    # ...
```

### Task 2: Migrate `_extract_time_intervals()`
**Duration**: 15 minutes

**Pattern**:
```python
def _extract_time_intervals(self, all_worlds):
    """Extract time intervals for each world from CVC5 solver.

    Args:
        all_worlds: List of valid world IDs

    Returns:
        dict: {world_id: (start_time, end_time)}
    """
    world_time_intervals = {}

    for world_id in all_worlds:
        # Create terms for interval functions
        world_id_term = self.solver.mkInteger(world_id)
        start_term = self.solver.mkTerm(Kind.APPLY_UF, self.world_interval_start, world_id_term)
        end_term = self.solver.mkTerm(Kind.APPLY_UF, self.world_interval_end, world_id_term)

        # Extract integer values
        start_value = self.solver.getValue(start_term)
        end_value = self.solver.getValue(end_term)

        start_int = start_value.getIntegerValue()
        end_int = end_value.getIntegerValue()

        world_time_intervals[world_id] = (start_int, end_int)

    return world_time_intervals
```

**Apply Patterns**:
- APPLY_UF for `world_interval_start/end` (Stage 5 pattern)
- `getIntegerValue()` for extraction

### Task 3: Migrate `_extract_world_histories()`
**Duration**: 20 minutes

**Key Challenge**: Extracting array values (world states at each time)

**Pattern**:
```python
def _extract_world_histories(self, all_worlds, world_arrays, world_time_intervals):
    """Build time→state mappings for each world.

    Args:
        all_worlds: List of valid world IDs
        world_arrays: Dict of world_id → array terms
        world_time_intervals: Dict of world_id → (start, end)

    Returns:
        dict: {world_id: {time: bitvector_state}}
    """
    world_histories = {}

    for world_id in all_worlds:
        if world_id not in world_arrays or world_id not in world_time_intervals:
            continue

        array = world_arrays[world_id]
        start, end = world_time_intervals[world_id]

        history = {}
        for time in range(start, end + 1):
            # Extract array[time] using SELECT
            time_term = self.solver.mkInteger(time)
            state_term = self.solver.mkTerm(Kind.SELECT, array, time_term)

            # Get BitVector value
            state_value = self.solver.getValue(state_term)

            # Extract as BitVector or integer (check CVC5 API)
            # May need: state_value.getBitVectorValue() or similar
            history[time] = state_value

        world_histories[world_id] = history

    return world_histories
```

**Note**: BitVector extraction may need special handling. Test and adapt.

### Task 4: Migrate `_extract_time_shift_relations()` (if time permits)
**Duration**: 10 minutes

**Pattern**: Similar to above - extract boolean values for shift predicates

**Adaptive**: If complex, skip and mark stage complete without this method.

### Task 5: Test Integration
**Duration**: 10 minutes

- [ ] Run all Stage 7 tests
- [ ] Verify GREEN state
- [ ] Test end-to-end: checkSat → extract_model_elements

### Task 6: Coverage and Commit
**Duration**: 10 minutes

- [ ] Check coverage >85%
- [ ] Refactor
- [ ] Commit

## Success Criteria Checklist

- [ ] Time intervals extract correctly (start, end tuples)
- [ ] World histories build time→state mappings
- [ ] Array element extraction works (SELECT + getValue)
- [ ] All tests pass
- [ ] Coverage >85%
- [ ] Ready for Stage 8 (operators)

## Common Issues & Solutions

### Issue: BitVector value extraction

**Cause**: CVC5 BitVector API differs from Z3

**Solution**: Check CVC5 documentation for Term methods:
```python
# Possible methods (check actual API):
state_value.getBitVectorValue()  # Returns string representation
# OR
state_value.toPythonObj()  # May convert to int
```

**Fallback**: Extract as integer if BitVector methods unclear

### Issue: Array values not in model

**Cause**: Array element not constrained

**Solution**: Wrap in try/except:
```python
try:
    state_value = self.solver.getValue(state_term)
    history[time] = state_value
except Exception:
    # Skip unconstrained array element
    pass
```

## Adaptive Scoping

**Minimum Viable**: Migrate `_extract_time_intervals()` only. This is concrete and testable.

**Stretch Goal**: Complete all extraction helpers.

**Don't Block**: If BitVectors are problematic, extract as much as possible and mark remaining as "TODO: CVC5 BitVector extraction".

---

**Stage 7 Status**: ☐ Not Started | ☐ In Progress | ☑ Complete

## Completion Summary

**Date**: 2025-10-03
**Commit**: a6b89afe
**Duration**: ~30 minutes (faster than 1h estimate)

### Migrated Methods
- ✅ `_extract_world_arrays()` - World function array extraction
- ✅ `_extract_time_intervals()` - Time interval extraction (start, end)

### Tests
- 7/7 tests passing (100%)
- All tests verify CVC5 API usage (APPLY_UF, getValue(), getIntegerValue())
- No Z3 dependencies remain in migrated code

### Key Patterns Applied
1. Function application: `mkTerm(Kind.APPLY_UF, world_function, world_id_term)`
2. Integer extraction: `getValue(term).getIntegerValue()` instead of `.as_long()`
3. Exception handling: Generic `Exception` instead of `z3.Z3Exception`
4. No model parameter: Extract directly from `self.solver`

### Deferred Work (Adaptive Scoping)
Per plan's adaptive scoping strategy, the following methods were **not** migrated in Stage 7:
- `_extract_world_histories()` - Requires BitVector extraction patterns
- `safe_select()` - Z3-specific array helper
- `_extract_time_shift_relations()` - Requires shift relation pattern

**Rationale**: Focus on concrete, testable methods first. BitVector extraction and world histories involve complex patterns that need more investigation. These can be addressed when needed for full model extraction or deferred to later stages.

### Sub-Phase 1.1 Status
**COMPLETE**: All semantic core stages (1-7) finished!
- Ready to proceed to Stage 8: Primitive Operators
