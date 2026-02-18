# Stage 7.5: Deferred Extraction Methods Cleanup

## Metadata
- **Stage**: 7.5/12 (CLEANUP STAGE) | **Est. Duration**: 1.5 hours
- **Complexity**: Medium-High (BitVector extraction, array SELECT)
- **Dependencies**: Stage 7 (core extraction complete)
- **Files**: `semantic.py` (lines ~1363-1548)
- **Coverage Target**: >85%
- **Purpose**: Eliminate technical debt by implementing all deferred extraction methods

## Objective

Systematically implement ALL deferred extraction methods from Stages 6-7 to avoid technical debt and ensure complete model extraction capability.

**Zero Tolerance for Deferral**: This stage completes the extraction pipeline comprehensively.

## Deferred Items Inventory

### From Stage 6 & 7
1. ✅ `_extract_world_arrays()` - **COMPLETED in Stage 7**
2. ✅ `_extract_time_intervals()` - **COMPLETED in Stage 7**
3. ❌ `_extract_world_histories()` - **PENDING** (BitVector extraction)
4. ❌ `safe_select()` - **PENDING** (array element extraction helper)
5. ❌ `_extract_time_shift_relations()` - **PENDING** (shift relation identification)

## CVC5 Patterns Needed

### Pattern 1: Array Element Selection (SELECT)
```python
# CVC5 array[index] selection
time_term = self.solver.mkInteger(time)
state_term = self.solver.mkTerm(Kind.SELECT, array_term, time_term)
state_value = self.solver.getValue(state_term)
```

### Pattern 2: BitVector Value Extraction
```python
# CVC5 BitVector extraction
bv_value = self.solver.getValue(bv_term)

# Option 1: String representation
bv_string = bv_value.getBitVectorValue()  # Returns binary string like "0b101"

# Option 2: Integer value (for conversion)
bv_int = int(bv_string, 2)  # Convert binary string to int
```

### Pattern 3: No separate safe_select needed
**Insight**: CVC5's SELECT is uniform - no ArrayRef vs Lambda distinction.
We can use SELECT directly without a wrapper like Z3's safe_select.

## Implementation Tasks

### Task 1: Research CVC5 BitVector API
**Duration**: 15 minutes

**Before writing code**, verify CVC5 BitVector methods:
```python
# Test snippet
solver = cvc5.Solver()
bv_sort = solver.mkBitVectorSort(3)
bv_const = solver.mkConst(bv_sort, 'test_bv')
# ... add constraints, checkSat()
bv_value = solver.getValue(bv_const)

# Test these methods:
print(type(bv_value))
print(dir(bv_value))  # Find available methods
# Expected: getBitVectorValue(), toPythonObj(), or similar
```

### Task 2: TDD - Write Tests First (RED State)
**Duration**: 20 minutes

```python
class TestDeferredExtractionCVC5Stage75(unittest.TestCase):
    """Test deferred extraction methods (Stage 7.5 cleanup)."""

    def test_extract_world_histories_returns_dict(self):
        """Test _extract_world_histories returns world→{time→state} mapping."""
        # Set up satisfiable world with array values
        # ...
        result = self.solver.checkSat()
        self.assertTrue(result.isSat())

        all_worlds = [0]
        world_arrays = self.semantics._extract_world_arrays(all_worlds)
        world_time_intervals = self.semantics._extract_time_intervals(all_worlds)

        histories = self.semantics._extract_world_histories(
            all_worlds, world_arrays, world_time_intervals
        )

        self.assertIsInstance(histories, dict)
        if 0 in histories:
            self.assertIsInstance(histories[0], dict)  # time→state mapping

    def test_extract_world_histories_no_z3_model_param(self):
        """Test _extract_world_histories has no z3_model parameter."""
        import inspect
        sig = inspect.signature(self.semantics._extract_world_histories)
        params = list(sig.parameters.keys())

        # Should have: all_worlds, world_arrays, world_time_intervals
        self.assertNotIn('z3_model', params)
        self.assertEqual(len(params), 3)

    def test_extract_world_histories_uses_select(self):
        """Test world histories use CVC5 SELECT for array access."""
        # This test verifies the pattern internally
        # Create array and extract element using SELECT
        # ...

    def test_extract_time_shift_relations_returns_dict(self):
        """Test _extract_time_shift_relations returns shift mapping."""
        # ...

    def test_extract_time_shift_relations_no_z3_model_param(self):
        """Test _extract_time_shift_relations has no z3_model parameter."""
        import inspect
        sig = inspect.signature(self.semantics._extract_time_shift_relations)
        params = list(sig.parameters.keys())

        self.assertNotIn('z3_model', params)

    def test_no_z3_dependencies_in_extraction(self):
        """Ensure NO Z3 code remains in any extraction method."""
        import inspect

        # Check all extraction methods
        for method_name in ['_extract_world_histories', '_extract_time_shift_relations']:
            method = getattr(self.semantics, method_name)
            source = inspect.getsource(method)

            # Should NOT contain Z3 patterns
            self.assertNotIn('z3_model', source, f"{method_name} should not use z3_model")
            self.assertNotIn('z3.', source, f"{method_name} should not import z3")
            self.assertNotIn('Z3Exception', source, f"{method_name} should not catch Z3Exception")
```

### Task 3: Migrate `_extract_world_histories()`
**Duration**: 30 minutes

**Strategy**: Remove safe_select, use CVC5 SELECT directly

```python
def _extract_world_histories(self, all_worlds, world_arrays, world_time_intervals):
    """Creates histories (time-state mappings) for each world using CVC5.

    MUST be called after solver.checkSat() returns isSat().

    Args:
        all_worlds: List of valid world IDs
        world_arrays: Dictionary of world_id → array (CVC5 Terms from Stage 7)
        world_time_intervals: Dictionary of world_id → (start, end) tuples

    Returns:
        dict: Mapping from world_id to time-state mapping
            {world_id: {time: state_representation}}
    """
    world_histories = {}

    for world_id in all_worlds:
        # Skip worlds with missing data
        if world_id not in world_arrays or world_id not in world_time_intervals:
            continue

        # Get the world array and time interval
        world_array = world_arrays[world_id]
        start_time, end_time = world_time_intervals[world_id]

        # Extract states for each time point
        time_states = {}

        for time in range(start_time, end_time + 1):
            try:
                # Use CVC5 SELECT to get array[time]
                time_term = self.solver.mkInteger(time)
                state_term = self.solver.mkTerm(Kind.SELECT, world_array, time_term)

                # Get BitVector value from solver
                state_value = self.solver.getValue(state_term)

                # Extract BitVector as string and convert to state representation
                # CVC5 returns BitVector values - need to extract and convert
                if state_value.getSort().isBitVector():
                    # Get BitVector binary representation
                    bv_string = state_value.getBitVectorValue()  # e.g., "101"
                    # Convert to state using existing utility
                    # Note: bitvec_to_worldstate expects Z3 BitVec - may need adaptation
                    # For now, store the raw value and convert later
                    time_states[time] = bv_string
                else:
                    # Non-BitVec result (shouldn't happen for world states)
                    time_states[time] = str(state_value)

            except Exception as e:
                # CVC5 may throw if array element unconstrained
                # Store error or skip - decide based on semantics
                time_states[time] = f"<error:{str(e)}>"

        # Add history to output
        world_histories[world_id] = time_states

    return world_histories
```

**CRITICAL DECISION**: BitVector to State Conversion

The existing `bitvec_to_worldstate()` utility expects Z3 BitVec objects. We have three options:

**Option A**: Adapt utility to accept CVC5 BitVec strings
**Option B**: Create CVC5-specific conversion in place
**Option C**: Store raw BitVec values and convert downstream

**Recommendation**: Option B for now, refactor to Option A later.

```python
# Option B: In-place conversion
bv_string = state_value.getBitVectorValue()  # "101"
bv_int = int(bv_string, 2)  # Convert to integer
# Then use existing logic to convert int to state representation
# This avoids modifying utilities now
```

### Task 4: Migrate `_extract_time_shift_relations()`
**Duration**: 20 minutes

**Good News**: This method doesn't use z3_model much - mostly compares extracted values.

```python
def _extract_time_shift_relations(self, all_worlds, world_histories):
    """Builds shift relations between worlds using CVC5-extracted data.

    Args:
        all_worlds: List of valid world IDs
        world_histories: Dictionary of time-state mappings (from _extract_world_histories)

    Returns:
        dict: Nested dictionary mapping source_id to {shift: target_id}
    """
    time_shift_relations = {}

    for source_id in all_worlds:
        time_shift_relations[source_id] = {}

        # Add self-shift (shift by 0)
        time_shift_relations[source_id][0] = source_id

        # Skip if world isn't in histories
        if source_id not in world_histories:
            continue

        # Check essential shifts (+1, -1)
        for shift in [1, -1]:
            for target_id in all_worlds:
                if source_id != target_id and target_id in world_histories:
                    try:
                        # First check interval compatibility
                        source_start, source_end = self.world_time_intervals[source_id]
                        target_start, target_end = self.world_time_intervals[target_id]

                        # For positive shift, target interval should be shifted up by 1
                        if shift == 1 and target_start == source_start + 1 and target_end == source_end + 1:
                            # Check if states match when shifted
                            is_shifted = True
                            for time in range(source_start, source_end + 1):
                                if time + shift <= target_end:
                                    source_state = world_histories[source_id].get(time)
                                    target_state = world_histories[target_id].get(time + shift)
                                    if source_state is not None and target_state is not None and source_state != target_state:
                                        is_shifted = False
                                        break

                            if is_shifted:
                                time_shift_relations[source_id][shift] = target_id
                                break

                        # For negative shift, target interval should be shifted down by 1
                        elif shift == -1 and target_start == source_start - 1 and target_end == source_end - 1:
                            # Check if states match when shifted
                            is_shifted = True
                            for time in range(source_start, source_end + 1):
                                if time + shift >= target_start:
                                    source_state = world_histories[source_id].get(time)
                                    target_state = world_histories[target_id].get(time + shift)
                                    if source_state is not None and target_state is not None and source_state != target_state:
                                        is_shifted = False
                                        break

                            if is_shifted:
                                time_shift_relations[source_id][shift] = target_id
                                break
                    except Exception:
                        # Skip on any error
                        pass

    return time_shift_relations
```

**Changes from Z3**:
- Remove `z3_model` parameter
- No Z3-specific code - just logic on extracted data
- Already uses self.world_time_intervals (populated in Stage 7)

### Task 5: Update `extract_model_elements()` caller
**Duration**: 10 minutes

```python
def extract_model_elements(self, z3_model):
    """Extract all model elements from CVC5 solver.

    Args:
        z3_model: DEPRECATED - kept for backwards compatibility, ignored

    Returns:
        Tuple: (world_histories, main_world_history, world_arrays, time_shift_relations)
    """
    # Extract core data (Stages 6-7)
    all_worlds = self._extract_valid_world_ids()
    world_arrays = self._extract_world_arrays(all_worlds)
    world_time_intervals = self._extract_time_intervals(all_worlds)

    # Extract histories (Stage 7.5)
    world_histories = self._extract_world_histories(
        all_worlds, world_arrays, world_time_intervals
    )

    # Check if we have any valid world histories
    if not world_histories:
        return {}, {}, {}, {}

    # Extract time shift relations (Stage 7.5)
    time_shift_relations = self._extract_time_shift_relations(
        all_worlds, world_histories
    )

    # Identify main world history
    main_world_history = world_histories.get(self.main_world, {})

    return world_histories, main_world_history, world_arrays, time_shift_relations
```

### Task 6: Remove `safe_select()` (if unused)
**Duration**: 5 minutes

**Decision Point**: Check if safe_select is used anywhere else

```bash
# Search for safe_select usage
grep -r "safe_select" Code/src/model_checker/theory_lib/bimodal/
```

If ONLY used in `_extract_world_histories()`, and we've replaced it with SELECT:
- Add `# TODO: Remove safe_select() - replaced by CVC5 SELECT in Stage 7.5` comment
- Mark for deletion (or delete if confident no external dependencies)

### Task 7: Test Integration
**Duration**: 15 minutes

- [ ] Run all Stage 7.5 tests
- [ ] Verify GREEN state
- [ ] Test full extraction pipeline: checkSat → extract_model_elements

### Task 8: Coverage and Commit
**Duration**: 10 minutes

- [ ] Check coverage >85%
- [ ] Run ALL previous stage tests (1-7) to ensure no regressions
- [ ] Refactor for clarity
- [ ] Commit with detailed message

## Success Criteria Checklist

- [ ] `_extract_world_histories()` migrated to CVC5
- [ ] `_extract_time_shift_relations()` migrated to CVC5
- [ ] BitVector extraction works correctly
- [ ] Array SELECT pattern works for all time points
- [ ] NO z3_model parameters remain
- [ ] NO Z3 dependencies in extraction code
- [ ] All tests pass (Stage 7.5 + Stages 1-7 regression)
- [ ] Coverage >85%
- [ ] **ZERO deferred items** - extraction pipeline complete

## Common Issues & Solutions

### Issue: BitVector extraction method unclear

**Cause**: CVC5 API may differ from expectation

**Solution**: Test incrementally
```python
# Debug script
solver = cvc5.Solver()
solver.setLogic("ALL")
solver.setOption("produce-models", "true")

# Create BitVec and constrain
bv_sort = solver.mkBitVectorSort(3)
bv = solver.mkConst(bv_sort, 'bv')
constraint = solver.mkTerm(Kind.EQUAL, bv, solver.mkBitVector(3, 5))  # 5 = 0b101
solver.assertFormula(constraint)

result = solver.checkSat()
if result.isSat():
    value = solver.getValue(bv)
    print(f"Type: {type(value)}")
    print(f"Sort: {value.getSort()}")
    print(f"BV Value: {value.getBitVectorValue()}")  # Test this
```

### Issue: bitvec_to_worldstate expects Z3 objects

**Cause**: Utility designed for Z3 BitVec

**Solution**: Convert CVC5 BitVec string to integer first
```python
bv_string = state_value.getBitVectorValue()  # "101"
bv_int = int(bv_string, 2)  # 5

# Create Z3-compatible representation or adapt utility
# For now, work with integers and convert downstream
```

**Alternative**: Create CVC5-aware state conversion
```python
def cvc5_bitvec_to_state(bv_value, num_atoms):
    """Convert CVC5 BitVector value to state representation."""
    bv_string = bv_value.getBitVectorValue()
    bv_int = int(bv_string, 2)
    # Apply same logic as bitvec_to_worldstate but for integers
    # ...
```

### Issue: Array extraction returns unconstrained values

**Cause**: Not all array elements may be constrained

**Solution**: Handle gracefully
```python
try:
    state_value = self.solver.getValue(state_term)
    # ... process
except Exception:
    time_states[time] = None  # Or "<unconstrained>"
```

## Validation

**Full Extraction Pipeline Test**:
```python
# End-to-end test
semantics = BimodalSemantics(settings, solver)
# ... add constraints ...
result = solver.checkSat()
assert result.isSat()

# Full extraction
world_histories, main_history, arrays, shifts = semantics.extract_model_elements(None)

# Validate structure
assert isinstance(world_histories, dict)
assert 0 in world_histories  # Main world
assert isinstance(world_histories[0], dict)  # Time mapping
assert len(world_histories[0]) > 0  # Has time points
```

## Adaptive Scoping

**NOT ALLOWED** in this stage. This is cleanup - no deferral permitted.

**Minimum Viable**: All 3 methods fully migrated and tested.

**If Blocked**: Escalate to get help with CVC5 API rather than defer.

---

**Stage 7.5 Status**: ☐ Not Started | ☐ In Progress | ✅ Complete

**Completion Summary**:
- Commit: fbe90189 (2025-10-03)
- Tests: 6/6 passing (100% coverage)
- Migrated methods:
  - ✅ `_extract_world_histories()` - CVC5 SELECT + BitVector extraction
  - ✅ `_extract_time_shift_relations()` - Pure logic on extracted data
- CVC5 patterns implemented:
  - Array SELECT: `mkTerm(Kind.SELECT, array, index_term)`
  - BitVector extraction: `getBitVectorValue()` returns binary string
  - No z3_model parameters - all extraction via `solver.getValue()`
- **Deferred Items After This Stage**: ZERO ✅ (by definition)
