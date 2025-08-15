# Remove iteration_timeout Setting

**Spec ID**: SPEC-047
**Created**: 2025-08-15
**Status**: DRAFT
**Priority**: P1
**Effort**: 3 hours
**Risk**: Medium
**Depends on**: SPEC-046 (Model 1 Timeout Handling)

## Executive Summary

Remove the `iteration_timeout` setting entirely and use `max_time` for all timeout purposes. This simplifies the timeout system by having a single, consistent timeout value for all operations.

## Motivation

Currently we have two timeout settings:
- `max_time`: Solver timeout (in seconds)
- `iteration_timeout`: Per-model search timeout during iteration

This creates confusion:
- Users must understand and set two different timeouts
- Model 1 uses different timeout logic than subsequent models
- Documentation must explain the distinction
- Code complexity from handling two timeout types

Using only `max_time` simplifies the mental model and codebase.

## Current Usage Analysis

### Default Values
- **logos**: `iteration_timeout: 5` (seconds)
- **bimodal**: `iteration_timeout: 1.0` 
- **exclusion**: `iteration_timeout: 1.0`

### Core Usage Locations
1. **iterate/core.py**: Timeout checking in `_iterate_with_progress()`
2. **builder/module.py**: Pass to UnifiedProgress
3. **output/progress/core.py**: Progress bar timeout duration
4. **Tests**: 6 test files use iteration_timeout

### Documentation References
- Multiple theory-specific SETTINGS.md and ITERATE.md files
- API_REFERENCE.md in logos theory
- README files in iterate and builder modules

## Implementation Plan

### Phase 1: Core Changes (1 hour)

#### 1.1 Update BaseModelIterator
```python
# iterate/core.py - Line 198
# OLD:
timeout = self.settings.get('iteration_timeout', self.settings.get('timeout', 300))

# NEW:
timeout = self.settings.get('max_time', 300)
```

Also update line 505 with same change.

#### 1.2 Update BuildModule
```python
# builder/module.py - Lines 752-757
# OLD:
iteration_timeout = example_case[2].get('iteration_timeout', 60.0)
initial_timeout = example_case[2].get('max_time', 60.0)
progress = UnifiedProgress(
    total_models=iterate_count,
    iteration_timeout=iteration_timeout,
    initial_timeout=initial_timeout
)

# NEW:
max_time = example_case[2].get('max_time', 60.0)
progress = UnifiedProgress(
    total_models=iterate_count,
    max_time=max_time  # Single timeout for all operations
)
```

#### 1.3 Update UnifiedProgress
```python
# output/progress/core.py
# Change constructor signature:
def __init__(self, 
             total_models: int = 1,
             max_time: Optional[float] = None,  # Renamed from iteration_timeout
             display: Optional['ProgressDisplay'] = None):
    # ...
    self.max_time = max_time or 60.0
    # Remove initial_timeout logic - use max_time for all models
```

Update `start_model_search()` to use `self.max_time` for all progress bars.

### Phase 2: Theory Updates (30 minutes)

#### 2.1 Remove from Default Settings
- **logos/semantic.py**: Remove line `'iteration_timeout': 5,`
- **bimodal/semantic.py**: Remove line `'iteration_timeout': 1.0,`
- **exclusion/semantic.py**: Remove lines with `'iteration_timeout': 1.0,`

#### 2.2 Update Documentation
Files to update:
- `theory_lib/logos/docs/SETTINGS.md`
- `theory_lib/logos/docs/ITERATE.md`
- `theory_lib/logos/docs/API_REFERENCE.md`
- `theory_lib/bimodal/docs/SETTINGS.md`
- `theory_lib/bimodal/docs/ITERATE.md`
- `theory_lib/exclusion/docs/SETTINGS.md`
- `theory_lib/exclusion/docs/ITERATE.md`

Remove all references to `iteration_timeout` and update examples to show `max_time` usage.

### Phase 3: Test Updates (30 minutes)

#### 3.1 Update Test Files
1. **iterate/tests/test_base_iterator.py**: Change `iteration_timeout` to `max_time`
2. **output/progress/tests/test_core.py**: Update all UnifiedProgress calls
3. **output/progress/tests/test_animated.py**: Update if needed

#### 3.2 Add Migration Test
Create test to verify old examples with iteration_timeout still work (ignored).

### Phase 4: Documentation & Cleanup (1 hour)

#### 4.1 Update Module Documentation
- `iterate/README.md`: Remove iteration_timeout references
- `builder/README.md`: Update timeout documentation
- `output/progress/README.md`: Update examples

#### 4.2 Migration Guide
Add to main docs:
```markdown
## Migration from iteration_timeout

The `iteration_timeout` setting has been removed. Use `max_time` for all timeout purposes:

Before:
```python
settings = {
    'max_time': 10,
    'iteration_timeout': 5
}
```

After:
```python
settings = {
    'max_time': 10  # Used for all operations
}
```
```

## Backwards Compatibility

To maintain compatibility:
1. Silently ignore `iteration_timeout` if present in settings
2. Log debug message when iteration_timeout is encountered
3. Use max_time value for all timeout checks

## Testing Strategy

1. **Unit Tests**: Verify timeout behavior with only max_time
2. **Integration Tests**: Run existing examples to ensure compatibility
3. **Performance Tests**: Confirm no regression in timeout handling
4. **Documentation Tests**: Verify all examples use correct settings

## Risk Mitigation

**Risk**: Breaking existing user examples
- **Mitigation**: Ignore iteration_timeout silently, use max_time

**Risk**: Users expect different timeouts for first vs subsequent models
- **Mitigation**: Document that max_time applies to all models equally

**Risk**: Some theories may need adjustment for longer timeouts
- **Mitigation**: Review theory examples and adjust max_time values

## Success Criteria

1. All timeout operations use max_time exclusively
2. No references to iteration_timeout in active code
3. All tests pass with updated timeout logic
4. Documentation clearly explains single timeout model
5. Existing examples continue to work

## Future Considerations

- Consider adding `solver_timeout` if finer control needed
- Could add per-model timeout overrides in future
- Monitor user feedback on single timeout approach

## References

- [Model 1 Timeout Handling](046_model1_timeout_handling.md)
- [Progress Bar Timing Research](../research/018_progress_bar_slow_fill_analysis.md)