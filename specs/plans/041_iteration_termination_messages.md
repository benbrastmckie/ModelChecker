# Iteration Termination Message Enhancement Plan

**Spec ID**: 041  
**Title**: Enhanced Iteration Termination Messages  
**Status**: Draft  
**Created**: 2024-01-14  
**Priority**: High  

## Executive Summary

Enhance the model iteration termination messages to clearly communicate why the search ended, how many models were checked, and whether the search was exhaustive or incomplete. This addresses user confusion when fewer models are found than requested.

## Problem Statement

Currently, when the iterator finds fewer models than requested (e.g., 2 models when iterate=4), users see:
```
Found 2/4 distinct models.
```

This provides no insight into:
- Why only 2 models were found
- Whether more models might exist
- How much computational effort was expended
- If the search was exhaustive or hit a limit

## Requirements

### Functional Requirements

1. **Clear Termination Reason**: Display why iteration stopped
   - Exhaustive search (no more models exist)
   - Timeout reached
   - Too many consecutive failures
   - Found all requested models

2. **Search Statistics**: Show computational effort
   - Total models checked (including isomorphic)
   - Time spent searching
   - Success rate (if relevant)

3. **Contextual Messages**: Different messages for different scenarios
   - Complete success: "Successfully found all N requested models"
   - Exhaustive search: "Found all possible models (M of N requested)"
   - Timeout: "Search stopped due to time limit"
   - Failure limit: "Search stopped after X consecutive failed attempts"

### Non-Functional Requirements

1. **Clarity**: Messages must be immediately understandable
2. **Conciseness**: Avoid verbose output while being informative
3. **Consistency**: Use similar format across all termination types
4. **No Breaking Changes**: Enhance existing output without breaking compatibility

## Proposed Solution

### Message Format

Standard format for all termination messages:
```
Found M/N distinct models (checked X models in Y seconds).
[Termination reason with context]
```

### Example Messages

1. **Complete Success**:
   ```
   Found 4/4 distinct models (checked 12 models in 2.3s).
   Successfully found all requested models.
   ```

2. **Exhaustive Search**:
   ```
   Found 2/4 distinct models (checked 47 models in 5.1s).
   Search complete: No more non-isomorphic models exist.
   ```

3. **Timeout**:
   ```
   Found 3/5 distinct models (checked 89 models in 300.0s).
   Search stopped: Time limit reached (max 300s).
   ```

4. **Consecutive Failures**:
   ```
   Found 2/3 distinct models (checked 156 models in 45.2s).
   Search stopped: 20 consecutive attempts found only isomorphic models.
   ```

## Implementation Details

### Phase 1: Enhance Summary Display

**Location**: `src/model_checker/builder/module.py::_run_generator_iteration`

```python
# Current implementation (line ~977)
print(f"Found {distinct_count + 1}/{iterate_count} distinct models.")

# Enhanced implementation
# Collect termination info from iterator
termination_info = self._get_termination_info(example, distinct_count + 1, iterate_count)
print(termination_info)
```

### Phase 2: Create Termination Info Method

**Location**: `src/model_checker/builder/module.py`

```python
def _get_termination_info(self, example, found_count, requested_count):
    """Generate comprehensive termination message.
    
    Args:
        example: BuildExample with iterator information
        found_count: Number of distinct models found
        requested_count: Number of models requested
        
    Returns:
        str: Formatted termination message
    """
    # Get iterator if available
    iterator = getattr(example, '_iterator', None)
    if not iterator:
        return f"Found {found_count}/{requested_count} distinct models."
    
    # Get basic stats
    checked_count = getattr(iterator, 'checked_model_count', 0)
    elapsed_time = 0.0
    if hasattr(iterator, 'termination_manager'):
        elapsed_time = iterator.termination_manager.get_elapsed_time()
    
    # Base message with stats
    base_msg = f"Found {found_count}/{requested_count} distinct models "
    base_msg += f"(checked {checked_count} models in {elapsed_time:.1f}s)."
    
    # Add termination reason
    if found_count == requested_count:
        reason = "Successfully found all requested models."
    else:
        reason = self._get_termination_reason(iterator, found_count, requested_count)
    
    return f"{base_msg}\n{reason}"
```

### Phase 3: Extract Termination Reason

**Location**: `src/model_checker/builder/module.py`

```python
def _get_termination_reason(self, iterator, found_count, requested_count):
    """Determine why iteration stopped.
    
    Returns formatted reason string.
    """
    # Check debug messages for specific reasons
    debug_messages = iterator.get_debug_messages() if hasattr(iterator, 'get_debug_messages') else []
    
    # Look for specific termination indicators
    for msg in reversed(debug_messages):  # Check most recent first
        if "No more models found" in msg:
            return "Search complete: No more non-isomorphic models exist."
        elif "timeout" in msg.lower():
            timeout_val = iterator.settings.get('timeout', 300)
            return f"Search stopped: Time limit reached (max {timeout_val}s)."
        elif "consecutive invalid" in msg or "consecutive failed" in msg:
            max_attempts = iterator.settings.get('max_invalid_attempts', 20)
            return f"Search stopped: {max_attempts} consecutive attempts found only isomorphic models."
        elif "Insufficient progress" in msg:
            return "Search stopped: Too many checks with insufficient progress."
    
    # Default message if no specific reason found
    return f"Search ended after finding {found_count} of {requested_count} requested models."
```

### Phase 4: Handle Batch Mode

**Location**: `src/model_checker/builder/module.py` (around line 902)

Apply similar enhancements to the batch iteration path:

```python
# Replace current simple message
print(f"Found {distinct_count}/{expected_total} distinct models.")

# With enhanced version
termination_info = self._get_termination_info(example, distinct_count, expected_total)
print(termination_info)
```

## Testing Strategy

### Test Cases

1. **Complete Success**: Example with iterate=2 that has 2+ models
2. **Exhaustive Search**: Example with iterate=4 that only has 2 models
3. **Timeout**: Example with low timeout that triggers limit
4. **Consecutive Failures**: Example that generates many isomorphic models

### Expected Output Examples

1. **Counterfactual Example** (current issue):
   ```
   Finding non-isomorphic models: [████████████████░░░░░░] 2/4 (checked 47) 5.1s
   ...
   Found 2/4 distinct models (checked 47 models in 5.1s).
   Search complete: No more non-isomorphic models exist.
   ```

2. **Modal Example** (complete):
   ```
   Finding non-isomorphic models: [████████████████████████] 4/4 (checked 9) 0.9s
   ...
   Found 4/4 distinct models (checked 9 models in 0.9s).
   Successfully found all requested models.
   ```

## Implementation Order

1. **Implement `_get_termination_info` method** - Core logic
2. **Implement `_get_termination_reason` helper** - Reason extraction
3. **Update generator iteration summary** - Apply to generator path
4. **Update batch iteration summary** - Apply to batch path
5. **Test with various examples** - Verify all scenarios
6. **Update documentation** - Document new output format

## Rollback Plan

If issues arise, revert to simple message format by changing only the print statements back to original format. The new methods can remain without affecting functionality.

## Success Criteria

1. Users can immediately understand why iteration stopped
2. Computational effort (models checked) is visible
3. Distinction between exhaustive/incomplete search is clear
4. Messages are concise and informative
5. All existing functionality continues to work

## Future Enhancements

1. Add verbosity levels for more/less detail
2. Include isomorphism statistics (how many were duplicates)
3. Add search strategy hints ("Try increasing N" for exhaustive searches)
4. Progress indication during long searches between models

## Notes

- The iterator already tracks all necessary information
- Focus is on presentation, not new functionality
- Must handle cases where iterator attributes might not exist
- Should gracefully degrade if information is unavailable