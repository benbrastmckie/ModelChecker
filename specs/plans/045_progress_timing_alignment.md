# Progress Bar Timing Alignment Refactor

**Spec ID**: SPEC-045  
**Created**: 2025-08-15  
**Status**: DRAFT  
**Priority**: P1  
**Effort**: 3 hours  
**Risk**: Medium  
**Depends on**: SPEC-044 (Progress Bar Animation)

## Executive Summary

Refactor the progress bar timing system to accurately reflect the time taken to find each non-isomorphic model, ensuring consistency between progress bar displays and the iteration report. Each progress bar should measure from when the search for that specific model begins until it is found or times out.

## Motivation

Currently, there is a significant discrepancy between progress bar times and iteration report times:
- Progress bars show ~8.9s while reports show ~11.4s for the same search
- This 28% difference confuses users about actual performance
- The timing doesn't accurately represent the search duration for each model

Users expect the progress bar to show how long it takes to find each specific non-isomorphic model, not just the animation duration.

## Current Implementation Issues

1. **Progress Bar Timing**: Starts when animation begins, after setup work
2. **Report Timing**: Includes all overhead from search initialization
3. **Inconsistent References**: Different components use different time references
4. **Model 1 Special Case**: Doesn't follow the same timing pattern

**Note**: The current implementation already fills each progress bar from 0-100% based on elapsed time vs timeout (not based on K models). This behavior is correct and should be preserved.

## Proposed Solution

### Core Timing Principle

Each model's search time should be measured from:
- **Start**: When the search for that specific model begins (after previous model found)
- **End**: When the model is found, timeout occurs, or search space exhausted

### Progress Bar Behavior

**IMPORTANT**: Each progress bar fills from 0% to 100% over the iteration timeout duration:
- Progress bars are independent for each model search
- Each bar fills completely (0% to 100%) based on elapsed time vs timeout
- No partial filling based on model count (no 1/K behavior)
- If model found before timeout, bar immediately jumps to 100%
- If timeout occurs, bar reaches 100% at the timeout moment

### Implementation Changes

#### 1. Unified Search Timing in BaseModelIterator

**Current Issues Found**:
- Line 174 sets `self.current_search_start = time.time()` for model 2
- Line 221 sets `search_start_time = time.time()` (unused duplicate)
- Line 232 starts progress bar AFTER initial overhead
- Line 360 resets `self.current_search_start` after finding a model

**Required Changes**:

```python
# core.py - BaseModelIterator._iterate_with_progress()
def _iterate_with_progress(self):
    """Main iteration loop with unified timing."""
    # ... existing setup ...
    
    # Remove duplicate timing variables (DELETE line 221)
    # Remove: search_start_time = time.time()
    
    # Initialize search for model 2 (line 174 - keep as is)
    self.current_search_start = time.time()
    
    while len(self.model_structures) < self.max_iterations:
        model_number = len(self.model_structures) + 1
        
        # Check timeout using current_search_start (lines 197-198 - keep as is)
        elapsed = time.time() - self.current_search_start
        
        # Start progress bar with synchronized time (modify lines 231-233)
        if self.search_progress and current_search_model != model_number:
            # Pass the current_search_start time to progress
            self.search_progress.start_model_search(
                model_number, 
                start_time=self.current_search_start  # NEW: pass start time
            )
            current_search_model = model_number
        
        # ... search for model ...
        
        # Calculate duration (line 255 for timeout, line 339 for success - keep as is)
        search_duration = time.time() - self.current_search_start
        
        # Reset timing for next search (line 360 - keep as is)
        self.current_search_start = time.time()
```

#### 2. Progress Bar Start Time Parameter

**Current Implementation** (lines 86-117 in core.py):
- Creates TimeBasedProgress without start_time parameter
- Sets its own `self.current_search_start` (line 95) - duplicates iterator timing

**Required Changes**:

```python
# core.py - UnifiedProgress (modify method signature at line 86)
def start_model_search(self, model_number: int, start_time: Optional[float] = None) -> None:
    """Start progress tracking for a model search.
    
    Args:
        model_number: The model number being searched for
        start_time: Optional start time to sync with iterator timing
    """
    # ... existing duplicate check (lines 89-92) ...
    
    self.current_model = model_number
    # Use provided start time or fallback to current time
    self.current_search_start = start_time or time.time()  # MODIFY line 95
    self.current_search_skipped = 0
    
    # ... existing overall timing (lines 98-100) ...
    
    # ... existing cleanup (lines 102-106) ...
    
    # Create animated progress bar with synchronized time (modify lines 110-114)
    from .animated import TimeBasedProgress
    progress_bar = TimeBasedProgress(
        timeout=self.iteration_timeout,
        model_number=model_number,
        total_models=self.total_models,
        display=self.display,
        start_time=self.current_search_start  # NEW: pass synchronized time
    )
    
    self.model_progress_bars.append(progress_bar)
    progress_bar.start()
```

#### 3. TimeBasedProgress with Custom Start Time

**Current Implementation** (animated.py):
- `__init__` doesn't accept start_time (lines 79-100)
- `start()` sets `self.start_time = time.time()` (line 104)
- Already has correct animation logic using elapsed/timeout

**Required Changes**:

```python
# animated.py - TimeBasedProgress.__init__ (modify line 79)
def __init__(self, 
             timeout: float,
             model_number: int,
             total_models: int,
             display: Optional[ProgressDisplay] = None,
             start_time: Optional[float] = None):  # NEW parameter
    """Initialize with optional start time for timing sync."""
    super().__init__(display)
    self.timeout = timeout
    self.model_number = model_number
    self.total_models = total_models
    self.provided_start_time = start_time  # NEW: store provided time
    self.start_time = None
    self.found = False
    self.checked_count = 0
    self.skipped_count = 0
    self.use_color = self._supports_color()

def start(self, total: int = 100, message: str = "") -> None:
    """Start the animated progress bar."""
    # Use provided start time or current time (modify line 104)
    self.start_time = self.provided_start_time or time.time()
    self.active = True
    self.thread = threading.Thread(target=self._animate)
    self.thread.daemon = True
    self.thread.start()

# _animate() method stays the same - already uses self.start_time correctly
```

#### 4. Consistent Model 1 Timing

**Current Implementation** (builder/module.py):
- Line 762: `progress.start_model_search(1)` starts without timing reference
- Line 765: `example = BuildExample(...)` creates and solves model
- Model structure has `z3_model_runtime` from solve() method

**Required Changes**:

```python
# builder/module.py - process_example_with_iteration (around line 760)
def process_example_with_iteration(self, ...):
    """Process example with proper Model 1 timing."""
    # ... existing progress creation ...
    
    # Capture Model 1 start time BEFORE any work
    model_1_start = time.time()  # NEW: add before line 762
    
    # Start progress for first model with timing
    progress.start_model_search(1, start_time=model_1_start)  # MODIFY line 762
    
    # Create and solve the example
    example = BuildExample(self, semantic_theory, example_case, theory_name)
    
    # Store timing reference for iteration report
    # The model already has z3_model_runtime for solver time
    # Add total search time for consistency
    example.model_structure._search_start_time = model_1_start  # NEW
    example.model_structure._total_search_time = time.time() - model_1_start  # NEW
    
    # ... rest of method ...
```

**Note**: Model 1's timing will include:
- Module initialization overhead
- BuildExample construction
- Constraint generation
- Z3 solving time
- Model structure building

This gives users the true "time to first model" metric.

#### 5. Remove Old Partial-Fill Logic

Ensure complete removal of any 1/K partial filling behavior:

```python
# animated.py - TimeBasedProgress._animate()
def _animate(self):
    """Animate progress bar that fills 0-100% over timeout."""
    while self.active and not self.found:
        elapsed = time.time() - self.start_time
        
        # Progress is ONLY based on elapsed time vs timeout
        # NOT based on model count or K value
        progress = min(1.0, elapsed / self.timeout)
        
        # Generate bar that fills completely for THIS search
        bar = self._generate_bar(progress)
        
        # No reference to total_models in progress calculation
        msg = f"Finding non-isomorphic models: {bar} {self.model_number}/{self.total_models}"
        # ... rest of animation ...
```

**Code to Remove/Verify Removed**:
- Any calculation like `progress = model_number / total_models`
- Any partial bar width based on K models
- Any cumulative progress across multiple models
- References to "portion" or "fraction" based on model count

#### 6. Update Iteration Report Timing

**Current Implementation** (iterate/core.py lines 431-438):
```python
# Gets z3_model_runtime for initial model (solver time only)
initial_time = getattr(self.build_example.model_structure, 'z3_model_runtime', 
                      getattr(self.build_example.model_structure, '_search_duration', 0.0))
```

**Required Changes**:

```python
# iterate/core.py - BaseModelIterator.print_report (around line 431)
# Use total search time for Model 1 to match progress bar
initial_time = getattr(self.build_example.model_structure, '_total_search_time',
                      getattr(self.build_example.model_structure, 'z3_model_runtime', 0.0))
```

This ensures the iteration report shows the same time that was displayed in the Model 1 progress bar.

## Testing Strategy

### Unit Tests
1. Verify progress bar uses provided start time
2. Test timing synchronization between components
3. Validate Model 1 includes setup time
4. Ensure subsequent models reset timing
5. **Verify full 0-100% fill behavior**:
   - Progress bar fills completely for each model
   - No partial filling based on K models
   - Each bar independent of others

### Integration Tests
1. Run examples with multiple models
2. Compare progress bar final times with report times
3. Verify times match within 0.1s tolerance
4. Test timeout scenarios

### Manual Validation
```bash
# Run with timing verification
./dev_cli.py -i 3 examples/test.py

# Expected output:
# Progress: "Finding non-isomorphic models: [████] 2/3 2.3s"
# Report:   "Model 2: Found after skipping 1 isomorphic model (2.3s)"
# Times should match exactly
```

## Success Criteria

1. Progress bar times match iteration report times (±0.1s)
2. Model 1 timing includes all setup overhead
3. Subsequent models time only their search duration
4. No regression in existing functionality
5. Clear, consistent timing across all displays

## Risk Mitigation

**Risk**: Changing timing affects timeout behavior
- **Mitigation**: Ensure timeout still measured from search start

**Risk**: Breaking existing progress displays
- **Mitigation**: Extensive testing, backwards compatible changes

**Risk**: Performance overhead from timing sync
- **Mitigation**: Minimal overhead, single time capture

## Edge Cases and Cleanup

### Timing Edge Cases to Handle

1. **Very Fast Model Finds** (<0.1s)
   - Progress bar may not have time to animate
   - Ensure final time is still captured correctly

2. **Timeout Scenarios**
   - Progress bar should show time up to timeout moment
   - Report should match this time (not include cleanup)

3. **Interrupted Searches** (Ctrl+C)
   - Gracefully handle partial timing data
   - Don't corrupt the report

### Code Cleanup Required

1. **Remove Duplicate Variables**:
   - Delete unused `search_start_time` (line 221 in core.py)
   - Consolidate timing to single `current_search_start`

2. **Remove Legacy Comments**:
   - Clean up references to old progress systems
   - Remove TODO comments about timing

3. **Type Hints**:
   - Add `Optional[float]` import where needed
   - Ensure all new parameters have proper type hints

## Implementation Plan

### Phase 1: Core Timing Infrastructure (1.5 hours)
1. Add start_time parameter to progress classes
2. Update BaseModelIterator timing logic
3. Ensure Model 1 captures setup time
4. Remove duplicate timing variables

### Phase 2: Progress Bar Integration (1 hour)
1. Modify UnifiedProgress to pass start times
2. Update TimeBasedProgress to use provided times
3. Test synchronization between components
4. Verify color still works with timing changes

### Phase 3: Testing and Refinement (30 minutes)
1. Add unit tests for timing alignment
2. Manual testing with various examples
3. Fine-tune any remaining discrepancies
4. Update existing tests that check timing

## Future Considerations

- Add detailed timing breakdown in debug mode
- Consider showing both "search time" and "total time"
- Option for microsecond precision in reports
- Performance metrics dashboard

## References

- [Progress Timing Research](../research/017_progress_bar_timing_discrepancy.md)
- [Unified Progress System](043_unified_progress_system_implementation.md)
- [Progress Animation Spec](044_progress_bar_full_width_animation.md)