# Enhanced Isomorphism Tracking and Reporting

**Status**: Draft  
**Priority**: High  
**Complexity**: Medium  
**Dependencies**: Spec 040 (Iterator Generator Implementation), Spec 041 (Termination Messages)

## Executive Summary

Enhance the model iteration system to track isomorphic models on a per-search basis, displaying real-time progress showing models skipped since the last non-isomorphic model, and generating a comprehensive final report detailing the search effort for each model found.

## Current State

The system currently:
- Tracks total isomorphic models skipped (`isomorphic_model_count`)
- Shows cumulative count in progress bar: "(skipped X)" 
- Displays basic termination message with total models skipped
- No per-model search statistics
- No detailed timing information per search

## Requirements

### 1. Per-Search Tracking
- Reset isomorphic skip counter after each non-isomorphic model is found
- Track search duration for each model separately
- Track models checked during each search phase

### 2. Progress Bar Updates
- Show "(skipped X)" where X = isomorphic models skipped since last found
- Reset counter to 0 when starting search for next model
- Maintain smooth progress bar updates without stacking

### 3. Final Report
- **Always printed** after iteration completes (success or timeout)
- For each model found:
  - Model number
  - Isomorphic models skipped during search
  - Time taken to find
  - Total models checked
- For incomplete searches (timeout/exhaustion):
  - Indicate search was incomplete
  - Show models checked and time elapsed before termination

### 4. Example Output

```
Finding models: [████████░░░░░░░░░░░░░░░░░░░░] 2/4 (skipped 3) 2.1s

[Model 2 output...]

Finding models: [████████████░░░░░░░░░░░░░░░░] 3/4 (skipped 1) 4.3s

[Model 3 output...]

Finding models: [██████████████████░░░░░░░░░░] 4/4 (skipped 7) 8.7s

[Model 4 output...]

========================================

ITERATION SEARCH SUMMARY
Model 1: Initial model (given)
Model 2: Found after skipping 3 isomorphic models (2.1s)
Model 3: Found after skipping 1 isomorphic model (0.8s)  
Model 4: Found after skipping 7 isomorphic models (4.4s)

Total: 4/4 models found, 11 isomorphic models skipped, 8.7s elapsed
========================================
```

For timeout case:
```
========================================

ITERATION SEARCH SUMMARY
Model 1: Initial model (given)
Model 2: Found after skipping 3 isomorphic models (2.1s)
Model 3: Not found - timeout after checking 45 models (57.9s)

Total: 2/4 models found, 3 isomorphic models skipped, 60.0s elapsed
========================================
```

## Implementation Plan

### Phase 1: Data Structure Updates

#### 1.1 Extend IteratorCore
```python
class IteratorCore:
    def __init__(self, build_example):
        # ... existing code ...
        self.search_stats = []  # List of per-model search statistics
        self.current_search_skipped = 0  # Isomorphic skipped in current search
        self.current_search_start = None  # Start time of current search
```

#### 1.2 Search Statistics Structure
```python
@dataclass
class SearchStatistics:
    model_number: int
    found: bool
    isomorphic_skipped: int
    models_checked: int
    search_duration: float
    termination_reason: Optional[str] = None
```

### Phase 2: Progress Tracking Updates

#### 2.1 Modify Progress Bar Updates
- Update `IterationProgress.update()` to show current search skipped count
- Reset counter when new model is found
- Ensure terminal width handling works with new format

#### 2.2 Update Iterator Logic
```python
# In iterate_generator method:
if is_isomorphic:
    self.current_search_skipped += 1
    self.isomorphic_model_count += 1  # Keep total for compatibility
    # Update progress with current search count
    self.progress.update(
        len(self.model_structures) + 1,
        self.current_search_skipped  # Not total
    )
    continue

# When model is found:
search_duration = time.time() - self.current_search_start
self.search_stats.append(SearchStatistics(
    model_number=len(self.model_structures) + 1,
    found=True,
    isomorphic_skipped=self.current_search_skipped,
    models_checked=models_checked_this_search,
    search_duration=search_duration
))
self.current_search_skipped = 0  # Reset for next search
self.current_search_start = time.time()
```

### Phase 3: Report Generation

#### 3.1 Create Report Generator
```python
class IterationReportGenerator:
    """Generates comprehensive iteration search reports."""
    
    def generate_report(self, search_stats, total_requested, total_elapsed):
        """Generate formatted report of iteration search statistics."""
        lines = []
        lines.append("\n" + "="*40)
        lines.append("\nITERATION SEARCH SUMMARY")
        
        # Model 1 is always given
        lines.append("Model 1: Initial model (given)")
        
        # Report on each search
        for stat in search_stats:
            if stat.found:
                lines.append(
                    f"Model {stat.model_number}: Found after skipping "
                    f"{stat.isomorphic_skipped} isomorphic model"
                    f"{'s' if stat.isomorphic_skipped != 1 else ''} "
                    f"({stat.search_duration:.1f}s)"
                )
            else:
                reason = stat.termination_reason or "exhausted search space"
                lines.append(
                    f"Model {stat.model_number}: Not found - {reason} "
                    f"after checking {stat.models_checked} models "
                    f"({stat.search_duration:.1f}s)"
                )
        
        # Summary line
        total_found = sum(1 for s in search_stats if s.found) + 1  # +1 for initial
        total_skipped = sum(s.isomorphic_skipped for s in search_stats)
        
        lines.append(f"\nTotal: {total_found}/{total_requested} models found, "
                    f"{total_skipped} isomorphic model"
                    f"{'s' if total_skipped != 1 else ''} skipped, "
                    f"{total_elapsed:.1f}s elapsed")
        lines.append("="*40)
        
        return "\n".join(lines)
```

#### 3.2 Integration Points
- Add report generator to BaseModelIterator
- Call report generation in:
  - `iterate_generator` finally block
  - BuildModule after iteration completes
  - Both success and failure paths

### Phase 4: Termination Handling

#### 4.1 Track Incomplete Searches
When iteration terminates (timeout, exhaustion, etc.):
```python
if should_terminate:
    # Record incomplete search
    search_duration = time.time() - self.current_search_start
    self.search_stats.append(SearchStatistics(
        model_number=len(self.model_structures) + 2,  # Next model we were looking for
        found=False,
        isomorphic_skipped=self.current_search_skipped,
        models_checked=models_checked_this_search,
        search_duration=search_duration,
        termination_reason=reason
    ))
    break
```

#### 4.2 Update BuildModule
- Remove or modify existing termination info generation
- Always print the detailed search report
- Ensure report is printed even on exceptions

### Phase 5: Testing

#### 5.1 Unit Tests
- Test SearchStatistics data structure
- Test report generation with various scenarios
- Test progress bar with per-search counts

#### 5.2 Integration Tests
- Test complete iteration with report
- Test timeout scenarios
- Test exhaustion scenarios
- Verify progress bar updates correctly

#### 5.3 Edge Cases
- Single model (iterate=1)
- All models isomorphic
- Immediate timeout
- No isomorphic models found

## Migration Strategy

1. **Backward Compatibility**: 
   - Keep total `isomorphic_model_count` for any code that uses it
   - Add new tracking alongside existing

2. **Gradual Rollout**:
   - Implement data structures first
   - Add tracking without changing display
   - Update display formats
   - Add final report

3. **Testing Strategy**:
   - Test each phase independently
   - Ensure no regression in existing functionality
   - Validate report accuracy

## Success Criteria

1. Progress bar shows per-search skipped count that resets after each find
2. Final report always appears with detailed per-model statistics
3. Timeout/exhaustion cases show partial results clearly
4. No performance degradation from additional tracking
5. Clean, readable output format

## Future Enhancements

1. Optional verbose mode showing more details during search
2. Export search statistics to JSON for analysis
3. Configurable report format
4. Historical comparison between runs
5. Memory usage tracking per search