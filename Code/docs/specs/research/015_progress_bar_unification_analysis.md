# Research 015: Progress Bar Unification Analysis

## Overview

This research document analyzes the multiple progress bar systems in ModelChecker to identify duplication and propose a unified approach for both initial model search and iteration progress tracking.

## Current Progress Systems

### 1. BuildModule Spinner (builder/progress.py)

**Purpose**: Shows a simple spinner during initial model checking
**Location**: Used in BuildModule for the first model check
**Implementation**:
```python
class Spinner:
    """Displays an animated progress spinner while a task runs."""
    # Shows: "Running model-checker: /" (animated)
```

**Usage in BuildModule**:
- Started before checking the first model
- Stopped after model is found or timeout
- Simple, non-intrusive progress indicator

### 2. Iterator Progress Bar (iterate/metrics.py)

**Purpose**: Shows detailed progress during iteration
**Location**: IterationProgress class in metrics.py
**Implementation**:
```python
class IterationProgress:
    """Progress bar for model iteration."""
    # Shows: "Finding models: [████░░] 2/4 (checked 5) 3.2s"
```

**Features**:
- Visual progress bar with filled/unfilled segments
- Shows models found vs. requested
- Displays total models checked (including isomorphic ones)
- Shows elapsed time
- Only displays in terminal (checks isatty)

### 3. Search Progress (Placeholder)

**Purpose**: Future unified progress system
**Location**: Referenced but not implemented in core.py
**References**:
```python
# In BaseModelIterator.__init__:
self.search_progress = None

# In iterate_generator:
if self.search_progress:
    self.search_progress.start_search(model_number)
# ...
if self.search_progress:
    self.search_progress.complete_search(model_number, found=True)
```

This appears to be a placeholder for a future unified progress system that would handle both initial search and iteration.

## Progress Bar Interactions and Issues

### Current Flow

1. **Initial Model Check**:
   - BuildModule starts Spinner: "Running model-checker: /"
   - Model is found
   - Spinner stops
   - Model is displayed

2. **Iteration Phase**:
   - BuildModule calls iterate_example_generator
   - Iterator creates IterationProgress
   - For each model search:
     - IterationProgress updates: "Finding models: [██░░] 2/4..."
     - Model is yielded
     - BuildModule displays model
   - IterationProgress completes

### Identified Issues

1. **Visual Discontinuity**: 
   - Different progress indicators for initial vs. iteration
   - Spinner (simple) vs. progress bar (detailed)

2. **Missing Progress for Initial Model**:
   - No indication of constraint solving progress
   - No "checked N models" counter for first model

3. **Potential Duplication**:
   - Both systems track elapsed time
   - Both systems handle timeout scenarios
   - Both write to stdout with carriage returns

4. **No Unified Interface**:
   - BuildModule uses Spinner directly
   - Iterator uses IterationProgress directly
   - No abstraction layer for progress tracking

## Proposed Unified Progress System

### Design Goals

1. Consistent visual appearance throughout the process
2. Single progress tracking system for both phases
3. Detailed information when useful (models checked, time elapsed)
4. Clean API for progress updates
5. Minimal changes to existing code

### Proposed Architecture

```python
class UnifiedProgress:
    """Unified progress tracking for model checking and iteration."""
    
    def __init__(self, total_models=1, show_checked_count=True):
        self.total_models = total_models
        self.found_models = 0
        self.checked_models = 0
        self.current_phase = "initial"  # "initial" or "iteration"
        self.show_checked_count = show_checked_count
        
    def start_model_search(self, model_number=1):
        """Start searching for a specific model."""
        self.current_model = model_number
        if model_number == 1:
            self.current_phase = "initial"
            self._show_spinner("Checking initial model")
        else:
            self.current_phase = "iteration"
            self._show_progress_bar()
            
    def update_checked_count(self):
        """Increment the checked models counter."""
        self.checked_models += 1
        self._update_display()
        
    def complete_model_search(self, found=True):
        """Complete search for current model."""
        if found:
            self.found_models += 1
        self._update_display()
        
    def finish(self):
        """Complete all progress tracking."""
        # Clear line and show final summary
```

### Integration Points

1. **BuildModule Changes**:
```python
# Create unified progress for all models
progress = UnifiedProgress(total_models=iterate_count)

# Initial model check
progress.start_model_search(1)
# ... check model ...
progress.complete_model_search(found=True)

# Pass progress to iterator
example._unified_progress = progress
```

2. **Iterator Changes**:
```python
# Use provided progress or create new one
self.search_progress = getattr(build_example, '_unified_progress', None)
if not self.search_progress:
    self.search_progress = UnifiedProgress(total_models=self.max_iterations)
    
# Remove old IterationProgress
# self.progress = IterationProgress(...)  # DELETE
```

### Benefits of Unification

1. **Consistent UX**: Same progress style throughout
2. **Better Information**: Can show "checked N models" even for initial model
3. **Cleaner Code**: Single progress system to maintain
4. **Extensibility**: Easy to add new progress features
5. **Less Duplication**: One timing system, one display system

### Migration Strategy

1. **Phase 1**: Implement UnifiedProgress class
2. **Phase 2**: Add to BuildModule for initial model (alongside Spinner)
3. **Phase 3**: Update Iterator to use UnifiedProgress
4. **Phase 4**: Remove old Spinner and IterationProgress
5. **Phase 5**: Clean up and optimize

## Recommendation

Implement the unified progress system to:
1. Provide consistent user experience
2. Reduce code duplication
3. Enable richer progress information
4. Simplify maintenance

The system should be implemented incrementally, starting with the UnifiedProgress class and gradually migrating both BuildModule and Iterator to use it. This approach minimizes risk while providing immediate benefits.

## Alternative: Minimal Fix

If a full unification is too complex, a minimal fix would be:
1. Keep existing systems separate
2. Ensure Iterator progress is suppressed when called from BuildModule
3. Let BuildModule handle all progress display
4. Add a simple "Searching for model N..." message in BuildModule

However, this approach maintains the duplication and inconsistency issues.