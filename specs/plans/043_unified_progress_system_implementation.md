# Implementation Plan 043: Unified Progress System

## Overview

This plan implements a **unified progress tracking system** for ModelChecker that provides consistent visual feedback during both initial model checking and model iteration. The system will be implemented as a dedicated subpackage at `output/progress/` and will support animated progress bars with time-based completion tracking.

**Goal**: Create a flexible, theory-agnostic progress system that can be easily integrated across all theories while maintaining backward compatibility.

## Current State Analysis

### Existing Progress Systems

1. **BuildModule Spinner** (`builder/progress.py`)
   - Simple animated spinner for initial model checking
   - Shows: "Running model-checker: /" (animated)
   - Thread-based animation

2. **Iterator Progress Bar** (`iterate/metrics.py`)
   - Detailed progress bar for model iteration
   - Shows: "Finding models: [████░░] 2/4 (skipped 3) 5.2s"
   - Terminal-aware with line clearing

3. **Placeholder Search Progress** (referenced in `iterate/core.py`)
   - `self.search_progress = None` placeholder for future system
   - Hooks already in place for `start_search()` and `complete_search()`

### Key Requirements

1. **Animated Progress Bars**: Progress bars should animate to fill over `iteration_timeout` duration
2. **Immediate Completion**: When a model is found, immediately fill that portion of the progress bar
3. **Unified Interface**: Same progress system for both single models and iterations
4. **Theory Agnostic**: Works with all theories without modification
5. **Clean Integration**: Minimal changes to existing code

## Implementation Design

### Phase 1: Core Progress System Architecture

#### 1.1 Create Base Progress Classes

**File**: `src/model_checker/output/progress/__init__.py`
```python
"""Unified progress tracking system for ModelChecker.

This module provides consistent progress feedback for model checking operations,
including both initial model search and iteration over multiple models.
"""

from .core import UnifiedProgress, ProgressBar
from .animated import AnimatedProgressBar, TimeBasedProgress
from .display import ProgressDisplay, TerminalDisplay

__all__ = [
    'UnifiedProgress',
    'ProgressBar', 
    'AnimatedProgressBar',
    'TimeBasedProgress',
    'ProgressDisplay',
    'TerminalDisplay'
]
```

#### 1.2 Core Progress Interface

**File**: `src/model_checker/output/progress/core.py`
```python
"""Core progress tracking interface and base implementation."""

import time
from abc import ABC, abstractmethod
from typing import Optional, Dict, Any


class ProgressBar(ABC):
    """Abstract base class for progress bars."""
    
    @abstractmethod
    def start(self, total: int, message: str = "") -> None:
        """Start progress tracking."""
        pass
    
    @abstractmethod
    def update(self, current: int, **kwargs) -> None:
        """Update progress."""
        pass
    
    @abstractmethod
    def complete(self, success: bool = True) -> None:
        """Complete progress tracking."""
        pass


class UnifiedProgress:
    """Unified progress tracking for all model checking operations.
    
    This class provides a consistent interface for progress tracking
    across initial model checking and iteration phases.
    """
    
    def __init__(self, 
                 total_models: int = 1,
                 iteration_timeout: Optional[float] = None,
                 display: Optional['ProgressDisplay'] = None):
        """Initialize unified progress tracker.
        
        Args:
            total_models: Total number of models to find
            iteration_timeout: Timeout per iteration in seconds
            display: Custom display handler (defaults to TerminalDisplay)
        """
        self.total_models = total_models
        self.iteration_timeout = iteration_timeout or 60.0
        self.display = display or TerminalDisplay()
        
        # State tracking
        self.current_model = 0
        self.models_found = 0
        self.models_checked = 0
        self.isomorphic_skipped = 0
        self.start_time = None
        self.current_search_start = None
        
        # Progress bars for each model
        self.model_progress_bars = []
        
    def start_model_search(self, model_number: int) -> None:
        """Start searching for a specific model."""
        self.current_model = model_number
        self.current_search_start = time.time()
        
        # Create animated progress bar for this model
        progress_bar = TimeBasedProgress(
            timeout=self.iteration_timeout,
            model_number=model_number,
            total_models=self.total_models
        )
        self.model_progress_bars.append(progress_bar)
        progress_bar.start()
        
    def model_checked(self) -> None:
        """Increment checked model counter."""
        self.models_checked += 1
        if self.model_progress_bars:
            self.model_progress_bars[-1].update_checked(self.models_checked)
            
    def model_skipped_isomorphic(self) -> None:
        """Increment isomorphic skip counter."""
        self.isomorphic_skipped += 1
        if self.model_progress_bars:
            self.model_progress_bars[-1].update_skipped(self.isomorphic_skipped)
        
    def complete_model_search(self, found: bool) -> None:
        """Complete search for current model."""
        if found:
            self.models_found += 1
            
        if self.model_progress_bars:
            self.model_progress_bars[-1].complete(found)
            
    def finish(self) -> None:
        """Complete all progress tracking."""
        self.display.clear()
        # Summary will be handled by iteration report
```

#### 1.3 Animated Progress Implementation

**File**: `src/model_checker/output/progress/animated.py`
```python
"""Animated progress bars with time-based completion."""

import time
import threading
from typing import Optional
from .core import ProgressBar
from .display import ProgressDisplay, TerminalDisplay


class AnimatedProgressBar(ProgressBar):
    """Base class for animated progress bars."""
    
    def __init__(self, display: Optional[ProgressDisplay] = None):
        self.display = display or TerminalDisplay()
        self.active = False
        self.thread = None
        
    def _animate(self):
        """Animation loop - to be implemented by subclasses."""
        raise NotImplementedError


class TimeBasedProgress(AnimatedProgressBar):
    """Progress bar that fills over a specified timeout duration.
    
    The bar animates to fill completely over the timeout period,
    but completes immediately when a model is found.
    """
    
    def __init__(self, 
                 timeout: float,
                 model_number: int,
                 total_models: int,
                 display: Optional[ProgressDisplay] = None):
        super().__init__(display)
        self.timeout = timeout
        self.model_number = model_number
        self.total_models = total_models
        self.start_time = None
        self.found = False
        self.checked_count = 0
        self.skipped_count = 0
        
    def start(self, total: int = 100, message: str = "") -> None:
        """Start the animated progress bar."""
        self.start_time = time.time()
        self.active = True
        self.thread = threading.Thread(target=self._animate)
        self.thread.daemon = True
        self.thread.start()
        
    def _animate(self):
        """Animate the progress bar based on elapsed time."""
        update_interval = 0.1  # Update every 100ms
        
        while self.active and not self.found:
            elapsed = time.time() - self.start_time
            progress = min(1.0, elapsed / self.timeout)
            
            # Create progress message
            bar = self._create_bar(progress)
            msg = f"Model {self.model_number}/{self.total_models}: {bar} "
            msg += f"({self.checked_count} checked"
            if self.skipped_count > 0:
                msg += f", {self.skipped_count} skipped"
            msg += f") {elapsed:.1f}s"
            
            self.display.update(msg)
            time.sleep(update_interval)
            
    def _create_bar(self, progress: float, width: int = 20) -> str:
        """Create visual progress bar."""
        filled = int(width * progress)
        return "[" + "█" * filled + "░" * (width - filled) + "]"
        
    def update(self, current: int, **kwargs) -> None:
        """Update progress (called when model is checked)."""
        # Updates handled by update_checked/update_skipped
        pass
        
    def update_checked(self, count: int) -> None:
        """Update checked model count."""
        self.checked_count = count
        
    def update_skipped(self, count: int) -> None:
        """Update skipped model count."""
        self.skipped_count = count
        
    def complete(self, success: bool = True) -> None:
        """Complete the progress bar."""
        self.found = success
        self.active = False
        
        if self.thread and self.thread.is_alive():
            self.thread.join(timeout=0.5)
            
        # Show final state
        elapsed = time.time() - self.start_time
        if success:
            # Fill bar completely
            bar = "[" + "█" * 20 + "]"
            msg = f"Model {self.model_number}/{self.total_models}: {bar} "
            msg += f"FOUND ({self.checked_count} checked"
            if self.skipped_count > 0:
                msg += f", {self.skipped_count} skipped"
            msg += f") {elapsed:.1f}s"
        else:
            # Show incomplete bar
            progress = min(1.0, elapsed / self.timeout)
            bar = self._create_bar(progress)
            msg = f"Model {self.model_number}/{self.total_models}: {bar} "
            msg += f"NOT FOUND ({self.checked_count} checked"
            if self.skipped_count > 0:
                msg += f", {self.skipped_count} skipped"
            msg += f") {elapsed:.1f}s"
            
        self.display.update(msg)
        self.display.complete()
```

#### 1.4 Display Handling

**File**: `src/model_checker/output/progress/display.py`
```python
"""Display handlers for progress output."""

import sys
import os
from abc import ABC, abstractmethod


class ProgressDisplay(ABC):
    """Abstract base class for progress display handlers."""
    
    @abstractmethod
    def update(self, message: str) -> None:
        """Update the progress display."""
        pass
        
    @abstractmethod
    def complete(self) -> None:
        """Complete the current progress line."""
        pass
        
    @abstractmethod
    def clear(self) -> None:
        """Clear the progress display."""
        pass


class TerminalDisplay(ProgressDisplay):
    """Terminal-based progress display with line clearing."""
    
    def __init__(self, stream=sys.stdout):
        self.stream = stream
        self.last_length = 0
        
    def update(self, message: str) -> None:
        """Update progress with carriage return and padding."""
        # Get terminal width for proper padding
        try:
            terminal_width = os.get_terminal_size().columns
        except:
            terminal_width = 80
            
        # Ensure message fits
        if len(message) > terminal_width - 1:
            message = message[:terminal_width - 4] + "..."
            
        # Pad to clear previous content
        padded = message.ljust(self.last_length)
        self.last_length = len(message)
        
        # Write with carriage return
        self.stream.write(f"\r{padded}")
        self.stream.flush()
        
    def complete(self) -> None:
        """Move to next line after progress completes."""
        self.stream.write("\n")
        self.stream.flush()
        self.last_length = 0
        
    def clear(self) -> None:
        """Clear the current line."""
        if self.last_length > 0:
            self.stream.write("\r" + " " * self.last_length + "\r")
            self.stream.flush()
            self.last_length = 0


class BatchDisplay(ProgressDisplay):
    """Non-interactive display for batch mode (no carriage returns)."""
    
    def __init__(self, stream=sys.stdout):
        self.stream = stream
        
    def update(self, message: str) -> None:
        """Update progress (batch mode just prints)."""
        # In batch mode, we might want to skip progress entirely
        # or print periodic updates
        pass
        
    def complete(self) -> None:
        """Complete progress (no-op in batch mode)."""
        pass
        
    def clear(self) -> None:
        """Clear display (no-op in batch mode)."""
        pass
```

### Phase 2: Integration with Existing Code

#### 2.1 Update BuildModule

**Changes to** `src/model_checker/builder/module.py`:

1. Import the new progress system:
```python
from model_checker.output.progress import UnifiedProgress
```

2. Replace Spinner usage with UnifiedProgress:
```python
def build_model(self, ...):
    # Create unified progress for all models
    progress = UnifiedProgress(
        total_models=iterate_count,
        iteration_timeout=self.settings.get('iteration_timeout', 60)
    )
    
    # Start progress for first model
    progress.start_model_search(1)
    
    # Run model check...
    # When checking satisfiability:
    progress.model_checked()
    
    # On completion:
    progress.complete_model_search(found=True)
    
    # Pass to iterator if needed
    if iterate_count > 1:
        example._unified_progress = progress
```

#### 2.2 Update Iterator

**Changes to** `src/model_checker/iterate/core.py`:

1. Use provided progress or create new:
```python
def __init__(self, build_example):
    # ... existing initialization ...
    
    # Use unified progress if provided
    self.search_progress = getattr(build_example, '_unified_progress', None)
    if not self.search_progress:
        self.search_progress = UnifiedProgress(
            total_models=self.max_iterations,
            iteration_timeout=self.settings.get('iteration_timeout', 60)
        )
    
    # Remove old progress system
    # self.progress = IterationProgress(...)  # DELETE
```

2. Update progress calls:
```python
# In iterate_generator:
# When starting search for model N:
self.search_progress.start_model_search(model_number)

# When checking a model:
self.search_progress.model_checked()

# When skipping isomorphic:
self.search_progress.model_skipped_isomorphic()

# When completing:
self.search_progress.complete_model_search(found=True)
```

### Phase 3: Theory Integration

Each theory's iterator already extends BaseModelIterator, so no changes needed to theory-specific code. The progress system will work automatically through the base class.

### Phase 4: Testing Infrastructure

#### 4.1 Unit Tests

**File**: `src/model_checker/output/progress/tests/test_core.py`
```python
"""Tests for core progress functionality."""

import time
import pytest
from model_checker.output.progress import UnifiedProgress


class TestUnifiedProgress:
    """Test unified progress tracking."""
    
    def test_single_model_progress(self):
        """Test progress for single model search."""
        progress = UnifiedProgress(total_models=1, iteration_timeout=1.0)
        
        progress.start_model_search(1)
        assert progress.current_model == 1
        
        # Simulate checks
        for _ in range(5):
            progress.model_checked()
        assert progress.models_checked == 5
        
        progress.complete_model_search(found=True)
        assert progress.models_found == 1
        
    def test_multiple_model_progress(self):
        """Test progress for multiple model iteration."""
        progress = UnifiedProgress(total_models=3, iteration_timeout=1.0)
        
        # Test three model searches
        for i in range(1, 4):
            progress.start_model_search(i)
            progress.model_checked()
            progress.complete_model_search(found=True)
            
        assert progress.models_found == 3
```

#### 4.2 Integration Tests

**File**: `src/model_checker/output/progress/tests/test_animated.py`
```python
"""Tests for animated progress bars."""

import time
import pytest
from model_checker.output.progress.animated import TimeBasedProgress
from model_checker.output.progress.display import ProgressDisplay


class MockDisplay(ProgressDisplay):
    """Mock display for testing."""
    
    def __init__(self):
        self.messages = []
        self.completed = False
        
    def update(self, message: str) -> None:
        self.messages.append(message)
        
    def complete(self) -> None:
        self.completed = True
        
    def clear(self) -> None:
        self.messages.clear()


class TestTimeBasedProgress:
    """Test time-based progress animation."""
    
    def test_progress_animation(self):
        """Test that progress animates over time."""
        display = MockDisplay()
        progress = TimeBasedProgress(
            timeout=0.5,  # 500ms timeout
            model_number=1,
            total_models=1,
            display=display
        )
        
        progress.start()
        time.sleep(0.3)  # Let it animate
        progress.complete(success=True)
        
        # Check that multiple updates occurred
        assert len(display.messages) > 2
        assert display.completed
        
        # Check final message
        assert "FOUND" in display.messages[-1]
```

### Phase 5: Migration and Cleanup

#### 5.1 Remove Old Progress Systems

1. Delete old IterationProgress from `iterate/metrics.py`
2. Remove Spinner from `builder/progress.py` (or keep as legacy)
3. Update all imports and references

#### 5.2 Update Documentation

1. Add progress system documentation to `output/progress/README.md`
2. Update integration guides in theory documentation
3. Add examples to notebooks

## Implementation Timeline

### Week 1: Core Implementation
- [ ] Implement core progress classes (Phase 1)
- [ ] Create comprehensive unit tests
- [ ] Test animated progress bars in isolation

### Week 2: Integration
- [ ] Integrate with BuildModule (Phase 2.1)
- [ ] Integrate with Iterator (Phase 2.2)
- [ ] Test with logos theory

### Week 3: Full Rollout
- [ ] Test with all theories (Phase 3)
- [ ] Fix any theory-specific issues
- [ ] Create integration tests (Phase 4.2)

### Week 4: Polish and Documentation
- [ ] Remove old progress systems (Phase 5.1)
- [ ] Update all documentation (Phase 5.2)
- [ ] Performance optimization if needed

## Success Criteria

1. **Consistent Progress**: Same visual style for all model searches
2. **Animated Completion**: Progress bars animate to completion over timeout
3. **Immediate Updates**: Models found immediately fill their portion
4. **No Regressions**: All existing functionality continues to work
5. **Clean Output**: No overlapping text or display artifacts

## Risk Mitigation

1. **Threading Issues**: Use daemon threads and proper cleanup
2. **Terminal Compatibility**: Test on different terminals
3. **Performance**: Ensure animation doesn't slow down model checking
4. **Backward Compatibility**: Keep old systems available during transition

## Future Enhancements

1. **Rich Terminal Support**: Use libraries like Rich for better visuals
2. **GUI Progress**: Support for Jupyter widgets
3. **Detailed Statistics**: Show more metrics during search
4. **Configurable Styles**: Allow users to customize progress appearance

## Conclusion

This implementation plan creates a unified, animated progress system that provides consistent visual feedback throughout the ModelChecker workflow. The modular design allows for easy extension and customization while maintaining compatibility with all existing theories.