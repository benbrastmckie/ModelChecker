# Progress Bar Full Width Animation and Color Refactor

**Spec ID**: SPEC-044
**Created**: 2025-08-15
**Status**: DRAFT
**Priority**: P2
**Effort**: 2.5 hours
**Risk**: Low
**Depends on**: SPEC-043 (Unified Progress System)

## Executive Summary

Refactor the progress bar animation logic to fill the entire bar width over the iteration timeout period and add orange/amber coloring, providing users with a more accurate and visually distinct representation of time remaining for each model search.

## Motivation

Currently, the progress bar only partially fills based on elapsed time versus timeout, which can be misleading when searches complete quickly. Additionally, the default terminal colors don't provide enough visual distinction for the progress bars. Users expect:
1. The progress bar to represent the full timeout duration, giving them a better sense of how much time remains
2. A visually distinct color (orange/amber) that stands out from regular terminal output

## Current Implementation

The existing implementation in `animated.py` calculates progress as:

```python
elapsed = time.time() - self.start_time
progress = min(1.0, elapsed / self.timeout)
filled = int(bar_width * progress)
```

This approach has several limitations:
1. Progress bar may never reach 100% if model is found quickly
2. Users cannot visually estimate remaining time accurately
3. The partial filling creates inconsistent visual feedback
4. No color distinction from regular terminal output

## Proposed Changes

### 1. Full Width Progress Animation

Modify the progress calculation to always use the full bar width over the timeout duration:

```python
# animated.py - TimeBasedProgress._animate()
def _animate(self) -> None:
    """Animation loop for progress bar that fills entire width over timeout."""
    while self.active:
        elapsed = time.time() - self.start_time
        
        # Calculate progress to fill entire bar over timeout duration
        progress = min(1.0, elapsed / self.timeout)
        
        # Generate full-width progress bar
        bar = self._generate_bar(progress)
        
        # Update display with current progress
        msg = self._format_message(bar, elapsed)
        self.display.update(msg)
        
        time.sleep(0.1)  # Maintain 100ms refresh rate
```

### 2. Consistent Bar Generation

Ensure the bar generation logic properly handles full width:

```python
def _generate_bar(self, progress: float) -> str:
    """Generate progress bar string with proper width handling and color."""
    bar_width = 20  # Standard width for all progress bars
    filled = int(bar_width * progress)
    remaining = bar_width - filled
    
    # ANSI color codes for orange/amber
    ORANGE = '\033[38;5;208m'  # Orange/amber color
    RESET = '\033[0m'
    
    # Create colored progress bar
    filled_bar = f"{ORANGE}{'█' * filled}{RESET}"
    empty_bar = '░' * remaining
    
    return f"[{filled_bar}{empty_bar}]"
```

### 3. Immediate Completion Visual

When a model is found, immediately show full bar:

```python
def complete(self, found: bool = True) -> None:
    """Complete progress with full bar on success."""
    self.active = False
    
    if found:
        # Show completed full bar in orange
        ORANGE = '\033[38;5;208m'
        RESET = '\033[0m'
        full_bar = f"[{ORANGE}{'█' * 20}{RESET}]"
        elapsed = time.time() - self.start_time
        msg = self._format_message(full_bar, elapsed)
        self.display.complete(msg)
    else:
        # Clear on timeout
        self.display.clear()
```

### 4. Color Support Detection

Add terminal color support detection to gracefully degrade:

```python
def _supports_color(self) -> bool:
    """Check if terminal supports color output."""
    # Check common environment variables
    if os.environ.get('NO_COLOR'):
        return False
    
    # Check if output is to a terminal
    if not hasattr(self.display.stream, 'isatty'):
        return False
        
    return self.display.stream.isatty()
```

### 5. Color Constants

Define color constants at module level for consistency:

```python
# Color constants for progress bars
PROGRESS_COLOR = '\033[38;5;208m'  # Orange/amber (256-color)
PROGRESS_COLOR_FALLBACK = '\033[33m'  # Yellow (16-color fallback)
COLOR_RESET = '\033[0m'
```

## Implementation Plan

### Phase 1: Core Animation Logic (1 hour)
1. Update `_animate()` method in `TimeBasedProgress`
2. Implement `_generate_bar()` helper method with color support
3. Ensure consistent bar width across all states
4. Add color constants at module level

### Phase 2: Visual Feedback Enhancement (45 minutes)
1. Update `complete()` method for immediate full bar with color
2. Add `_supports_color()` method for terminal detection
3. Implement graceful fallback for non-color terminals
4. Test visual appearance across different terminal widths

### Phase 3: Testing and Validation (45 minutes)
1. Update existing tests for new behavior
2. Add tests for color support detection
3. Test in various terminal environments (TTY, pipe, NO_COLOR)
4. Manual testing with various timeout durations

## Testing Strategy

### Unit Tests
- Verify progress calculation reaches exactly 1.0 at timeout
- Test bar generation produces correct character counts
- Validate immediate completion shows full bar
- Test color output with and without terminal support
- Verify NO_COLOR environment variable handling

### Integration Tests
- Run examples with various timeout settings
- Verify visual consistency across different scenarios
- Test with both quick completions and timeouts

### Manual Validation
```bash
# Test with short timeout
./dev_cli.py -i 3 --timeout 1.0 examples/test.py

# Test with long timeout  
./dev_cli.py -i 5 --timeout 10.0 examples/test.py

# Test with mixed results
./dev_cli.py examples/relevance/examples.py

# Test without color support
NO_COLOR=1 ./dev_cli.py -i 3 examples/test.py

# Test with pipe (no TTY)
./dev_cli.py -i 3 examples/test.py | cat
```

## Success Criteria

1. Progress bars always fill the entire width over timeout duration
2. Visual feedback accurately represents time remaining
3. Progress bars display in orange/amber when terminal supports color
4. Graceful fallback to non-colored progress bars when needed
5. No visual artifacts or alignment issues
6. All existing tests pass with updated behavior
7. Clean, maintainable implementation without decorators

## Risk Mitigation

- **Risk**: Users confused by changed behavior
  - **Mitigation**: Clear visual indication that bar represents timeout duration
  
- **Risk**: Performance impact from more frequent updates
  - **Mitigation**: Maintain 100ms update interval, optimize calculations

- **Risk**: Color codes breaking in certain terminals
  - **Mitigation**: Implement robust terminal detection and NO_COLOR support
  
- **Risk**: Accessibility issues with color choice
  - **Mitigation**: Orange/amber chosen for good visibility; progress bar symbols remain primary indicator

## Future Considerations

This refactor lays groundwork for potential future enhancements:
- Configurable bar width based on terminal size
- Different bar styles for different operation types
- User-configurable color themes
- Additional color states (green for complete, red for timeout)

## References

- [Unified Progress System Spec](043_unified_progress_system_implementation.md)
- [Progress Module Documentation](../../../src/model_checker/output/progress/README.md)
- [Code Standards](../../../maintenance/CODE_STANDARDS.md)