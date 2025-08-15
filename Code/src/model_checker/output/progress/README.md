# Unified Progress Tracking System

[← Back to Output](../README.md) | [Core Module →](core.py) | [Animated Progress →](animated.py) | [Display Handlers →](display.py)

## Directory Structure

```
progress/
├── README.md              # This file - progress system documentation
├── __init__.py           # Module exports and initialization
├── core.py               # Core progress tracking interface
├── animated.py           # Animated progress bar implementations
├── display.py            # Display handlers for different environments
├── spinner.py            # Simple spinner for indeterminate operations
└── tests/                # Comprehensive test suite
    ├── README.md         # Test documentation and coverage guide
    ├── __init__.py
    ├── test_animated.py  # Tests for animated progress bars
    ├── test_core.py      # Tests for UnifiedProgress and ProgressBar
    ├── test_display.py   # Tests for display adapters
    └── test_spinner.py   # Tests for spinner component
```

## Overview

The **Unified Progress Tracking System** provides consistent, animated progress feedback during model checking operations, enhancing user experience with real-time status updates and visual progress indicators. This module implements a clean, extensible architecture that seamlessly integrates with the ModelChecker framework while maintaining theory independence.

The progress system addresses the need for **clear operation feedback** during potentially long-running model searches, providing users with immediate visual confirmation of activity, progress toward completion, and insight into the search process through metrics like models checked and isomorphic models skipped.

Following ModelChecker's **core development principles**, the progress system avoids backwards compatibility concerns, uses simple inheritance without decorators, and maintains clean separation between display logic and progress tracking logic. The implementation prioritizes clarity and maintainability over complex abstractions.

## Key Features

### Visual Progress Tracking

- **Time-based Animation**: Progress bars fill over the configured timeout duration
- **Immediate Completion**: Instant visual feedback when models are found
- **Clear Status Display**: Shows model number, skip counts, and elapsed time
- **Responsive Updates**: 100ms refresh rate for smooth animation
- **Color Support**: Orange/amber progress bars in color-capable terminals

### Intelligent Display Management

- **Terminal Detection**: Automatically enables/disables based on output environment
- **Width Adaptation**: Adjusts to terminal width to prevent wrapping
- **Clean Line Management**: Proper carriage return handling and line clearing
- **Batch Mode Support**: Silent operation for non-interactive environments

### Seamless Integration

- **Theory Agnostic**: Works with all semantic theories without modification
- **Automatic Activation**: No manual setup required when iterate > 1
- **Unified Interface**: Consistent behavior across initial and iteration searches
- **Clean Spacing**: Smart spacing management for report formatting

## Usage Examples

### Basic Configuration

Progress tracking activates automatically when iteration is requested:

```python
# In your example file
EXAMPLE_settings = {
    'N': 3,        # State count
    'iterate': 4,  # Find 4 models (enables progress)
    'max_time': 5, # 5 seconds timeout for all operations
}
```

Note: The `iteration_timeout` setting has been removed. All timeout control is now unified under the `max_time` setting.

### Output Format

When `iterate > 1`, users see animated progress bars:

```
Finding non-isomorphic models: [████████████████████] 1/4 0.3s

[Model 1 output...]

Finding non-isomorphic models: [████████████████████] 2/4 (2 skipped) 1.2s

[Model 2 output...]

Finding non-isomorphic models: [████████████████████] 3/4 (6 skipped) 2.1s

[Model 3 output...]

Finding non-isomorphic models: [██████░░░░░░░░░░░░░░] 4/4 (12 skipped) 5.0s

ITERATION REPORT
    Model 1: Initial model (0.01s)
    Model 2: Found after skipping 2 isomorphic models (1.15s)
    Model 3: Found after skipping 4 isomorphic models (0.87s)
    Model 4: Not found - timeout after 5s after checking 45 models (5.00s)

Total: 3/4 models found, 6 isomorphic models skipped, 6.32s elapsed
```

### Special Cases

When `iterate=1`, no progress bars are shown:

```python
# No progress tracking for single model
SINGLE_settings = {
    'N': 3,
    'iterate': 1,  # No progress bars shown
}
```

## Architecture

### Component Overview

```
BuildModule
    │
    ├─> UnifiedProgress (core.py)
    │       ├─> Manages overall progress state
    │       ├─> Coordinates multiple progress bars
    │       └─> Handles timing and statistics
    │
    ├─> TimeBasedProgress (animated.py)
    │       ├─> Implements animated progress bars
    │       ├─> Runs animation in background thread
    │       └─> Updates based on elapsed time
    │
    └─> ProgressDisplay (display.py)
            ├─> TerminalDisplay: Interactive terminals
            └─> BatchDisplay: Non-interactive environments
```

### Integration Flow

1. **BuildModule** creates UnifiedProgress when iterate > 1
2. **UnifiedProgress** creates TimeBasedProgress for each model search
3. **BaseModelIterator** calls progress hooks during search
4. **TimeBasedProgress** animates in background thread
5. **ProgressDisplay** handles terminal output

### Key Classes

#### UnifiedProgress (core.py)

- Central coordinator for all progress tracking
- Manages multiple model search progress bars
- Tracks cumulative statistics across searches
- Handles graceful cleanup on completion

#### TimeBasedProgress (animated.py)

- Animated progress bar implementation
- Time-based filling animation
- Background thread for smooth updates
- Immediate completion on model found

#### ProgressDisplay (display.py)

- Abstract interface for display handlers
- TerminalDisplay for interactive sessions
- BatchDisplay for non-interactive environments
- Clean line management and clearing

## Implementation Details

### Threading Model

The progress system uses Python threading for smooth animation:

```python
# Animation runs in daemon thread
self.thread = threading.Thread(target=self._animate)
self.thread.daemon = True  # Won't block program exit
self.thread.start()
```

### Progress Calculation

Progress fills based on elapsed time vs timeout:

```python
elapsed = time.time() - self.start_time
progress = min(1.0, elapsed / self.timeout)
filled = int(bar_width * progress)
```

### Display Updates

Terminal updates use carriage returns for in-place updates:

```python
# Clear line and update
self.stream.write(f"\r{message.ljust(terminal_width)}")
self.stream.flush()
```

### Spacing Management

Intelligent spacing before ITERATION REPORT:

```python
# Check if timeout left blank line
needs_spacing = True
if self.search_stats:
    last_search = self.search_stats[-1]
    if "timeout" in last_search.termination_reason:
        needs_spacing = False  # Already have space
```

## Testing

### Comprehensive Test Suite

The progress module includes a thorough test suite with 54 tests providing complete coverage of all components:

```bash
# Run all progress tests (54 tests)
pytest src/model_checker/output/progress/tests/ -xvs

# Run specific test file
pytest src/model_checker/output/progress/tests/test_animated.py -xvs

# Run with verbose output
pytest src/model_checker/output/progress/tests/ -v
```

### Test Coverage

The test suite ensures comprehensive coverage across all modules:

- **[test_core.py](tests/test_core.py)**: 14 tests for UnifiedProgress and ProgressBar
  - Single and multiple model progress tracking
  - Isomorphic skip counting and timing
  - Edge cases: zero models, custom start times
  - Abstract interface verification
  
- **[test_animated.py](tests/test_animated.py)**: 9 tests for TimeBasedProgress
  - Time-based animation behavior
  - Thread lifecycle management
  - Color support detection
  - Progress bar visual rendering
  
- **[test_display.py](tests/test_display.py)**: 18 tests for display adapters
  - ProgressDisplay abstract interface
  - TerminalDisplay carriage return handling
  - BatchDisplay no-op behavior
  - Terminal width adaptation
  
- **[test_spinner.py](tests/test_spinner.py)**: 13 tests for Spinner component
  - Animation character cycling
  - Thread creation and cleanup
  - Start/stop behavior
  - Custom message formatting

See [tests/README.md](tests/README.md) for detailed test documentation and coverage guidelines.

### Integration Testing

Test with real model checking examples:

```bash
# Test with iteration progress
I./dev_cli.py examples/my_example.py

# Test timeout behavior  
./dev_cli.py examples/timeout_example.py

# Test with different theories
./dev_cli.py -l logos examples/logos_example.py
```

## Development Guidelines

### Adding New Progress Types

To add a new progress bar type:

1. Extend AnimatedProgressBar base class
2. Implement \_animate() method
3. Handle complete() for cleanup
4. Add tests for new behavior

### Modifying Display Behavior

Display customization points:

- Subclass ProgressDisplay for new environments
- Override update/complete/clear methods
- Maintain terminal width awareness
- Handle special characters properly

### Performance Considerations

- Animation thread updates every 100ms
- Minimal CPU usage during animation
- Proper thread cleanup on completion
- No progress overhead when iterate=1

## Troubleshooting

### Common Issues

**Progress bars not showing:**

- Check if output is to terminal (not pipe/file)
- Verify iterate > 1 in settings
- Ensure UnifiedProgress is created

**Double spacing in output:**

- Timeout handling creates natural spacing
- Non-timeout cases add explicit spacing
- Check ITERATION REPORT spacing logic

**Animation stuttering:**

- Thread scheduling on busy systems
- Consider increasing update interval
- Check for blocking operations

### Debug Mode

Enable debug logging:

```python
import logging
logging.getLogger('model_checker.output.progress').setLevel(logging.DEBUG)
```

## References

### Related Documentation

- **[Output System Overview](../README.md)** - Parent module documentation
- **[Builder Integration](../../builder/module.py)** - Progress creation logic
- **[Iterator Integration](../../iterate/core.py)** - Progress update hooks
- **[Code Standards](../../../maintenance/CODE_STANDARDS.md)** - Development guidelines

### Design Decisions

- No decorators per repository standards
- Simple inheritance over complex abstractions
- Thread safety through minimal shared state
- Terminal detection for automatic enable/disable

---

[← Back to Output](../README.md) | [Core Module →](core.py) | [Animated Progress →](animated.py) | [Testing →](tests/)
