# Unified Progress System

This module provides a unified progress tracking system for ModelChecker that displays consistent, animated progress bars during model checking and iteration.

## Features

- **Animated Progress Bars**: Progress bars that fill over the `iteration_timeout` duration
- **Immediate Completion**: When a model is found, the progress bar immediately fills to 100%
- **Unified Interface**: Same progress system for both initial model search and iteration
- **Theory Agnostic**: Works automatically with all theories without modification
- **Terminal Aware**: Only displays progress in interactive terminals (not in pipes/redirects)

## Usage

The progress system is automatically integrated with BuildModule and the iteration system. No manual setup is required.

### Example Output

When running with `iterate > 1`, you'll see animated progress bars:

```
Model 1/3: [████████████████████] FOUND (1 checked) 0.3s
Model 2/3: [████████████████████] FOUND (3 checked, 2 skipped) 1.2s
Model 3/3: [██████░░░░░░░░░░░░░░] NOT FOUND (5 checked) 2.0s
```

### Configuration

Progress bars use the `iteration_timeout` setting to determine animation speed:

```python
settings = {
    'iterate': 3,                # Find 3 models
    'iteration_timeout': 5.0,    # 5 seconds per model search
}
```

## Architecture

### Core Components

1. **UnifiedProgress** (`core.py`): Main progress tracking interface
2. **TimeBasedProgress** (`animated.py`): Animated progress bar implementation
3. **ProgressDisplay** (`display.py`): Terminal display handling

### Integration Points

- **BuildModule**: Creates UnifiedProgress instance and passes to iterator
- **BaseModelIterator**: Uses UnifiedProgress hooks for progress updates
- **Theory Iterators**: No changes needed - progress works through base class

## Testing

Run the test suite:

```bash
pytest src/model_checker/output/progress/tests/
```

Test with a real example:

```python
# In your example file
settings = {
    'N': 3,
    'iterate': 3,
    'iteration_timeout': 2.0,
}
```

## Implementation Details

The progress system uses threading for animation while the main thread searches for models. Progress bars update every 100ms and show:

- Current model number and total
- Visual progress bar
- Number of models checked
- Number of isomorphic models skipped (if any)
- Elapsed time

The system gracefully handles:
- Early termination (timeout, exhausted search space)
- Keyboard interrupts
- Non-terminal environments (disables progress)
- Different terminal widths