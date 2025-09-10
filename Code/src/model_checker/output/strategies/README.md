# Output Strategies: Save Timing and Mode Control

[← Back to Output](../README.md) | [Formatters →](../formatters/README.md) | [Progress →](../progress/README.md)

## Directory Structure

```
strategies/
├── README.md          # This file - strategy subsystem documentation
├── __init__.py        # Package initialization and exports
├── base.py            # Abstract base strategy class
├── batch.py           # Batch mode - save all at end
├── sequential.py      # Sequential mode - save immediately
└── interactive.py     # Interactive mode - user-controlled saves
```

## Overview

The **strategies subsystem** implements the strategy pattern for controlling when and how model checking results are saved to disk. Each strategy encapsulates a different approach to output timing, allowing the framework to adapt to various use cases - from batch processing to interactive exploration - without modifying core logic.

This separation of concerns enables flexible output behavior while maintaining clean architecture. The strategies work in conjunction with formatters to provide a complete output solution that can handle everything from single examples to large-scale batch processing.

## Architecture

### Design Pattern

The strategies implement a **strategy pattern** where:
- `OutputStrategy` defines the abstract interface all strategies must implement
- Each concrete strategy (Batch, Sequential, Interactive) provides specific timing behavior
- The `OutputManager` delegates to the active strategy for save decisions
- Strategies maintain state about accumulated results as needed

### Class Hierarchy

```
OutputStrategy (abstract)
├── BatchStrategy        # Accumulate all, save at end
├── SequentialStrategy   # Save each result immediately
└── InteractiveStrategy  # Save on user request
```

## Strategies

### OutputStrategy (Base)

Abstract base class defining the strategy interface:

```python
from model_checker.output.strategies.base import OutputStrategy

class CustomStrategy(OutputStrategy):
    def should_save_immediately(self) -> bool:
        """Determine if results should be saved now."""
        return False
    
    def accumulate(self, example_name: str, formatted_outputs: Dict[str, str]):
        """Store results for later saving."""
        pass
    
    def get_accumulated(self) -> Dict[str, Dict[str, str]]:
        """Retrieve all accumulated results."""
        return {}
```

### BatchStrategy

Accumulates all results and saves at the end:

```python
from model_checker.output.strategies import BatchStrategy

strategy = BatchStrategy()

# During processing
strategy.accumulate('EXAMPLE_1', {
    'markdown': '# Example 1\n...',
    'json': '{"example": "1", ...}'
})
strategy.accumulate('EXAMPLE_2', {...})

# At the end
if not strategy.should_save_immediately():
    all_results = strategy.get_accumulated()
    # Save all results together
```

**Use Cases**:
- Processing multiple examples in a module
- Generating consolidated output files
- Minimizing I/O operations during processing
- Creating summary reports

### SequentialStrategy

Saves each result immediately as it's generated:

```python
from model_checker.output.strategies import SequentialStrategy

strategy = SequentialStrategy(sequential_files='multiple')

# Each result is saved immediately
if strategy.should_save_immediately():
    # Save to individual files
    save_formatted_outputs(formatted_outputs)
```

**Configuration Options**:
- `sequential_files='multiple'`: Each example in separate file
- `sequential_files='single'`: Append to single file

**Use Cases**:
- Long-running computations where partial results are valuable
- Memory-constrained environments
- Real-time result monitoring
- Debugging and development

### InteractiveStrategy

User controls when to save results:

```python
from model_checker.output.strategies import InteractiveStrategy

strategy = InteractiveStrategy()

# Accumulate results
strategy.accumulate('EXAMPLE_1', formatted_outputs)

# Check if user wants to save
if strategy.should_save_immediately():
    # Based on user interaction in OutputManager
    save_formatted_outputs(formatted_outputs)
```

**Features**:
- User prompts for save decisions
- Selective example saving
- Interactive exploration mode
- Manual control over output

## Usage Patterns

### Basic Strategy Selection

```python
from model_checker.output.strategies import (
    BatchStrategy, 
    SequentialStrategy, 
    InteractiveStrategy
)
from model_checker.output.config import OutputConfig

# Based on configuration
config = OutputConfig.from_cli_args(args)

if config.mode == 'batch':
    strategy = BatchStrategy()
elif config.mode == 'sequential':
    strategy = SequentialStrategy(config.sequential_files)
else:  # interactive
    strategy = InteractiveStrategy()
```

### Integration with OutputManager

```python
from model_checker.output import OutputManager

# OutputManager uses strategy internally
manager = OutputManager(build_module)
# Strategy is selected based on configuration

# During example processing
manager.save_example('TEST_1', example_data, formatted_output)
# Strategy determines if saved immediately or accumulated
```

### Custom Strategy Implementation

```python
from model_checker.output.strategies.base import OutputStrategy

class ThresholdStrategy(OutputStrategy):
    """Save after accumulating N examples."""
    
    def __init__(self, threshold: int = 10):
        self.threshold = threshold
        self.accumulated = {}
    
    def should_save_immediately(self) -> bool:
        return len(self.accumulated) >= self.threshold
    
    def accumulate(self, example_name: str, formatted_outputs: Dict[str, str]):
        self.accumulated[example_name] = formatted_outputs
        if self.should_save_immediately():
            # Trigger save and reset
            self.flush()
    
    def get_accumulated(self) -> Dict[str, Dict[str, str]]:
        return self.accumulated
```

## Configuration

Strategies are configured via command-line arguments and `OutputConfig`:

```bash
# Batch mode (default)
python -m model_checker examples.py

# Sequential mode with multiple files
python -m model_checker examples.py --output-mode sequential

# Sequential mode with single file
python -m model_checker examples.py --output-mode sequential --sequential-files single

# Interactive mode
python -m model_checker examples.py --interactive
```

## State Management

Different strategies manage state differently:

### BatchStrategy
- Maintains dictionary of all accumulated results
- Memory usage grows with number of examples
- State cleared after final save

### SequentialStrategy
- Minimal state (configuration only)
- No accumulation of results
- Constant memory usage

### InteractiveStrategy
- Accumulates results until user saves
- Maintains interaction state
- Selective clearing based on user choice

## Performance Considerations

### BatchStrategy
- **Pros**: Minimal I/O operations, efficient for bulk processing
- **Cons**: Higher memory usage, no partial results

### SequentialStrategy
- **Pros**: Constant memory usage, immediate results
- **Cons**: More I/O operations, potential performance impact

### InteractiveStrategy
- **Pros**: User control, selective saving
- **Cons**: Requires user interaction, variable memory usage

## Testing

The strategies have comprehensive test coverage:

```bash
# Unit tests for each strategy
pytest src/model_checker/output/tests/unit/test_strategies.py

# Integration tests
pytest src/model_checker/output/tests/integration/test_output_modes.py
```

## Extension Points

### Adding New Strategies

1. Create a new strategy class extending `OutputStrategy`
2. Implement required methods
3. Register in `__init__.py`
4. Update `OutputConfig` to recognize new mode

### Strategy Composition

Strategies can be composed for complex behavior:

```python
class HybridStrategy(OutputStrategy):
    """Combine multiple strategies based on conditions."""
    
    def __init__(self):
        self.batch = BatchStrategy()
        self.sequential = SequentialStrategy()
    
    def should_save_immediately(self) -> bool:
        # Use sequential for errors, batch for success
        if self.current_has_error:
            return self.sequential.should_save_immediately()
        return self.batch.should_save_immediately()
```

## Related Components

- **[Output Manager](../manager.py)** - Uses strategies for save timing
- **[Output Formatters](../formatters/README.md)** - Generate content to save
- **[Output Configuration](../config.py)** - Configures strategy selection
- **[Interactive Module](../interactive.py)** - Interactive mode support

---

[← Back to Output](../README.md) | [Formatters →](../formatters/README.md) | [Progress →](../progress/README.md)