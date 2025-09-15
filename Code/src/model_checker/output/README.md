# Output Management: Multi-Format Result Generation and Control

[← Back to ModelChecker](../../README.md) | [API Documentation →](../README.md) | [Interactive Save Guide →](../../../docs/INTERACTIVE_SAVE.md)

## Directory Structure

```
output/
├── README.md               # This file - output subsystem documentation
├── __init__.py            # Module exports and initialization
├── config.py              # Output configuration management
├── constants.py           # Centralized constants and defaults
├── errors.py              # Custom exception classes
├── manager.py             # Core OutputManager orchestrator
├── collectors.py          # Model data collection utilities
├── helpers.py             # Utility functions for output processing
├── interactive.py         # Interactive save mode manager
├── prompts.py            # User prompt utilities
├── input_provider.py     # Input abstraction for testing
├── formatters/           # Output format generators
│   ├── base.py           # Abstract formatter interface
│   ├── markdown.py       # Markdown documentation generator
│   ├── json.py           # JSON data serialization
│   └── notebook.py       # Jupyter notebook integration adapter
├── strategies/           # Save timing strategies
│   ├── base.py           # Abstract strategy interface
│   ├── batch.py          # Accumulate and save at end
│   ├── sequential.py     # Save immediately
│   └── interactive.py    # User-controlled saving
├── notebook/             # Notebook generation subsystem
│   ├── streaming_generator.py  # Efficient streaming notebook builder
│   └── [various]         # Template and cell management
├── progress/             # Progress indication utilities
│   └── [various]         # Spinner and progress components
└── tests/                # Comprehensive test suite
    ├── unit/            # Unit tests for components
    ├── integration/     # Integration tests
    └── e2e/            # End-to-end scenarios
```

## Overview

The **Output Management subsystem** provides a flexible, extensible framework for generating and managing model checking results in multiple formats. Built on the strategy pattern, it separates concerns between format generation (formatters), save timing (strategies), and overall orchestration (manager), enabling clean architecture and easy extension.

### Key Design Principles

- **Separation of Concerns**: Format generation, save timing, and orchestration are independent
- **Strategy Pattern**: Both formatters and save strategies use pluggable implementations
- **Configuration-Driven**: Behavior controlled through centralized configuration
- **Testability**: All components designed for easy testing with minimal mocking
- **Extensibility**: New formats and strategies can be added without modifying core logic

## Core Components

### OutputManager

The central orchestrator that coordinates ALL output operations through a unified pipeline:

```python
from model_checker.output import OutputManager
from model_checker.output.config import OutputConfig

# Initialize with configuration
config = OutputConfig.from_cli_args(args)
manager = OutputManager(config, interactive_manager)

# Set module context for notebook generation
manager.set_module_context(module_vars, source_path)

# Save an example result
manager.save_example('EXAMPLE_1', example_data, formatted_output)

# Finalize all outputs including notebooks
manager.finalize()
```

**Responsibilities**:
- Coordinate formatters and strategies through unified pipeline
- Manage output directory creation
- Handle interactive user prompts
- Collect and organize model data
- Generate ALL output formats including notebooks

### Output Configuration

Centralized configuration for all output behavior with full CLI integration:

```python
from model_checker.output.config import OutputConfig

# Create from CLI arguments (handles new --save flag)
config = OutputConfig.from_cli_args(args)

# Or create manually
config = OutputConfig(
    formats=['markdown', 'json', 'notebook'],  # All formats unified
    mode='batch',
    sequential_files='multiple',
    save_output=True
)

# Check enabled formats
if config.is_format_enabled('notebook'):
    # Notebook generated through unified pipeline
    pass

# CLI Usage:
# --save                    # Save ALL formats (markdown, json, notebook)
# --save markdown           # Save only markdown
# --save markdown jupyter   # Save markdown and notebook
# --save json markdown  # Save specific formats
```

### Formatters

Transform model checking results into different output formats:

```python
from model_checker.output.formatters import (
    MarkdownFormatter,
    JSONFormatter, 
    JupyterNotebookFormatter
)

# Format results for human reading
markdown = MarkdownFormatter().format(example_data)

# Format for data analysis
json_str = JSONFormatter().format(example_data)

# Create interactive notebook
notebook = JupyterNotebookFormatter().format(example_data)
```

**Available Formatters**:
- **MarkdownFormatter**: Human-readable documentation with mathematical notation
- **JSONFormatter**: Complete data serialization for analysis
- **JupyterNotebookFormatter**: Interactive notebooks for exploration

See [formatters/README.md](formatters/README.md) for detailed documentation.

### Strategies

Control when results are saved to disk:

```python
from model_checker.output.strategies import (
    BatchStrategy,
    SequentialStrategy,
    InteractiveStrategy
)

# Batch: accumulate all, save at end
batch = BatchStrategy()

# Sequential: save each immediately
sequential = SequentialStrategy(sequential_files='multiple')

# Interactive: user controls saving
interactive = InteractiveStrategy()
```

**Available Strategies**:
- **BatchStrategy**: Minimize I/O, save all at once
- **SequentialStrategy**: Immediate results, constant memory
- **InteractiveStrategy**: User-controlled selective saving

See [strategies/README.md](strategies/README.md) for detailed documentation.

## Usage Patterns

### Basic Usage

```python
from model_checker.builder import BuildModule

# Load module with examples
build_module = BuildModule(flags)

# OutputManager handles everything through unified pipeline
# (created automatically by BuildModule with module context)
build_module.run_examples()

# All formats generated through unified architecture
# Results saved according to configuration
```

### Command-Line Control

```bash
# Generate all formats (markdown, json, notebook)
python -m model_checker examples.py --save

# Generate specific formats
python -m model_checker examples.py --save markdown jupyter

# Sequential mode with immediate saves
python -m model_checker examples.py --save --output-mode sequential

# Interactive mode with user control
python -m model_checker examples.py --save --interactive
```

### Programmatic Usage

```python
from model_checker.output import OutputManager
from model_checker.output.config import OutputConfig

# Custom configuration
config = OutputConfig(
    formats=['markdown', 'notebook'],
    mode='sequential',
    sequential_files='single'
)

# Create manager with custom config
manager = OutputManager(config, interactive_manager=None)

# Set module context for notebook generation
manager.set_module_context(module_vars, source_path)

# Process examples
for name, example in examples.items():
    result = process_example(example)
    manager.save_example(name, result, formatted_output)

# Finalize if needed
manager.finalize()
```

## Interactive Mode

The interactive mode provides user control over saving:

```python
from model_checker.output.interactive import InteractiveSaveManager

# Created automatically when --interactive flag is used
interactive_manager = InteractiveSaveManager(input_provider)

# User prompts for each example
response = interactive_manager.prompt_for_save('EXAMPLE_1')
if response in ['y', 'a']:  # yes or all
    # Save the example
    pass
```

**Interactive Options**:
- `y` - Save current example
- `n` - Skip current example
- `a` - Save all remaining examples
- `s` - Stop processing

## Input Provider Pattern

For testability, user input is abstracted:

```python
from model_checker.output import ConsoleInputProvider, MockInputProvider

# Production: real user input
input_provider = ConsoleInputProvider()

# Testing: predetermined responses
mock_provider = MockInputProvider(['a', 'y', 'n'])
test_manager = InteractiveSaveManager(mock_provider)
```

## Model Data Collection

The `collectors` module extracts structured data from models:

```python
from model_checker.output.collectors import collect_model_data

# Extract all model information
model_data = collect_model_data(
    model_structure,
    propositions_list,
    print_model_callback
)

# Returns structured dictionary with:
# - states and their properties
# - relations between states
# - proposition evaluations
# - formatted output
```

## Unified Architecture

The output package implements a **unified pipeline** where ALL output formats (markdown, json, notebook) are generated through the same architecture:

### Key Benefits
- **Single Responsibility**: OutputManager handles all format generation
- **No Duplicate Logic**: All formats use the same save strategies
- **Consistent Behavior**: `--save` generates all formats uniformly
- **Easy Extension**: New formats integrate through the same pipeline

### Architecture Flow
1. **Configuration**: OutputConfig determines enabled formats
2. **Context Setup**: Module variables passed via `set_module_context()`
3. **Example Processing**: Each example saved through formatters
4. **Finalization**: All formats generated including notebooks

### Notebook Integration
Notebooks are generated through the unified pipeline using:
- **NotebookFormatter**: Adapter between formatter interface and streaming generator
- **StreamingNotebookGenerator**: Efficient notebook creation without memory overhead
- **Module Context**: Semantic theories and settings passed through OutputManager

## File Organization

Output files are organized in a clear structure:

```
ModelChecker_Outputs_TIMESTAMP/
├── EXAMPLES.md                  # Combined markdown with model outputs
├── MODELS.json                  # Combined JSON with model data
├── NOTEBOOK.ipynb               # Runnable Jupyter notebook (no outputs)
└── summary.json                 # Summary data (interactive mode only)
```

## Configuration Options

### Format Selection (New Consolidated --save Flag)
- `--save` - Save all formats (markdown, json, notebook)
- `--save markdown` - Save only markdown format
- `--save json markdown` - Save specific formats
- No --save flag - No output saved

### Output Modes
- `--output-mode batch` - Save all at end (default)
- `--output-mode sequential` - Save immediately
- `--interactive` - User-controlled saving (overrides all settings)
- `interactive: True` in settings - Enable interactive mode without CLI flag

### Sequential Options
- `--sequential-files multiple` - Separate file per example
- `--sequential-files single` - Append to single file

### Interactive Mode Priority
The interactive mode follows a clear priority order:
1. `--interactive` CLI flag (highest priority - always wins)
2. `--output-mode` CLI flag (overrides settings but not --interactive)
3. `interactive` setting in general_settings (enables interactive by default)
4. Default to batch mode if no configuration

## Testing

The output subsystem has comprehensive test coverage (97% as of 2025-01-10):

```bash
# Run all output tests (251 tests)
pytest src/model_checker/output/tests/

# Unit tests only (including new config, errors, helpers tests)
pytest src/model_checker/output/tests/unit/

# Integration tests
pytest src/model_checker/output/tests/integration/

# End-to-end tests
pytest src/model_checker/output/tests/e2e/

# Run with coverage report
pytest src/model_checker/output/tests/ --cov=src/model_checker/output
```

**Test Coverage Highlights**:
- Overall: 97% coverage (3046/3154 statements)
- config.py: 100% coverage (comprehensive CLI parsing tests)
- errors.py: 100% coverage (all exception classes tested)
- helpers.py: 100% coverage (all utilities validated)
- 251 total tests, all passing

## Extension Points

### Adding New Formats

1. Create formatter extending `BaseFormatter`
2. Implement `format()` and `get_extension()`
3. Register in `formatters/__init__.py`
4. Update `OutputConfig` for CLI support

### Adding New Strategies

1. Create strategy extending `OutputStrategy`
2. Implement required methods
3. Register in `strategies/__init__.py`
4. Update configuration handling

### Custom Output Processing

```python
from model_checker.output.helpers import process_custom_output

# Add custom processing step
def custom_processor(data):
    # Transform data
    return processed_data

# Use in output pipeline
processed = custom_processor(model_data)
```

## Performance Considerations

- **Memory Usage**: Batch mode accumulates all results in memory
- **I/O Operations**: Sequential mode performs more disk writes
- **Format Generation**: Notebook generation has higher overhead
- **Large Models**: Consider sequential mode for memory efficiency

## Error Handling

Custom exceptions for clear error reporting:

```python
from model_checker.output.errors import (
    OutputError,
    FormatterError,
    StrategyError
)

try:
    manager.save_example(name, data, output)
except OutputError as e:
    # Handle output-specific errors
    print(f"Output failed: {e}")
```

## Related Documentation

- **[Formatters Documentation](formatters/README.md)** - Detailed formatter information
- **[Strategies Documentation](strategies/README.md)** - Strategy pattern details
- **[Progress Indicators](progress/README.md)** - Progress display components
- **[Test Documentation](tests/README.md)** - Testing approach and coverage
- **[Interactive Save Guide](../../../docs/INTERACTIVE_SAVE.md)** - User guide for interactive mode

## See Also

### Conceptual Documentation
- **[Architecture Overview](../../../../Docs/methodology/ARCHITECTURE.md)** - System design philosophy
- **[Output Methodology](../../../../Docs/methodology/OUTPUT.md)** - Output generation concepts

### Technical Documentation
- **[Technical Architecture](../../../docs/ARCHITECTURE.md)** - Output subsystem architecture
- **[Development Guide](../../../docs/DEVELOPMENT.md)** - Contributing to output system
- **[Testing Guide](../../../docs/TESTS.md)** - Testing output components

### Related Components
- **[Builder Package](../builder/README.md)** - Generates models for output
- **[Jupyter Package](../jupyter/README.md)** - Interactive notebook output
- **[Settings Package](../settings/README.md)** - Output configuration settings

---

[← Back to ModelChecker](../../README.md) | [API Documentation →](../README.md) | [Interactive Save Guide →](../../../docs/INTERACTIVE_SAVE.md)