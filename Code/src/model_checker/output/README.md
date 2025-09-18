# Output Management: Simplified Multi-Format Result Generation

[← Back to ModelChecker](../../README.md) | [API Documentation →](../README.md)

## Directory Structure

```
output/
├── README.md                       # This file - output subsystem documentation
├── __init__.py                     # Module exports and initialization
├── config.py                       # Simple output configuration
├── constants.py                    # Format constants only
├── errors.py                       # Custom exception classes
├── manager.py                      # Simplified OutputManager
├── collectors.py                   # Model data collection utilities
├── helpers.py                      # Utility functions for output processing
├── sequential_manager.py           # Sequential save manager
├── prompts.py                      # User prompt utilities
├── input_provider.py               # Input abstraction for testing
├── formatters/                     # Output format generators
│   ├── base.py                     # Abstract formatter interface
│   ├── markdown.py                 # Markdown documentation generator
│   ├── json.py                     # JSON data serialization
│   └── notebook.py                 # Jupyter notebook integration
├── notebook/                       # Notebook generation subsystem
│   ├── streaming_generator.py      # Efficient streaming notebook builder
│   └── [various]                   # Template and cell management
├── progress/                       # Progress indication utilities
│   └── [various]                   # Spinner and progress components
└── tests/                          # Comprehensive test suite
    ├── unit/                       # Unit tests for components
    └── integration/                # Integration tests
```

## Overview

The **Output Management subsystem** provides a clean, simple framework for generating model checking results in multiple formats. The architecture has been dramatically simplified to eliminate unnecessary abstractions while maintaining functionality.

### Key Design Principles

- **Simplicity First**: One boolean flag instead of complex modes
- **Direct Logic**: No unnecessary abstraction layers or patterns
- **Clear Behavior**: Either batch save or sequential save, nothing else
- **No Backwards Compatibility**: Clean breaks for cleaner code

## Architecture

### Core Components

#### OutputConfig
Simple configuration with three fields:
- `formats`: List of formats to generate
- `sequential`: Boolean flag for sequential mode
- `save_output`: Whether saving is enabled

#### OutputManager
Handles output with direct, simple logic:
- Accumulates outputs in batch mode
- Saves immediately in sequential mode
- No strategy pattern, no complex modes

#### SequentialSaveManager
Manages user interaction:
- Prompts for save decisions
- Tracks model numbers
- Handles directory change prompts

### Removed Components

The following have been completely removed:
- All strategy classes (BatchStrategy, SequentialStrategy, etc.)
- Mode constants (MODE_BATCH, MODE_SEQUENTIAL, MODE_INTERACTIVE)
- Strategy pattern infrastructure
- Complex configuration options

## Usage Examples

### Command Line Interface

```bash
# Batch mode (default) - save all at end
python -m model_checker --save

# Sequential mode - ask before each save
python -m model_checker --save --sequential
python -m model_checker -s -q  # Short form
```

### Programmatic Usage

```python
from model_checker.output import OutputManager, OutputConfig, SequentialSaveManager

# Batch mode - accumulate and save at end
config = OutputConfig(
    formats=['markdown', 'json'],
    sequential=False  # Default
)
manager = OutputManager(config)
manager.save_example("example1", data1, output1)
manager.save_example("example2", data2, output2)
manager.finalize()  # Saves all accumulated outputs

# Prompted mode - save immediately with user confirmation
config = OutputConfig(
    formats=['markdown', 'json'],
    sequential=True
)
sequential_manager = SequentialSaveManager()
manager = OutputManager(config, prompt_manager)
# User will be prompted for each save
```

### Settings Configuration

In theory semantic files:

```python
DEFAULT_GENERAL_SETTINGS = {
    "save_output": False,
    "sequential": False,  # Set to True for sequential mode
    # ... other settings
}
```

## Output Formats

Three formats are supported:

### Markdown (.md)
Human-readable documentation with:
- Formatted model structures
- Color-coded output (ANSI conversion)
- Clear section headers

### JSON (.json)
Machine-readable data with:
- Complete model data
- Metadata timestamps
- Structured format

### Notebook (.ipynb)
Interactive Jupyter notebooks with:
- Theory code cells
- Example execution
- Formatted results

## Directory Structures

### Batch Mode Output

All results saved at once:

```
output_20240115_123456/
├── EXAMPLES.md      # All examples in one markdown file
├── MODELS.json      # All model data in one JSON file
└── NOTEBOOK.ipynb   # Generated Jupyter notebook
```

### Prompted Mode Output

Individual saves per user approval:

```
output_20240115_123456/
├── EXAMPLE_1/
│   ├── MODEL_1.md   # First saved model
│   └── MODEL_1.json
├── EXAMPLE_2/
│   ├── MODEL_1.md   # Multiple models per example
│   ├── MODEL_2.md
│   └── MODEL_2.json
└── summary.json     # Summary of what was saved
```

## API Reference

### OutputConfig

```python
class OutputConfig:
    def __init__(self,
                 formats: List[str] = None,
                 sequential: bool = False,
                 save_output: bool = True)
```

### OutputManager

```python
class OutputManager:
    def __init__(self, config: OutputConfig, prompt_manager=None)
    def create_output_directory(self, custom_name: str = None)
    def save_example(self, example_name: str, example_data: Dict, output: str)
    def save_sequential_model(self, example_name: str, data: Dict, output: str, num: int)
    def finalize(self)
```

### SequentialSaveManager

```python
class SequentialSaveManager:
    def should_save(self, example_name: str) -> bool
    def should_find_more(self) -> bool
    def get_next_model_number(self, example_name: str) -> int
    def prompt_directory_change(self, output_dir: str) -> bool
```

## Testing

The package includes comprehensive tests:

```bash
# Run all output tests
pytest src/model_checker/output/tests/

# Run unit tests
pytest src/model_checker/output/tests/unit/

# Run integration tests
pytest src/model_checker/output/tests/integration/
```

## Migration Guide

If upgrading from the old system:

1. **CLI Changes**: 
   - Use `--sequential` flag for sequential mode
   - Remove any old mode-related flags

2. **Settings Changes**:
   - Use `"sequential": true` for sequential mode
   - Remove any mode-related settings

3. **Code Changes**:
   - Use `SequentialSaveManager` for sequential mode
   - Remove any strategy pattern code
   - Update imports to use simplified API

## Design Decisions

### Why Remove the Strategy Pattern?

The strategy pattern was overkill for a simple boolean choice. The entire pattern infrastructure (~800 lines) has been replaced with a simple if-statement in the manager.

### Why One Boolean Flag?

There are only two behaviors:
1. Save everything at the end (batch)
2. Ask before each save (sequential)

A boolean perfectly captures this choice.

### Why No Backwards Compatibility?

Following the maintenance standards: clean breaks lead to cleaner code. The migration is trivial (change a flag name) and the benefit is substantial (500+ lines removed).

## Performance Considerations

- **Batch mode**: More memory efficient for large result sets
- **Prompted mode**: Immediate disk writes, lower memory usage
- **Notebook generation**: Uses streaming for large outputs

## Error Handling

The package defines custom exceptions:
- `OutputError`: Base exception for output operations
- `OutputDirectoryError`: Directory creation failures
- `OutputIOError`: File I/O errors

## Future Enhancements

Possible improvements that maintain simplicity:
- Additional output formats (CSV, HTML)
- Parallel format generation
- Compression options

---

*For more details on the ModelChecker framework, see the [main documentation](../../README.md).*
