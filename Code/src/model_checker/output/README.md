# Output Management Module

[← Back to ModelChecker](../../README.md) | [API Documentation →](../README.md) | [Interactive Save Guide →](../../../docs/INTERACTIVE_SAVE.md)

## Directory Structure
```
output/
├── README.md               # This file - module documentation
├── __init__.py            # Module exports
├── manager.py             # Core OutputManager class
├── collectors.py          # Model data collection utilities
├── formatters.py          # Output formatting (Markdown, ANSI)
├── interactive.py         # Interactive save mode manager
├── prompts.py            # User prompt utilities
├── input_provider.py     # Input abstraction for testable user interaction
└── tests/                # Comprehensive test suite
```

## Overview

The **Output Management Module** provides comprehensive functionality for saving and organizing model checking results, supporting both batch and interactive workflows with structured file outputs and user-friendly formatting.

### Core Features

- **Flexible Save Modes**: Batch processing or interactive per-model saving
- **Structured Output**: Organized directory structure with JSON and Markdown formats
- **Interactive Workflow**: User prompts for selective model saving and iteration control
- **ANSI to Markdown**: Automatic color conversion for readable documentation
- **Model Data Collection**: Systematic extraction of model structure and properties

## API Reference

### Input Provider Pattern

The output module uses an **Input Provider abstraction** to handle user input in a testable way:

```python
from model_checker.output import ConsoleInputProvider, MockInputProvider

# Production usage with console input
input_provider = ConsoleInputProvider()
interactive_manager = InteractiveSaveManager(input_provider)

# Testing with predetermined responses
mock_provider = MockInputProvider(['a', 'y', 'n'])  # Responses for 3 prompts
test_manager = InteractiveSaveManager(mock_provider)
```

This pattern ensures:
- **Testability**: Tests can provide predetermined input without mocking stdin
- **Consistency**: All user input goes through a single abstraction
- **Flexibility**: Easy to add new input sources (files, GUIs, etc.)
- **No Backwards Compatibility**: Direct refactoring without legacy support

### OutputManager

The main class for managing output operations:

```python
from model_checker.output import OutputManager

# Basic usage
output_manager = OutputManager(
    save_output=True,
    mode='batch',  # or 'sequential'
    sequential_files='multiple'  # or 'single'
)

# With interactive mode
output_manager = OutputManager(
    save_output=True,
    interactive_manager=interactive_manager
)
```

#### Key Methods

- `create_output_directory(custom_name=None)`: Create timestamped output directory
- `save_example(example_name, model_data, formatted_output)`: Save in batch mode
- `save_model_interactive(example_name, model_data, formatted_output, model_num)`: Save individual model
- `finalize()`: Complete output process and write final files
- `should_save()`: Check if output saving is enabled

### InteractiveSaveManager

Manages interactive save workflow:

```python
from model_checker.output import InteractiveSaveManager, ConsoleInputProvider

# Create with input provider
input_provider = ConsoleInputProvider()
manager = InteractiveSaveManager(input_provider)

# Prompt for save mode
mode = manager.prompt_save_mode()  # Returns 'batch' or 'interactive'

# Set mode directly (e.g., from CLI flag)
manager.set_mode('interactive')

# Interactive workflow methods
should_save = manager.prompt_save_model("EXAMPLE_1")
find_more = manager.prompt_find_more_models()
manager.prompt_change_directory("/path/to/output")
```

### Formatters

Convert and format output data:

```python
from model_checker.output import MarkdownFormatter, ANSIToMarkdown

# Format model data as Markdown
formatter = MarkdownFormatter(use_colors=True)
markdown_output = formatter.format_example(model_data, raw_output)

# Convert ANSI colors to Markdown
converter = ANSIToMarkdown()
converted = converter.convert(ansi_text)
```

### Data Collectors

Extract structured data from models:

```python
from model_checker.output import ModelDataCollector

collector = ModelDataCollector()
model_data = collector.collect_model_data(
    model_structure,
    example_name,
    theory_name
)
```

## Usage Examples

### Basic Batch Mode

```python
# In examples file
general_settings = {
    "save_output": True
}

# Command line
model-checker -s examples/my_logic.py
```

Output structure:
```
output_20250804_123456/
├── EXAMPLES.md    # All examples in one file
└── MODELS.json    # Structured data for all models
```

### Interactive Mode

```python
# Command line with interactive flag
model-checker -s -I examples/my_logic.py

# Or programmatically
flags.save_output = True
flags.interactive = True
```

Interactive workflow:
1. Select save mode (if not specified)
2. After each model: "Save model for EXAMPLE_NAME? (Y/n)"
3. After save decision: "Find additional models? (y/N)"
4. At completion: "Change to output directory? (y/N)"

Output structure:
```
output_20250804_123456/
├── EXAMPLE_1/
│   ├── MODEL_1.md
│   ├── MODEL_1.json
│   └── MODEL_2.md
├── EXAMPLE_2/
│   └── MODEL_1.md
├── summary.json
└── MODELS.json
```

### Sequential Mode

```python
# Command line
model-checker -s --output-mode sequential examples/my_logic.py

# With multiple files
model-checker -s --output-mode sequential --sequential-files multiple examples/my_logic.py
```

Output structure:
```
output_20250804_123456/
├── sequential/
│   ├── EXAMPLE_1.md
│   ├── EXAMPLE_2.md
│   └── EXAMPLE_3.md
└── MODELS.json
```

## File Formats

### Markdown Output (.md)

Human-readable format with converted colors:

```markdown
# EXAMPLE_NAME

Theory: theory_name

## Model Structure

### States
- 🟢 Possible states: s1, s2
- 🔴 Impossible states: s3
- 🔵 World states: s1, s2
- ⭐ Evaluation world: s1

### Relations
- R: {(s1, s2)}

### Propositions
- p: True at s1, False at s2

## Verification
✓ Model found
```

### JSON Output (.json)

Structured data for programmatic access:

```json
{
  "example": "EXAMPLE_NAME",
  "theory": "theory_name",
  "timestamp": "2025-01-15T10:30:45",
  "has_model": true,
  "evaluation_world": "s1",
  "states": {
    "possible": ["s1", "s2"],
    "impossible": ["s3"],
    "worlds": ["s1", "s2"]
  },
  "relations": {
    "R": [["s1", "s2"]]
  },
  "propositions": {
    "p": {
      "s1": true,
      "s2": false
    }
  },
  "verification": {
    "premises_true": true,
    "conclusions_true": true
  }
}
```

### Summary Output (summary.json)

Interactive session metadata:

```json
{
  "metadata": {
    "timestamp": "2025-01-15T10:30:45",
    "mode": "interactive",
    "total_examples": 3,
    "total_models": 5
  },
  "examples": {
    "EXAMPLE_1": {
      "model_count": 2,
      "model_numbers": [1, 2],
      "directory": "EXAMPLE_1"
    },
    "EXAMPLE_2": {
      "model_count": 1,
      "model_numbers": [1],
      "directory": "EXAMPLE_2"
    }
  }
}
```

## Integration

### With BuildModule

The output system integrates seamlessly with BuildModule:

```python
class BuildModule:
    def __init__(self, flags):
        # Create interactive manager if needed
        if flags.save_output:
            from model_checker.output import ConsoleInputProvider
            input_provider = ConsoleInputProvider()
            self.interactive_manager = InteractiveSaveManager(input_provider)
            if flags.interactive:
                self.interactive_manager.set_mode('interactive')
            else:
                self.interactive_manager.prompt_save_mode()
                
        # Initialize output manager
        self.output_manager = OutputManager(
            save_output=flags.save_output,
            interactive_manager=self.interactive_manager
        )
```

### With Model Checking

During model checking, results are captured and saved:

```python
def _capture_and_save_output(self, example, example_name, theory_name):
    # Capture output
    captured_output = capture_print_output(
        lambda: example.print_model(example_name, theory_name)
    )
    
    # Convert ANSI colors
    converter = ANSIToMarkdown()
    converted = converter.convert(captured_output)
    
    # Collect model data
    collector = ModelDataCollector()
    model_data = collector.collect_model_data(...)
    
    # Save based on mode
    if self.interactive_manager.is_interactive():
        if self.interactive_manager.prompt_save_model(example_name):
            self.output_manager.save_model_interactive(...)
    else:
        self.output_manager.save_example(...)
```

## Testing

The module includes comprehensive tests:

```bash
# Run all output tests
python -m pytest src/model_checker/output/tests/ -v

# Specific test categories
python -m pytest src/model_checker/output/tests/test_manager.py -v
python -m pytest src/model_checker/output/tests/test_interactive.py -v
python -m pytest src/model_checker/output/tests/test_formatters.py -v
```

Test coverage includes:
- Output directory creation and structure
- Batch and interactive save modes
- ANSI to Markdown conversion
- Model data collection
- User prompt handling
- Edge cases and error conditions

## Development

### Adding New Output Formats

1. Create formatter in `formatters.py`:
```python
class LaTeXFormatter:
    def format_example(self, model_data, raw_output):
        # Convert to LaTeX format
        return latex_output
```

2. Update OutputManager to use new format:
```python
def save_example_latex(self, example_name, model_data):
    formatter = LaTeXFormatter()
    latex_output = formatter.format_example(model_data, "")
    # Save to file
```

### Extending Interactive Features

1. Add new prompt in `interactive.py`:
```python
def prompt_export_format(self):
    choices = ['Markdown', 'LaTeX', 'HTML']
    return prompt_choice("Select export format:", choices)
```

2. Integrate into workflow:
```python
if self.interactive_manager.is_interactive():
    format_choice = self.interactive_manager.prompt_export_format()
    # Handle format selection
```

## References

### Related Documentation
- [Interactive Save Guide](../../../docs/INTERACTIVE_SAVE.md) - User guide for interactive features
- [CLI Documentation](../README.md#cli-usage) - Command-line interface reference
- [Development Guide](../../../docs/DEVELOPMENT.md) - General development practices

### Design Principles
- **User Control**: Give users fine-grained control over outputs
- **Structure**: Maintain organized, predictable output structure
- **Flexibility**: Support multiple workflows and use cases
- **Clarity**: Provide clear, readable output formats

---

Part of the ModelChecker framework. Licensed under GPL-3.0.