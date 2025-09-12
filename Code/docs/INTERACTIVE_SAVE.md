# Interactive Save Mode Documentation

[← Back to Development](README.md) | [Implementation Guide →](IMPLEMENTATION.md) | [CLI Reference →](../src/model_checker/README.md#cli-usage)

## Overview

The **Interactive Save Mode** provides fine-grained control over which model checking results are saved, allowing users to selectively save models and iterate through additional solutions interactively. This feature enhances the ModelChecker's output capabilities by offering a conversational workflow for managing results.

### Key Features

- **Selective Model Saving**: Choose which models to save after viewing results
- **Interactive Iteration**: Decide whether to find additional models on-the-fly
- **Directory Navigation**: Easy navigation to saved output with path display
- **Batch Mode Compatibility**: Seamlessly switches between batch and interactive modes

## Usage

### Command Line Interface

Enable interactive save mode using the `-I` or `--interactive` flag along with the new consolidated `--save` flag:

```bash
# Interactive mode with save output (new --save flag)
model-checker --save --interactive examples/my_logic.py

# Save specific formats interactively
model-checker --save markdown json --interactive examples/my_logic.py

# Legacy format (still supported)
model-checker -s -I examples/my_logic.py
```

### Interactive Workflow

1. **Mode Selection** (if `-I` not specified):
   ```
   Select save mode:
   1) batch - Save all at end
   2) interactive - Prompt after each model
   ```

2. **Model Save Prompt** (after each model):
   ```
   Save model for EXAMPLE_NAME? (Y/n):
   ```

3. **Iteration Prompt** (after saving decision):
   ```
   Find additional models? (y/N):
   ```

4. **Directory Navigation** (at completion):
   ```
   All models saved to: /path/to/output_20250804_123456
   Change to output directory? (y/N):
   ```

### Output Structure

In interactive mode, outputs are organized by example:

```
output_YYYYMMDD_HHMMSS/
├── EXAMPLE_1/
│   ├── MODEL_1.md      # Formatted model with colors
│   ├── MODEL_1.json    # Structured data
│   ├── MODEL_2.md      # Second model (if saved)
│   └── MODEL_2.json
├── EXAMPLE_2/
│   ├── MODEL_1.md
│   └── MODEL_1.json
├── summary.json        # Interactive session summary
└── MODELS.json         # All models in single file
```

## Implementation Details

### Architecture Components

1. **InteractiveSaveManager** (`src/model_checker/output/interactive.py`):
   - Manages user prompts and workflow state
   - Tracks model counts per example
   - Handles mode selection and navigation

2. **OutputManager Extensions** (`src/model_checker/output/manager.py`):
   - `save_model_interactive()`: Saves individual models
   - `create_example_directory()`: Creates per-example directories
   - `_create_interactive_summary()`: Generates session summary

3. **BuildModule Integration** (`src/model_checker/builder/module.py`):
   - Checks for interactive flag
   - Prompts for iteration in interactive mode
   - Displays final output path

### Prompt Utilities

The system uses consistent prompt utilities (`src/model_checker/output/prompts.py`):

- `prompt_yes_no()`: Binary decisions with defaults
- `prompt_choice()`: Multiple choice selections
- Keyboard interrupt handling (Ctrl+C)
- Input validation and error recovery

## Examples

### Basic Interactive Session

```python
# examples/modal_logic.py
from model_checker.theory_lib.bimodal import *

semantic_theories = {
    "modal": {
        "semantics": ModalSemantics,
        "proposition": ModalProposition,
        "model": ModalModel,
        "operators": {"not": Negation, "box": Box},
        "dictionary": {"~": "not", "[]": "box"}
    }
}

example_range = {
    "POSSIBILITY": [['[]p'], ['p'], {'N': 3}],
    "NECESSITY": [['p'], ['[]p'], {'N': 3}]
}

general_settings = {"save_output": True}
```

Run with interactive mode:
```bash
# Using new --save flag
model-checker --save --interactive examples/modal_logic.py

# Or save specific formats
model-checker --save markdown --interactive examples/modal_logic.py
```

### Batch Mode Comparison

```bash
# Batch mode - saves all results (new --save flag)
model-checker --save examples/modal_logic.py

# Interactive mode - selective saving
model-checker --save --interactive examples/modal_logic.py

# Legacy format (still supported)
model-checker -s -I examples/modal_logic.py
```

## Best Practices

### When to Use Interactive Mode

- **Exploratory Analysis**: When investigating different models
- **Large Example Sets**: To avoid saving unnecessary results
- **Iterative Development**: When refining logical theories
- **Resource Management**: To control output storage

### When to Use Batch Mode

- **Automated Testing**: CI/CD pipelines
- **Complete Documentation**: Saving all results
- **Reproducible Research**: Consistent output sets
- **Performance Testing**: Minimal user interaction

## Technical Reference

### Configuration

Interactive mode respects general settings:

```python
general_settings = {
    "save_output": True,      # Required for any saving
    "print_impossible": True,  # Still shows impossible states
    "print_constraints": True  # Shows constraints when requested
}
```

### File Formats

**MODEL_N.md** (Markdown with ANSI colors converted):
```markdown
# EXAMPLE_NAME

Theory: modal

## Model Structure

### States
- 🟢 Possible: s1, s2
- 🔴 Impossible: s3
- 🔵 Worlds: s1, s2
- ⭐ Evaluation: s1

### Propositions
- p: True at s1
```

**MODEL_N.json** (Structured data):
```json
{
  "example": "POSSIBILITY",
  "theory": "modal",
  "has_model": true,
  "states": {
    "possible": ["s1", "s2"],
    "impossible": ["s3"],
    "worlds": ["s1", "s2"]
  },
  "propositions": {
    "p": {"s1": true, "s2": false}
  }
}
```

**summary.json** (Session metadata):
```json
{
  "metadata": {
    "timestamp": "2025-01-15T10:30:45",
    "mode": "interactive",
    "total_examples": 2,
    "total_models": 3
  },
  "examples": {
    "POSSIBILITY": {
      "model_count": 2,
      "model_numbers": [1, 2],
      "directory": "POSSIBILITY"
    }
  }
}
```

## Troubleshooting

### Common Issues

1. **No Prompts Appearing**:
   - Ensure both `--save` and `--interactive` flags are used (or `-s -I` legacy)
   - Check that `save_output` is True in general_settings (for legacy compatibility)

2. **Models Not Saved**:
   - Verify model has valid status (not UNSAT)
   - Check file permissions in output directory

3. **Iteration Not Working**:
   - Ensure theory supports iteration
   - Check `iterate` setting in example configuration

### Debug Mode

Enable debug output for troubleshooting:

```bash
# With print constraints
model-checker -s -I -p examples/test.py

# With Z3 output
model-checker -s -I -z examples/test.py
```

## Integration

### With Other Tools

Interactive mode works with all ModelChecker features:

- **Theory Comparison** (`-m`): Compare theories interactively
- **Constraint Printing** (`-p`): View constraints before saving
- **Impossible States** (`-i`): Include impossible states in output

### Programmatic Usage

```python
from model_checker.builder import BuildModule
from model_checker.output import InteractiveSaveManager

# Create flags with interactive mode
flags = type('Flags', (), {
    'file_path': 'examples/test.py',
    'save_output': True,
    'interactive': True,
    'output_mode': 'batch',
    'print_constraints': False
})()

# Run with interactive saving
module = BuildModule(flags)
module.run_examples()
```

## Future Enhancements

Planned improvements for interactive save mode:

1. **Filter Options**: Save models matching specific criteria
2. **Bulk Operations**: Select multiple models at once
3. **Preview Mode**: View output before saving
4. **Export Formats**: Additional output formats (LaTeX, HTML)
5. **Session Resume**: Continue interrupted sessions

---

For implementation details, see [Implementation Guide](IMPLEMENTATION.md). For complete API reference, consult [API Documentation](../src/model_checker/output/README.md).