# Notebook Generation Package

[← Back to ModelChecker](../../README.md) | [API Documentation →](../README.md)

## Overview

The **Notebook Generation Package** provides streaming, memory-efficient generation of Jupyter notebooks from model checking results. It uses a template-based approach with theory-specific customization to create interactive, runnable notebooks that demonstrate countermodels and theorem validations.

As of the unified architecture implementation, this package is integrated into the output management pipeline through the NotebookFormatter adapter, ensuring all output formats are generated consistently through the same system.

## Directory Structure

```
notebook/
├── README.md                    # This file - package documentation
├── __init__.py                 # Package exports
├── streaming_generator.py      # Main streaming notebook generator
├── notebook_writer.py          # Low-level JSON streaming writer
├── template_loader.py          # Template discovery and loading
├── generator.py                # Legacy generator (deprecated)
├── templates/                  # Theory-specific template implementations
│   ├── __init__.py
│   ├── base.py                # Base template class
│   ├── logos.py               # Logos theory template
│   ├── exclusion.py           # Exclusion theory template
│   └── imposition.py          # Imposition theory template
└── tests/                     # Test suite
    ├── unit/                  # Unit tests for components
    └── integration/           # Integration tests
```

## Architecture

### Core Components

#### StreamingNotebookGenerator
The main entry point for notebook generation. Coordinates template loading, example processing, and streaming output.

```python
from model_checker.notebook import StreamingNotebookGenerator

generator = StreamingNotebookGenerator()
generator.generate_notebook_stream(module_vars, source_path, output_path)
```

#### NotebookWriter
Low-level streaming JSON writer that creates valid Jupyter notebook format without holding the entire structure in memory.

```python
with NotebookWriter(output_path) as writer:
    writer.write_cell({
        'cell_type': 'markdown',
        'source': ['# Example Notebook']
    })
```

#### TemplateLoader
Discovers and loads the appropriate template based on the semantic theory class.

```python
loader = TemplateLoader()
template = loader.get_template_for_class(semantics_class)
```

### Template System

Each theory provides a template that defines:
1. **Setup cells** - Theory imports and configuration
2. **Example processing** - How to format examples as notebook cells
3. **Result formatting** - How to display countermodels and validations

Templates are discovered in two ways:
- **Class-based templates** in `templates/` directory
- **JSON templates** in theory `notebooks/` directories

## Usage

### Basic Usage

The notebook generator is now invoked through the unified output pipeline via NotebookFormatter:

```python
from model_checker.output.formatters.notebook import NotebookFormatter

# NotebookFormatter acts as adapter
formatter = NotebookFormatter()

# Set module context
formatter.set_context(module_vars, source_path)

# Generate through unified pipeline
formatter.format_for_streaming('output/NOTEBOOK.ipynb')
```

### Direct Usage (Advanced)

For direct usage outside the unified pipeline:

```python
from model_checker.output.notebook.streaming_generator import StreamingNotebookGenerator

# Module variables from theory execution
module_vars = {
    'semantic_theories': {...},
    'examples': [...],
    # ... other execution context
}

# Generate notebook directly
generator = StreamingNotebookGenerator()
generator.generate_notebook_stream(
    module_vars,
    'path/to/examples.py',
    'output/NOTEBOOK.ipynb'
)
```

### Creating Theory Templates

#### JSON Template Format

Create a `template.json` in your theory's `notebooks/` directory:

```json
{
  "setup_cells": [
    {
      "cell_type": "markdown",
      "metadata": {},
      "source": [
        "# {{THEORY_NAME}} Examples\n",
        "Generated: {{DATE}}"
      ]
    },
    {
      "cell_type": "code",
      "metadata": {},
      "source": [
        "from model_checker.jupyter import create_build_example\n",
        "from my_theory import MySemantics\n",
        "# Theory setup code..."
      ]
    }
  ],
  "example_cell_template": {
    "cell_type": "code",
    "metadata": {},
    "source": []
  }
}
```

#### Class-Based Template

Create a subclass of `BaseNotebookTemplate`:

```python
from model_checker.notebook.templates.base import BaseNotebookTemplate

class MyTheoryTemplate(BaseNotebookTemplate):
    def get_setup_cells(self):
        """Return list of setup cells for the notebook."""
        return [
            self._create_markdown_cell("# My Theory Examples"),
            self._create_code_cell([
                "from model_checker.jupyter import create_build_example",
                "# Setup code..."
            ])
        ]
    
    def create_example_cells(self, name, definition):
        """Create cells for a single example."""
        # Custom example formatting
        return [...]
```

## Template Placeholders

Templates support the following placeholders:
- `{{THEORY_NAME}}` - Name of the theory
- `{{DATE}}` - Current date/time
- `{{SOURCE_PATH}}` - Path to examples file
- `{{EXAMPLE_NAME}}` - Name of current example

## Memory Efficiency

The streaming architecture ensures constant memory usage regardless of the number of examples:

1. **Streaming JSON output** - Cells are written directly to disk
2. **No full notebook in memory** - Only current cell is held
3. **Lazy template loading** - Templates loaded only when needed
4. **Incremental processing** - Examples processed one at a time

## Testing

### Running Tests

```bash
# Run all notebook tests
python -m pytest src/model_checker/notebook/tests/

# Run unit tests only
python -m pytest src/model_checker/notebook/tests/unit/

# Run with coverage
python -m pytest src/model_checker/notebook/tests/ --cov=model_checker.notebook
```

### Test Structure

- **Unit tests** - Test individual components in isolation
  - `test_notebook_writer.py` - NotebookWriter functionality
  - `test_template_loader.py` - Template discovery and loading
  
- **Integration tests** - Test complete workflows
  - `test_notebook_generation.py` - End-to-end generation

## Migration Note

This package is planned to be moved to `output/notebook/` as part of the output subsystem consolidation. The current location is temporary and will be updated in a future refactor.

## Error Handling

The package provides clear error messages for common issues:

- **Missing template** - FileNotFoundError with expected path
- **No examples** - ValueError indicating no examples found
- **Invalid JSON** - JSONDecodeError with template location
- **Missing theory** - ValueError for no semantic theories

## Performance Considerations

- **Streaming output** - Constant memory usage
- **Template caching** - Templates loaded once per generation
- **Lazy evaluation** - Examples processed on-demand
- **File I/O optimization** - Buffered writes for efficiency

## Future Enhancements

1. **Template validation** - Schema-based validation
2. **Custom cell types** - Support for widgets and interactive elements
3. **Parallel generation** - Multi-notebook generation
4. **Template inheritance** - Base templates for theory families

## API Reference

### StreamingNotebookGenerator

```python
class StreamingNotebookGenerator:
    def generate_notebook_stream(
        self,
        module_vars: Dict,
        source_path: str, 
        output_path: str
    ) -> None:
        """Generate a notebook from module execution context."""
```

### NotebookWriter

```python
class NotebookWriter:
    def __init__(self, output_path: str):
        """Initialize writer for output path."""
    
    def write_cell(self, cell: Dict[str, Any]):
        """Write a single cell to the notebook."""
```

### TemplateLoader

```python
class TemplateLoader:
    def get_template_for_class(self, semantics_class: Any):
        """Get template instance for semantic class."""
```

## License

Part of the ModelChecker framework, licensed under GPL-3.0.

---

[← Back to ModelChecker](../../README.md) | [Output Package →](../output/README.md)