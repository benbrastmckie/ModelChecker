# Output Formatters: Multi-Format Result Generation

[← Back to Output](../README.md) | [Strategies →](../strategies/README.md) | [Tests →](../tests/README.md)

## Directory Structure

```
formatters/
├── README.md          # This file - formatter subsystem documentation
├── __init__.py        # Package initialization and exports
├── base.py            # Abstract base formatter class
├── markdown.py        # Markdown (.md) output generation
├── json.py            # JSON (.json) data serialization
└── notebook.py        # Jupyter notebook (.ipynb) integration adapter
```

## Overview

The **formatters subsystem** implements the strategy pattern for generating model checking results in multiple output formats. Each formatter transforms the unified internal representation of model checking results into a specific file format, ensuring consistent information presentation across different media while leveraging format-specific capabilities.

This modular design allows the framework to support diverse use cases - from human-readable documentation (Markdown) to data analysis (JSON) to interactive exploration (Jupyter notebooks) - without coupling the core model checking logic to output concerns.

## Architecture

### Design Pattern

The formatters implement a **protocol-based strategy pattern** where:
- `IOutputFormatter` protocol defines the interface all formatters must implement
- Each concrete formatter (Markdown, JSON, Notebook) provides format-specific implementation
- The `OutputManager` delegates to formatters based on configuration through unified pipeline
- Formatters are stateless and reusable across multiple examples
- NotebookFormatter acts as adapter to integrate streaming generation

### Class Hierarchy

```
IOutputFormatter (Protocol)
├── MarkdownFormatter    # Human-readable documentation
├── JSONFormatter        # Machine-readable data
└── NotebookFormatter    # Jupyter notebook adapter
```

## Formatters

### IOutputFormatter Protocol

Protocol defining the formatter interface:

```python
from model_checker.output.formatters.base import IOutputFormatter

class CustomFormatter:
    def format_example(self, example_data: Dict[str, Any], 
                      model_output: str) -> str:
        """Format a single example."""
        # Implementation required
        pass
    
    def format_batch(self, examples: list) -> str:
        """Format multiple examples for batch output."""
        # Implementation required
        pass
    
    def get_file_extension(self) -> str:
        """Return file extension for this format."""
        return "custom"
```

### MarkdownFormatter

Generates human-readable Markdown documentation:

```python
from model_checker.output.formatters import MarkdownFormatter

formatter = MarkdownFormatter()
markdown_output = formatter.format({
    'example_name': 'TEST_1',
    'theory_name': 'Logos',
    'premises': ['p ∧ q'],
    'conclusions': ['p'],
    'model': {...},
    'verification': 'Countermodel found'
})
```

**Features**:
- Clean, readable formatting with headers and sections
- Mathematical notation support (Unicode and LaTeX)
- Structured presentation of states and relations
- GitHub-flavored Markdown compatibility

### JSONFormatter

Produces machine-readable JSON for data analysis:

```python
from model_checker.output.formatters import JSONFormatter

formatter = JSONFormatter()
json_output = formatter.format({
    'example_name': 'TEST_1',
    'theory_name': 'Logos',
    'model': {...},
    'settings': {'N': 5}
})
```

**Features**:
- Complete data serialization
- Preserves all model structure
- Suitable for programmatic analysis
- Compact representation option

### NotebookFormatter

Adapter that integrates notebook generation with the unified pipeline:

```python
from model_checker.output.formatters import NotebookFormatter

formatter = NotebookFormatter()

# Set module context (required for notebook generation)
formatter.set_context(module_vars, source_path)

# Generate notebook using streaming approach
formatter.format_for_streaming(output_path)
```

**Features**:
- Integrates StreamingNotebookGenerator with formatter interface
- Efficient streaming generation without memory overhead
- Produces complete .ipynb JSON structure
- Includes theory-specific templates and examples
- Compatible with Jupyter Lab/Notebook

**Architecture**:
- Acts as adapter between IOutputFormatter protocol and streaming generator
- Requires module context for semantic theories and settings
- Supports both batch and streaming generation modes

## Usage Patterns

### Basic Formatting

```python
from model_checker.output.formatters import MarkdownFormatter, JSONFormatter

# Format the same data in multiple formats
data = {
    'example_name': 'EXAMPLE_1',
    'theory_name': 'Modal',
    'premises': ['□p → p'],
    'conclusions': ['◇p'],
    'model': model_result,
    'verification': 'Valid'
}

markdown = MarkdownFormatter().format(data)
json_str = JSONFormatter().format(data)
```

### Integration with OutputManager

```python
from model_checker.output import OutputManager

# OutputManager automatically uses configured formatters
manager = OutputManager(build_module)
manager.save_example('TEST_1', example_data, formatted_output)
# Generates .md, .json, and .ipynb based on configuration
```

### Custom Formatter Implementation

```python
from model_checker.output.formatters.base import BaseFormatter

class LaTeXFormatter(BaseFormatter):
    """Generate LaTeX documents from model checking results."""
    
    def format(self, example_data: Dict[str, Any]) -> str:
        """Convert to LaTeX format."""
        return f"""\\documentclass{{article}}
\\begin{{document}}
\\section{{{example_data['example_name']}}}
Premises: {', '.join(example_data['premises'])}
\\end{{document}}"""
    
    def get_extension(self) -> str:
        return ".tex"
```

## Configuration

Formatters are configured via the `OutputConfig`:

```python
from model_checker.output.config import OutputConfig

# Enable specific formatters
config = OutputConfig(
    formats=['markdown', 'json', 'notebook'],
    mode='batch'
)

# Check if formatter is enabled
if config.is_format_enabled('markdown'):
    formatter = MarkdownFormatter()
```

## Extension Points

### Adding New Formatters

1. Create a new formatter class extending `BaseFormatter`
2. Implement the `format()` and `get_extension()` methods
3. Register in `__init__.py` for auto-discovery
4. Update `OutputConfig` to recognize the new format

### Customizing Existing Formatters

Formatters can be extended through subclassing:

```python
class VerboseMarkdownFormatter(MarkdownFormatter):
    """Markdown with additional debugging information."""
    
    def format(self, example_data: Dict[str, Any]) -> str:
        base_output = super().format(example_data)
        debug_info = self._generate_debug_section(example_data)
        return f"{base_output}\n\n## Debug Information\n{debug_info}"
```

## Testing

The formatters have comprehensive test coverage:

```bash
# Run formatter-specific tests
pytest src/model_checker/output/tests/unit/test_markdown_formatter.py
pytest src/model_checker/output/tests/unit/test_json_serialization.py

# Integration tests
pytest src/model_checker/output/tests/integration/test_output_integration.py
```

## Performance Considerations

- **Stateless Design**: Formatters maintain no state between calls
- **Lazy Evaluation**: Format only when needed
- **Memory Efficiency**: Stream large outputs when possible
- **Format-Specific Optimization**: Each formatter optimizes for its use case

## Related Components

- **[Output Manager](../manager.py)** - Coordinates formatter usage
- **[Output Strategies](../strategies/README.md)** - Controls when formatting occurs
- **[Output Configuration](../config.py)** - Manages formatter selection
- **[Output Tests](../tests/README.md)** - Comprehensive test suite

---

[← Back to Output](../README.md) | [Strategies →](../strategies/README.md) | [Tests →](../tests/README.md)