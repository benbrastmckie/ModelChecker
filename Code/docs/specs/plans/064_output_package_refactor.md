# Plan 064: Output Package Refactor Implementation

**Status:** Planning Complete  
**Created:** 2025-01-09  
**Updated:** 2025-01-09 (Enhanced with Jupyter notebook generation)  
**Priority:** MEDIUM  
**Current Compliance:** 72%  
**Target Compliance:** 95%+  
**Estimated Effort:** 24 hours (increased for notebook generation)  

## Executive Summary

The output/ package needs architectural improvements, method extraction, and test modernization. A major enhancement will be adding Jupyter notebook generation as a default output format alongside markdown and JSON. The refactor will implement a strategy pattern for output modes and a configurable format system allowing users to select which output formats to generate via command-line flags.

## Critical Issues

1. **Method Complexity** - Several methods exceed guidelines
2. **Weak Architecture** - No clear pattern for output modes
3. **Test Organization** - Tests need modernization
4. **Mixed Responsibilities** - OutputManager handles too much
5. **Limited Output Formats** - Only markdown and JSON, no notebook support
6. **No Format Configuration** - Cannot selectively enable/disable output formats

## Implementation Plan

### Phase 1: Foundation Cleanup (3 hours)
- Standardize import organization to relative imports
- Extract constants for output configurations
- Create base protocols for strategies and formatters
- Fix documentation gaps and add type hints
- Create error hierarchy (OutputError base class)

### Phase 2: Method Refinement (4 hours)
- Extract `save_model_interactive()` (65 lines) into smaller methods
- Refactor `_create_interactive_summary()` (60 lines)
- Break down `finalize()` method into format-specific handlers
- Extract formatting logic to dedicated helper modules
- Create shared utilities for file I/O operations

### Phase 3: Architectural Improvements (5 hours)
- Implement OutputStrategy protocol for save modes
- Create BatchOutputStrategy, SequentialOutputStrategy, InteractiveOutputStrategy
- Implement OutputFormatter protocol for format handlers
- Add dependency injection for strategies and formatters
- Separate concerns: manager coordinates, strategies decide when, formatters decide how

### Phase 4: Format Configuration System (4 hours)
- Add `--output-formats` CLI argument with default "md,json,ipynb"
- Create FormatRegistry to manage available formatters
- Implement format selection logic in OutputManager
- Add format-specific flags (--no-markdown, --no-json, --no-notebook)
- Update settings module to handle format configuration

### Phase 5: Jupyter Notebook Generation (6 hours)
- Create JupyterNotebookFormatter class
- Implement notebook JSON structure generation
- Add code cell generation with proper imports
- Add markdown cell generation for explanations
- Implement output cell generation for model results
- Create notebook metadata (kernel info, language info)

### Phase 6: Test Enhancement (2 hours)
- Reorganize tests by type (unit/integration/e2e)
- Add notebook generation tests
- Create format configuration tests
- Add cross-format consistency tests
- Validate notebook structure with nbformat library

## Detailed Implementation

### 1. Format Configuration System
```python
# output/config.py
class OutputConfig:
    """Configuration for output formats and modes."""
    
    DEFAULT_FORMATS = ['markdown', 'json', 'notebook']
    
    def __init__(self, formats: Optional[List[str]] = None):
        self.enabled_formats = formats or self.DEFAULT_FORMATS
        self.mode = 'batch'  # batch, sequential, interactive
        self.sequential_files = 'multiple'  # single, multiple
        
    def is_format_enabled(self, format_name: str) -> bool:
        return format_name in self.enabled_formats
        
    @classmethod
    def from_cli_args(cls, args) -> 'OutputConfig':
        """Create config from CLI arguments."""
        formats = []
        if not args.no_markdown:
            formats.append('markdown')
        if not args.no_json:
            formats.append('json')
        if not args.no_notebook:
            formats.append('notebook')
        return cls(formats or cls.DEFAULT_FORMATS)
```

### 2. Strategy Pattern Implementation
```python
# output/strategies/base.py
class IOutputStrategy(Protocol):
    """Protocol for output save strategies."""
    
    def should_save_immediately(self) -> bool: ...
    def prepare_save(self, example_name: str, model_data: Dict) -> SaveContext: ...
    def finalize(self, output_manager: 'OutputManager') -> None: ...

# output/strategies/batch.py
class BatchOutputStrategy:
    """Accumulate outputs and save at end."""
    
    def __init__(self):
        self.accumulated_outputs = []
        
    def should_save_immediately(self) -> bool:
        return False
        
    def accumulate(self, example_name: str, outputs: Dict[str, str]):
        self.accumulated_outputs.append({
            'name': example_name,
            'outputs': outputs
        })
        
    def finalize(self, output_manager):
        # Save all accumulated outputs at once
        for item in self.accumulated_outputs:
            output_manager.save_formats(item['name'], item['outputs'])
```

### 3. Jupyter Notebook Formatter
```python
# output/formatters/notebook.py
class JupyterNotebookFormatter:
    """Generate Jupyter notebooks from model checking results."""
    
    def format_example(self, example_data: Dict, model_output: str) -> str:
        """Convert example to notebook JSON string."""
        cells = []
        
        # Header cell
        cells.append(self._create_markdown_cell(
            f"# {example_data['example']}\n\n"
            f"Model checking result using {example_data['theory']} theory"
        ))
        
        # Setup cell
        cells.append(self._create_code_cell(
            self._generate_setup_code(example_data),
            execution_count=1
        ))
        
        # Input cell
        cells.append(self._create_code_cell(
            self._generate_input_code(example_data),
            execution_count=2
        ))
        
        # Execution cell
        cells.append(self._create_code_cell(
            self._generate_execution_code(example_data),
            execution_count=3,
            outputs=[self._create_output(model_output)]
        ))
        
        # Analysis cell
        if example_data.get('has_model'):
            cells.append(self._create_markdown_cell(
                self._generate_analysis(example_data)
            ))
        
        # Create notebook structure
        notebook = {
            "cells": cells,
            "metadata": self._create_metadata(),
            "nbformat": 4,
            "nbformat_minor": 5
        }
        
        return json.dumps(notebook, indent=2)
    
    def _create_markdown_cell(self, content: str) -> Dict:
        return {
            "cell_type": "markdown",
            "metadata": {},
            "source": content.split('\n')
        }
    
    def _create_code_cell(self, source: str, execution_count: int = None, 
                         outputs: List = None) -> Dict:
        return {
            "cell_type": "code",
            "execution_count": execution_count,
            "metadata": {},
            "outputs": outputs or [],
            "source": source.split('\n')
        }
    
    def _generate_setup_code(self, example_data: Dict) -> str:
        theory = example_data.get('theory', 'logos')
        return f"""# Setup
import sys
from model_checker.jupyter import create_build_example, build_and_check
from model_checker.theory_lib import {theory}

# Configure theory
semantic_theory = {{
    "semantics": {theory}.semantics,
    "proposition": {theory}.proposition,
    "model": {theory}.model,
    "operators": {theory}.operators,
}}"""

    def _generate_input_code(self, example_data: Dict) -> str:
        # Extract premises and conclusions from example_data
        premises = example_data.get('premises', [])
        conclusions = example_data.get('conclusions', [])
        settings = example_data.get('settings', {})
        
        return f"""# Define the example
example = [
    {premises},  # Premises
    {conclusions},  # Conclusions
    {settings}  # Settings
]"""

    def _generate_execution_code(self, example_data: Dict) -> str:
        return f"""# Check for countermodel
model = create_build_example(
    '{example_data['example']}',
    semantic_theory,
    example
)

# Display result
if model.model_structure.z3_model:
    model.model_structure.print_to(
        model.settings,
        '{example_data['example']}',
        'Model Checking Result',
        output=sys.stdout
    )
else:
    print("No countermodel found - the inference is VALID")"""
```

### 4. Enhanced OutputManager
```python
# output/manager.py
class OutputManager:
    """Manages output with configurable formats and strategies."""
    
    def __init__(self, config: OutputConfig, strategy: IOutputStrategy):
        self.config = config
        self.strategy = strategy
        self.formatters = self._initialize_formatters()
        
    def _initialize_formatters(self) -> Dict[str, IOutputFormatter]:
        """Initialize enabled formatters."""
        formatters = {}
        if self.config.is_format_enabled('markdown'):
            formatters['markdown'] = MarkdownFormatter()
        if self.config.is_format_enabled('json'):
            formatters['json'] = JSONFormatter()
        if self.config.is_format_enabled('notebook'):
            formatters['notebook'] = JupyterNotebookFormatter()
        return formatters
    
    def save_example(self, example_name: str, example_data: Dict, 
                     model_output: str):
        """Save example in all enabled formats."""
        formatted_outputs = {}
        
        # Generate outputs for each enabled format
        for format_name, formatter in self.formatters.items():
            formatted_outputs[format_name] = formatter.format_example(
                example_data, model_output
            )
        
        # Save based on strategy
        if self.strategy.should_save_immediately():
            self._save_all_formats(example_name, formatted_outputs)
        else:
            self.strategy.accumulate(example_name, formatted_outputs)
    
    def _save_all_formats(self, example_name: str, outputs: Dict[str, str]):
        """Save outputs in all formats."""
        for format_name, content in outputs.items():
            extension = self._get_extension(format_name)
            filename = f"{example_name}.{extension}"
            filepath = os.path.join(self.output_dir, filename)
            
            with open(filepath, 'w', encoding='utf-8') as f:
                f.write(content)
```

### 5. CLI Integration
```python
# Updates to __main__.py ParseFileFlags
parser.add_argument(
    '--output-formats',
    type=str,
    default='md,json,ipynb',
    help='Comma-separated list of output formats (md,json,ipynb)'
)
parser.add_argument(
    '--no-markdown',
    action='store_true',
    help='Disable markdown output generation'
)
parser.add_argument(
    '--no-json',
    action='store_true',
    help='Disable JSON output generation'
)
parser.add_argument(
    '--no-notebook',
    action='store_true',
    help='Disable Jupyter notebook output generation'
)
```

## File Structure After Refactor

```
output/
├── __init__.py                # Updated exports
├── manager.py                 # Simplified with strategies and formatters
├── config.py                  # New - output configuration
├── constants.py               # New - extracted constants
├── errors.py                  # New - error hierarchy
├── strategies/                # New directory for save strategies
│   ├── __init__.py
│   ├── base.py               # IOutputStrategy protocol
│   ├── batch.py              # Batch mode strategy
│   ├── sequential.py         # Sequential mode strategy
│   └── interactive.py        # Interactive mode strategy
├── formatters/                # Reorganized formatters
│   ├── __init__.py
│   ├── base.py               # IOutputFormatter protocol
│   ├── markdown.py           # Existing, refactored
│   ├── json.py               # New - extracted from manager
│   └── notebook.py           # New - Jupyter notebook generation
├── collectors.py              # Existing, enhanced for notebooks
├── helpers.py                 # New - shared formatting utilities
├── interactive.py             # Existing, refactored
├── prompts.py                # Existing
├── input_provider.py         # Existing
├── progress/                  # Existing subdirectory
└── tests/
    ├── unit/
    │   ├── test_config.py
    │   ├── test_strategies.py
    │   ├── test_formatters.py
    │   └── test_notebook.py
    ├── integration/
    │   ├── test_format_selection.py
    │   ├── test_notebook_generation.py
    │   └── test_cross_format.py
    └── fixtures/
        ├── sample_models.py
        └── notebook_validator.py
```

## Example Usage

### Default Behavior (All Formats)
```bash
# Generates .md, .json, and .ipynb files
python -m model_checker example.py -s
```

### Selective Format Generation
```bash
# Only markdown and JSON (no notebooks)
python -m model_checker example.py -s --no-notebook

# Only notebooks
python -m model_checker example.py -s --no-markdown --no-json

# Custom format list
python -m model_checker example.py -s --output-formats "md,ipynb"
```

### Generated Files Example
```
output_20250109_143022/
├── EXAMPLES.md              # Markdown documentation
├── MODELS.json              # Structured model data
├── EXAMPLES.ipynb           # Executable Jupyter notebook
└── summary.json             # Output summary metadata
```

## Notebook Features

### Generated Notebook Structure
1. **Header Cell** - Example name and description
2. **Import Cell** - Required imports and theory setup
3. **Configuration Cell** - Settings and parameters
4. **Input Cell** - Premises and conclusions definition
5. **Execution Cell** - Model checking code with captured output
6. **Result Cell** - Countermodel display or validation message
7. **Analysis Cell** - Interpretation and insights

### Notebook Metadata
- Kernel: Python 3
- Language: Python
- Created by: ModelChecker Output Manager
- Timestamp: Generation time
- Theory: Semantic theory used

## Testing Strategy

### Unit Tests
- Test each formatter independently
- Test strategy behavior isolation
- Test configuration parsing
- Validate notebook JSON structure

### Integration Tests
- Test format selection logic
- Test file generation for each format
- Test combined format output
- Validate cross-format consistency

### End-to-End Tests
- Test full pipeline from model checking to output
- Verify notebook executability
- Test CLI flag combinations
- Validate output directory structure

## Success Metrics
- ✅ All methods under 40 lines
- ✅ Clear strategy pattern implementation
- ✅ Test coverage above 85%
- ✅ Clean separation of concerns
- ✅ All output formats generated correctly
- ✅ Notebooks executable in Jupyter
- ✅ Configurable format selection working
- ✅ 95%+ maintenance standards compliance

## Migration Notes

### Breaking Changes
- OutputManager constructor signature changed (now requires config)
- New CLI arguments added (backward compatible with defaults)
- File structure reorganized (imports need updating)

### Compatibility
- Default behavior unchanged (all formats generated)
- Existing code works with default configuration
- New features opt-in via CLI flags

---

**Status**: Ready for implementation
**Next Action**: Begin with Phase 1 (Foundation Cleanup)