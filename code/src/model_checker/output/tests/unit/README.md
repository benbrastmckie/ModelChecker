# Output Unit Tests

## Overview

This directory contains unit tests for the output package, covering all output formatting, display, and serialization functionality. These tests ensure that the unified output architecture correctly handles various output formats, progress displays, and user interactions.

## Modules

### test_color_formatting.py
**Purpose**: Tests terminal color formatting and ANSI escape sequences
**Key Classes**: 
- `TestColorFormatter` - Tests for applying color codes to text
- `TestANSIEscapes` - Tests for ANSI escape sequence generation
**Key Functions**: Tests color application, style combinations, color stripping
**Dependencies**: `pytest`, `output.color_formatting`
**Used By**: Terminal output validation

### test_config.py
**Purpose**: Tests output configuration management and settings
**Key Classes**: 
- `TestOutputConfig` - Tests for output configuration handling
- `TestConfigValidation` - Tests for configuration validation
**Key Functions**: Tests config loading, validation, defaults, merging
**Dependencies**: `pytest`, `output.config`
**Used By**: Configuration system validation

### test_errors.py
**Purpose**: Tests error handling and error message formatting
**Key Classes**: 
- `TestOutputErrors` - Tests for custom error classes
- `TestErrorFormatting` - Tests for error message formatting
**Key Functions**: Tests error creation, formatting, context preservation
**Dependencies**: `pytest`, `output.errors`
**Used By**: Error handling validation

### test_helpers.py
**Purpose**: Tests utility helper functions for output processing
**Key Classes**: 
- `TestOutputHelpers` - Tests for output utility functions
**Key Functions**: Tests string manipulation, format detection, path utilities
**Dependencies**: `pytest`, `output.helpers`
**Used By**: Utility function validation

### test_input_provider.py
**Purpose**: Tests user input handling and prompt systems
**Key Classes**: 
- `TestInputProvider` - Tests for capturing user input
- `TestPromptHandling` - Tests for interactive prompts
**Key Functions**: Tests input validation, prompt formatting, default handling
**Dependencies**: `pytest`, `output.input_provider`
**Used By**: Interactive feature validation

### test_json_serialization.py
**Purpose**: Tests JSON serialization of build results and models
**Key Classes**: 
- `TestJSONSerializer` - Tests for JSON output generation
- `TestJSONDeserialization` - Tests for parsing JSON inputs
**Key Functions**: Tests serialization formats, custom encoders, pretty printing
**Dependencies**: `pytest`, `output.json_serialization`, `json`
**Used By**: JSON output validation

### test_markdown_formatter.py
**Purpose**: Tests Markdown formatting for documentation output
**Key Classes**: 
- `TestMarkdownFormatter` - Tests for Markdown generation
- `TestMarkdownTables` - Tests for table formatting
**Key Functions**: Tests heading generation, list formatting, code blocks
**Dependencies**: `pytest`, `output.markdown_formatter`
**Used By**: Documentation output validation

### test_notebook_formatter.py
**Purpose**: Tests Jupyter notebook generation and formatting
**Key Classes**: 
- `TestNotebookFormatter` - Tests for notebook cell generation
- `TestNotebookStructure` - Tests for notebook document structure
**Key Functions**: Tests cell creation, metadata handling, output formatting
**Dependencies**: `pytest`, `output.notebook_formatter`, `nbformat`
**Used By**: Notebook generation validation

### test_progress_animated.py
**Purpose**: Tests animated progress indicators for long-running operations
**Key Classes**: 
- `TestAnimatedProgress` - Tests for progress animations
- `TestSpinnerAnimation` - Tests for spinner implementations
**Key Functions**: Tests animation frames, timing, terminal compatibility
**Dependencies**: `pytest`, `output.progress.animated`
**Used By**: Progress display validation

### test_progress_core.py
**Purpose**: Tests core progress tracking functionality
**Key Classes**: 
- `TestProgressTracker` - Tests for progress state management
- `TestProgressCalculation` - Tests for progress percentage calculations
**Key Functions**: Tests progress updates, completion detection, state management
**Dependencies**: `pytest`, `output.progress.core`
**Used By**: Progress system validation

### test_progress_display.py
**Purpose**: Tests progress display rendering and formatting
**Key Classes**: 
- `TestProgressDisplay` - Tests for progress bar rendering
- `TestProgressFormatting` - Tests for progress text formatting
**Key Functions**: Tests bar generation, percentage display, ETA calculation
**Dependencies**: `pytest`, `output.progress.display`
**Used By**: Progress UI validation

### test_progress_spinner.py
**Purpose**: Tests spinner implementations for indeterminate progress
**Key Classes**: 
- `TestSpinner` - Tests for spinner behavior
- `TestSpinnerStyles` - Tests for different spinner styles
**Key Functions**: Tests spinner rotation, style selection, terminal handling
**Dependencies**: `pytest`, `output.progress.spinner`
**Used By**: Spinner display validation

### test_prompts.py
**Purpose**: Tests interactive prompt generation and handling
**Key Classes**: 
- `TestPrompts` - Tests for user prompt generation
- `TestPromptValidation` - Tests for input validation
**Key Functions**: Tests yes/no prompts, choice selection, input validation
**Dependencies**: `pytest`, `output.prompts`
**Used By**: Interactive UI validation

## Usage

### Running All Unit Tests
```bash
# From project root
./run_tests.py --unit output

# Or directly with pytest
pytest src/model_checker/output/tests/unit/ -v
```

### Running Specific Test Module
```python
# Run a specific test file
pytest src/model_checker/output/tests/unit/test_notebook_formatter.py -v

# Run a specific test class
pytest src/model_checker/output/tests/unit/test_config.py::TestOutputConfig -v

# Run with coverage
pytest src/model_checker/output/tests/unit/ --cov=model_checker.output
```

## Test Fixtures

Common fixtures are defined in `../conftest.py` and include:
- Mock terminal environments
- Sample build results for formatting
- Temporary file systems for output testing
- Mock user input streams

## Coverage

These unit tests provide comprehensive coverage of:
- All output format generators (JSON, Markdown, Notebook)
- Progress tracking and display systems
- User interaction and prompt handling
- Configuration management
- Error formatting and handling

## Contributing

When adding new unit tests:
1. Test each output format independently
2. Mock terminal capabilities for consistent testing
3. Test both successful and error cases
4. Verify formatted output matches expected structure
5. Ensure tests work in non-interactive environments

## See Also

- [Output Package Documentation](../../README.md)
- [Integration Tests](../integration/README.md)
- [Formatters Documentation](../../formatters/README.md)
- [Progress System Documentation](../../progress/README.md)