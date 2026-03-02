# Jupyter Unit Tests

## Overview

This directory contains unit tests for the jupyter package, which provides Jupyter notebook integration, interactive displays, and debugging tools for the ModelChecker framework. These tests validate notebook helpers, UI builders, and adapter functionality.

## Modules

### test_adapters.py
**Purpose**: Tests adapter classes for integrating with Jupyter environments
**Key Classes**: 
- `TestJupyterAdapter` - Tests for Jupyter environment adaptation
- `TestDisplayAdapter` - Tests for display output adaptation
**Key Functions**: Tests environment detection, output routing, display formatting
**Dependencies**: `pytest`, `jupyter.adapters`
**Used By**: Jupyter integration validation

### test_exceptions.py
**Purpose**: Tests custom exceptions and error handling for Jupyter integration
**Key Classes**: 
- `TestJupyterExceptions` - Tests for custom exception classes
- `TestExceptionFormatting` - Tests for exception display in notebooks
**Key Functions**: Tests exception creation, traceback formatting, cell error display
**Dependencies**: `pytest`, `jupyter.exceptions`
**Used By**: Error handling validation

### test_notebook_helpers.py
**Purpose**: Tests helper functions for notebook operations
**Key Classes**: 
- `TestNotebookHelpers` - Tests for notebook utility functions
- `TestCellHelpers` - Tests for cell manipulation utilities
**Key Functions**: Tests cell creation, metadata handling, output management
**Dependencies**: `pytest`, `jupyter.notebook_helpers`
**Used By**: Notebook utility validation

### test_ui_builders.py
**Purpose**: Tests UI component builders for interactive notebooks
**Key Classes**: 
- `TestUIBuilders` - Tests for UI component generation
- `TestWidgetBuilders` - Tests for widget creation
**Key Functions**: Tests button creation, form building, interactive displays
**Dependencies**: `pytest`, `jupyter.ui_builders`
**Used By**: UI component validation

### test_unicode.py
**Purpose**: Tests Unicode handling and mathematical symbol display
**Key Classes**: 
- `TestUnicodeHandling` - Tests for Unicode symbol processing
- `TestMathSymbols` - Tests for mathematical notation display
**Key Functions**: Tests symbol conversion, LaTeX rendering, Unicode normalization
**Dependencies**: `pytest`, `jupyter.unicode`
**Used By**: Symbol display validation

### __init__.py
**Purpose**: Test package initialization
**Key Classes**: None
**Key Functions**: Package setup for test discovery
**Dependencies**: None
**Used By**: Test framework

## Usage

### Running All Unit Tests
```bash
# From project root
./run_tests.py --unit jupyter

# Or directly with pytest
pytest src/model_checker/jupyter/tests/unit/ -v
```

### Running Specific Test Module
```python
# Run a specific test file
pytest src/model_checker/jupyter/tests/unit/test_adapters.py -v

# Run with Jupyter environment mocked
pytest src/model_checker/jupyter/tests/unit/test_notebook_helpers.py -v

# Run with coverage
pytest src/model_checker/jupyter/tests/unit/ --cov=model_checker.jupyter
```

## Test Fixtures

Common fixtures are defined in `../conftest.py` and include:
- Mock Jupyter environments
- Sample notebook structures
- Test widget configurations
- Unicode test strings

## Coverage

These unit tests provide comprehensive coverage of:
- Jupyter environment detection and adaptation
- Notebook cell manipulation
- UI component generation
- Unicode and mathematical symbol handling
- Error display in notebook contexts

## Contributing

When adding new unit tests:
1. Mock Jupyter/IPython dependencies appropriately
2. Test both notebook and console environments
3. Verify Unicode symbols render correctly
4. Test interactive components with mock inputs
5. Ensure tests work without actual Jupyter runtime

## See Also

- [Jupyter Package Documentation](../../README.md)
- [Integration Tests](../integration/README.md)
- [Debug Tools](../../debug/README.md)
- [Notebook Examples](../../notebooks/README.md)