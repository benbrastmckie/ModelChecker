# Jupyter Tests

## Overview

This directory contains the test suite for the jupyter package, validating Jupyter notebook integration, interactive displays, and debugging tools. Tests are organized by scope to ensure comprehensive coverage of all Jupyter-related functionality.

## Test Organization

### Subdirectories

- **[unit/](unit/README.md)** - Component isolation tests
  - Contains: 5 test modules for individual components
  - Tests adapters, UI builders, Unicode handling
  - See README for complete module documentation

- **[integration/](integration/README.md)** - Integration tests
  - Contains: Widget interaction tests
  - Tests Jupyter environment integration
  - See README for integration details

- **[fixtures/](fixtures/)** - Test data and mocks
  - Contains: Mock notebooks, widget configurations
  - Sample display outputs, test cells

- **[utils/](utils/)** - Testing utilities
  - Contains: Jupyter environment mocks
  - Display capture helpers

## Key Test Files

### conftest.py
**Purpose**: Pytest configuration and Jupyter-specific fixtures
**Key Fixtures**:
- `mock_jupyter_env` - Simulated Jupyter environment
- `mock_ipython` - Mock IPython instance
- `test_notebook` - Sample notebook structure
- `widget_config` - Test widget configurations

### __init__.py
**Purpose**: Test package initialization

## Test Coverage

| Component | Unit Tests | Integration Tests |
|-----------|------------|------------------|
| Adapters | ✓ | ✓ |
| UI Builders | ✓ | ✓ |
| Unicode Handling | ✓ | - |
| Notebook Helpers | ✓ | - |
| Widget Interaction | - | ✓ |
| Debug Tools | ✓ | - |

## Running Tests

### All Tests
```bash
# Run all jupyter tests
./run_tests.py jupyter

# With coverage
pytest src/model_checker/jupyter/tests/ --cov=model_checker.jupyter
```

### By Test Level
```bash
# Unit tests only
./run_tests.py --unit jupyter

# Integration tests only
./run_tests.py --integration jupyter
```

### Specific Tests
```bash
# Test adapters
pytest src/model_checker/jupyter/tests/unit/test_adapters.py -v

# Test widget interaction
pytest src/model_checker/jupyter/tests/integration/test_widget_interaction.py -v
```

## Special Considerations

### Jupyter Environment Mocking

Since tests run outside actual Jupyter environments, we mock:
- IPython display functions
- Jupyter comm channels
- Widget state management
- Cell execution context

### Display Testing

Display outputs are captured and validated:
- HTML output for rich displays
- Markdown rendering
- LaTeX mathematical notation
- Unicode symbol display

## Development Guidelines

### Adding New Tests

1. **Mock Jupyter dependencies**:
   ```python
   from unittest.mock import Mock, patch
   
   @patch('IPython.display.display')
   def test_display_output(mock_display):
       # Test display functionality
   ```

2. **Test both notebook and console**:
   - Verify behavior in Jupyter notebooks
   - Ensure graceful degradation in IPython console

3. **Handle missing dependencies**:
   - Tests should pass even if Jupyter not installed
   - Use conditional imports and skips

## Known Issues

- Widget tests require ipywidgets mock
- Some display tests are environment-sensitive
- Unicode tests may vary by terminal encoding

## See Also

- [Jupyter Package](../README.md)
- [Debug Tools](../debug/README.md)
- [Notebook Examples](../notebooks/README.md)