# Output Package Test Suite

[← Back to Output](../README.md) | [Unit Tests →](unit/) | [Integration Tests →](integration/)

## Directory Structure

```
tests/
├── README.md              # This file - test suite documentation
├── __init__.py           # Test package initialization
├── conftest.py           # Pytest configuration and fixtures
├── unit/                 # Unit tests for individual components
│   ├── formatters/       # Formatter-specific tests
│   ├── strategies/       # Strategy-specific tests
│   └── progress/         # Progress indicator tests
├── integration/          # Integration tests for component interactions
│   ├── builder/          # Builder integration tests
│   ├── modes/           # Output mode tests
│   └── interactive/     # Interactive mode tests
└── e2e/                 # End-to-end workflow tests
```

## Overview

The **output package test suite** provides comprehensive coverage of all output subsystem components, following a three-tier testing strategy that ensures both individual component correctness and system-wide integration. Tests are organized to mirror the package structure, making it easy to locate and maintain test code.

### Testing Philosophy

- **Unit Tests**: Verify individual components in isolation with mocked dependencies
- **Integration Tests**: Test component interactions and data flow
- **End-to-End Tests**: Validate complete user workflows from input to output
- **Mock-First Design**: Use mocks to isolate components and control test conditions
- **Comprehensive Coverage**: Target 95%+ code coverage with meaningful tests

## Test Categories

### Unit Tests (`unit/`)

Test individual components in isolation:

#### Core Components
- `test_config.py` - Output configuration and CLI parsing (100% coverage)
- `test_errors.py` - Custom exception classes and error handling (100% coverage)
- `test_helpers.py` - Utility functions and file operations (100% coverage)
- `test_input_provider.py` - Input abstraction and mock provider tests
- `test_prompts.py` - User prompt generation and validation
- `test_color_formatting.py` - ANSI color code handling

#### Formatters
- `test_markdown_formatter.py` - Markdown generation and formatting
- `test_json_serialization.py` - JSON data serialization
- `test_notebook_formatter.py` - Jupyter notebook creation (if exists)

#### Strategies
- `test_batch_strategy.py` - Batch accumulation logic (if exists)
- `test_sequential_strategy.py` - Immediate save behavior (if exists)
- `test_interactive_strategy.py` - User-controlled saves (if exists)

#### Progress Indicators
- `test_progress_core.py` - Core progress tracking
- `test_progress_spinner.py` - Spinner animation logic
- `test_progress_display.py` - Progress display formatting
- `test_progress_animated.py` - Animation sequences

### Integration Tests (`integration/`)

Test component interactions:

#### Builder Integration
- `test_build_integration.py` - OutputManager with BuildModule
- `test_cli_arguments.py` - CLI argument processing and configuration

#### Output Modes
- `test_output_modes.py` - Batch, sequential, and interactive modes
- `test_output_directory.py` - Directory creation and management

#### Data Collection
- `test_collector_integration.py` - Model data extraction
- `test_model_data_collection.py` - Complete data collection workflow

#### Interactive Features
- `test_interactive.py` - Interactive mode workflow
- `test_output_manager_interactive.py` - OutputManager in interactive mode

#### Formatting
- `test_markdown_relations.py` - Relation formatting in Markdown
- `test_output_integration.py` - Complete output generation

### End-to-End Tests (`e2e/`)

Complete workflow validation:

- `test_end_to_end_save.py` - Full save workflow from example to files

## Test Fixtures

### Shared Fixtures (`conftest.py`)

Common test fixtures and utilities:

```python
@pytest.fixture
def mock_build_module():
    """Create a mock BuildModule for testing."""
    # Returns configured mock
    pass

@pytest.fixture
def temp_output_dir(tmp_path):
    """Create temporary output directory."""
    return tmp_path / "test_outputs"

@pytest.fixture
def sample_model_data():
    """Provide sample model checking results."""
    return {
        'example_name': 'TEST_1',
        'theory_name': 'TestTheory',
        'model': {...}
    }
```

### Mock Patterns

Standard mocking approaches:

```python
# Mock user input
from model_checker.output import MockInputProvider
mock_input = MockInputProvider(['y', 'n', 'a'])

# Mock file system
with patch('builtins.open', mock_open()) as mock_file:
    # Test file operations
    pass

# Mock BuildModule
mock_module = Mock()
mock_module.output_directory = '/tmp/test'
mock_module.general_settings = {'save_output': True}
```

## Running Tests

### All Tests

```bash
# Run complete test suite
pytest src/model_checker/output/tests/

# With coverage report
pytest src/model_checker/output/tests/ --cov=model_checker.output

# Verbose output
pytest src/model_checker/output/tests/ -v
```

### Specific Categories

```bash
# Unit tests only
pytest src/model_checker/output/tests/unit/

# Integration tests
pytest src/model_checker/output/tests/integration/

# End-to-end tests
pytest src/model_checker/output/tests/e2e/
```

### Individual Tests

```bash
# Single test file
pytest src/model_checker/output/tests/unit/test_markdown_formatter.py

# Single test method
pytest src/model_checker/output/tests/unit/test_markdown_formatter.py::TestMarkdownFormatter::test_format_basic

# Tests matching pattern
pytest src/model_checker/output/tests/ -k "interactive"
```

## Test Development

### Adding New Tests

1. **Identify Category**: Unit, integration, or e2e
2. **Create Test File**: Follow naming convention `test_*.py`
3. **Use Fixtures**: Leverage existing fixtures when possible
4. **Mock Dependencies**: Isolate the component under test
5. **Assert Behavior**: Test both success and failure cases

### Test Structure

```python
import pytest
from unittest.mock import Mock, patch
from model_checker.output.component import Component

class TestComponent:
    """Test suite for Component class."""
    
    def test_basic_functionality(self):
        """Test basic component behavior."""
        component = Component()
        result = component.process(input_data)
        assert result == expected_output
    
    def test_error_handling(self):
        """Test component handles errors gracefully."""
        component = Component()
        with pytest.raises(ComponentError):
            component.process(invalid_data)
    
    @patch('model_checker.output.component.dependency')
    def test_with_mock(self, mock_dep):
        """Test component with mocked dependency."""
        mock_dep.return_value = mock_result
        component = Component()
        result = component.process_with_dependency()
        mock_dep.assert_called_once_with(expected_args)
```

## Coverage Goals

Current coverage (as of 2025-01-10):

- **Overall**: 97% line coverage (3046/3154 statements)
- **Core Components**: 100% coverage achieved for config, errors, helpers
- **Error Handling**: All error conditions tested
- **Edge Cases**: Boundary conditions and special cases covered
- **Total Tests**: 251 tests, all passing

Check coverage:

```bash
# Generate coverage report
pytest src/model_checker/output/tests/ --cov=model_checker.output --cov-report=html

# View report
open htmlcov/index.html
```

## Performance Testing

For performance-sensitive components:

```python
import time

def test_formatter_performance():
    """Ensure formatter completes in reasonable time."""
    formatter = MarkdownFormatter()
    large_data = generate_large_dataset()
    
    start = time.time()
    result = formatter.format(large_data)
    elapsed = time.time() - start
    
    assert elapsed < 1.0  # Should complete within 1 second
```

## Continuous Integration

Tests run automatically on:
- Pull requests
- Commits to main branch
- Nightly builds

Integration with GitHub Actions ensures all tests pass before merging.

## Troubleshooting

### Common Issues

1. **Import Errors**: Ensure PYTHONPATH includes src directory
2. **File Not Found**: Use fixtures for file operations
3. **Flaky Tests**: Add retries or increase timeouts
4. **Mock Leakage**: Use proper setup/teardown

### Debug Commands

```bash
# Run with debugging output
pytest -vv --tb=long

# Stop on first failure
pytest -x

# Run with pdb on failure
pytest --pdb

# Show print statements
pytest -s
```

## Related Documentation

- **[Output Package Documentation](../README.md)** - Main package documentation
- **[Formatters Documentation](../formatters/README.md)** - Formatter details
- **[Strategies Documentation](../strategies/README.md)** - Strategy patterns
- **[Testing Guide](../../../../docs/TESTS.md)** - Framework-wide testing standards

---

[← Back to Output](../README.md) | [Unit Tests →](unit/) | [Integration Tests →](integration/)