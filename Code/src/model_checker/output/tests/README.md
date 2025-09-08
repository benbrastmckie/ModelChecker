# Output Package Tests

This directory contains tests for the output package following the builder pattern structure.

## Test Organization

### unit/
Unit tests for individual output components:
- `test_input_provider.py` - InputProvider class tests
- `test_prompts.py` - Prompt handling tests
- `test_color_formatting.py` - ANSI color formatting tests
- `test_markdown_formatter.py` - Markdown formatting tests
- `test_json_serialization.py` - JSON serialization tests
- `test_progress_core.py` - Progress indicator core tests
- `test_progress_spinner.py` - Spinner animation tests
- `test_progress_display.py` - Progress display tests
- `test_progress_animated.py` - Animated progress tests

### integration/
Integration tests for component interactions:
- `test_build_integration.py` - Output with builder integration
- `test_collector_integration.py` - Data collector integration
- `test_interactive.py` - Interactive mode tests
- `test_markdown_relations.py` - Markdown relation formatting
- `test_model_data_collection.py` - Model data collection
- `test_output_integration.py` - Output system integration
- `test_output_manager_interactive.py` - OutputManager interactive mode
- `test_output_modes.py` - Different output modes
- `test_cli_arguments.py` - CLI argument handling
- `test_output_directory.py` - Output directory management

### e2e/
End-to-end tests for complete workflows:
- `test_end_to_end_save.py` - Complete save workflow

### fixtures/
Shared test data and mock objects:
- `builder/` - Builder-related test fixtures

### utils/
Test utilities and helpers (to be populated as needed)

## Running Tests

```bash
# Run all output tests
pytest src/model_checker/output/tests/

# Run specific test category
pytest src/model_checker/output/tests/unit/
pytest src/model_checker/output/tests/integration/
pytest src/model_checker/output/tests/e2e/

# Run with coverage
pytest src/model_checker/output/tests/ --cov=model_checker.output
```

## Test Guidelines

1. **Unit Tests**: Test single classes or functions in isolation
2. **Integration Tests**: Test interactions between output components
3. **E2E Tests**: Test complete output workflows including file I/O

All tests use pytest fixtures defined in `conftest.py` for consistent test setup and teardown.

## Note on Progress Tests

The progress indicator tests were previously in `output/progress/tests/` but have been 
flattened into this directory to maintain a consistent package structure. All progress
tests are prefixed with `test_progress_` for easy identification.