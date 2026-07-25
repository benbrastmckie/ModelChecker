# Settings Package Tests

This directory contains tests for the settings package following the builder pattern structure.

## Test Organization

### unit/
Unit tests for settings components:
- `test_settings.py` - Core settings validation and management tests

### integration/
Integration tests for settings pipeline:
- `test_settings_pipeline.py` - Settings pipeline and propagation tests

### e2e/
Not present here by design: end-to-end coverage exercises the CLI and project-generation
pipeline, not individual package internals, and lives at core level (`code/tests/e2e/`,
`builder/tests/e2e/`, `iterate/tests/e2e/`), parametrized over all four theories -- see
`theory_lib/docs/THEORY_ARCHITECTURE.md`'s End-to-End Testing section.

### fixtures/
Shared test data and mock objects (to be populated as needed)

### utils/
Test utilities and helpers (to be populated as needed)

## Running Tests

```bash
# Run all settings tests
pytest src/model_checker/settings/tests/

# Run specific test category
pytest src/model_checker/settings/tests/unit/
pytest src/model_checker/settings/tests/integration/

# Run with coverage
pytest src/model_checker/settings/tests/ --cov=model_checker.settings
```

## Test Guidelines

1. **Unit Tests**: Test single settings functions in isolation
2. **Integration Tests**: Test settings propagation through components
3. **E2E Tests**: Test complete settings workflows

All tests use pytest for consistent test execution.