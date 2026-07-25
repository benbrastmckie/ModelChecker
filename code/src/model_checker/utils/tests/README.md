# Utils Package Tests

This directory contains tests for the utils package following the builder pattern structure.

## Test Organization

### unit/
Unit tests for utility functions:
- `test_bitvector.py` - BitVector utility tests
- `test_context.py` - Context management tests
- `test_parsing.py` - Parsing utility tests
- `test_z3_helpers.py` - Z3 helper function tests

### integration/
Integration tests for utility interactions (to be added as needed)

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
# Run all utils tests
pytest src/model_checker/utils/tests/

# Run specific test category
pytest src/model_checker/utils/tests/unit/

# Run with coverage
pytest src/model_checker/utils/tests/ --cov=model_checker.utils
```

## Test Guidelines

1. **Unit Tests**: Test single utility functions in isolation
2. **Integration Tests**: Test utility function combinations
3. **E2E Tests**: Test utilities in complete workflows

All tests use pytest for consistent test execution.