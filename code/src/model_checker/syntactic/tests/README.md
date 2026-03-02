# Syntactic Package Tests

This directory contains tests for the syntactic package following the builder pattern structure.

## Test Organization

### unit/
Unit tests for individual syntactic components:
- `test_atoms.py` - Atomic proposition tests
- `test_operators.py` - Operator definition tests
- `test_sentence.py` - Sentence structure tests
- `test_syntax.py` - Core Syntax class tests

### integration/
Integration tests for component interactions:
- `test_collection.py` - Collection and traversal tests

### e2e/
End-to-end tests for complete workflows (to be added as needed)

### fixtures/
Shared test data and mock objects (to be populated as needed)

### utils/
Test utilities and helpers (to be populated as needed)

## Running Tests

```bash
# Run all syntactic tests
pytest src/model_checker/syntactic/tests/

# Run specific test category
pytest src/model_checker/syntactic/tests/unit/
pytest src/model_checker/syntactic/tests/integration/

# Run with coverage
pytest src/model_checker/syntactic/tests/ --cov=model_checker.syntactic
```

## Test Guidelines

1. **Unit Tests**: Test single classes or functions in isolation
2. **Integration Tests**: Test interactions between syntactic components
3. **E2E Tests**: Test complete formula parsing and validation workflows

All tests use pytest fixtures defined in `conftest.py` for consistent test setup and teardown.