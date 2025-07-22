# Exclusion Theory Tests

This directory contains unit tests for the exclusion (witness uninegation) theory implementation.

## Test Structure

- `conftest.py` - Common fixtures for all tests
- `test_operators.py` - Tests for operator implementations
- `test_witness_semantics.py` - Tests for witness semantics and registry
- `test_examples.py` - Tests that examples run correctly

## Running Tests

To run all exclusion theory tests:
```bash
./run_tests.py exclusion
```

To run specific test modules:
```bash
pytest src/model_checker/theory_lib/exclusion/tests/test_operators.py
pytest src/model_checker/theory_lib/exclusion/tests/test_witness_semantics.py
pytest src/model_checker/theory_lib/exclusion/tests/test_examples.py
```

## Test Coverage

The tests cover:
- Operator availability and properties
- Semantic clause implementations
- Witness registry functionality
- Witness predicate generation
- Example execution and validation