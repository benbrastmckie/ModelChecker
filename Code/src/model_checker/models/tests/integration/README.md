# Models Integration Tests

## Overview

This directory contains integration tests for the models package, validating interactions between model structures, constraints, and semantic definitions.

## Modules

### test_constraints_injection.py
**Purpose**: Tests constraint injection into model structures
**Dependencies**: `pytest`, `models.constraints`, `z3`

### test_imports.py
**Purpose**: Tests import relationships and module loading
**Dependencies**: `pytest`, `models`, `importlib`

### test_integration.py
**Purpose**: Tests overall models package integration
**Dependencies**: `pytest`, all models modules

## Usage

```bash
# Run all integration tests
./run_tests.py --integration models

# Run specific test
pytest src/model_checker/models/tests/integration/test_constraints_injection.py -v
```

## See Also

- [Unit Tests](../unit/README.md)
- [Models Package](../../README.md)