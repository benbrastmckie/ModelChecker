# Syntactic Integration Tests

## Overview

This directory contains integration tests for the syntactic package, validating formula parsing, operator collections, and syntactic analysis in integrated scenarios.

## Modules

### test_collection.py
**Purpose**: Tests operator collection and registration
**Dependencies**: `pytest`, `syntactic.operators`, `syntactic.collection`

## Usage

```bash
# Run all integration tests
./run_tests.py --integration syntactic

# Run specific test
pytest src/model_checker/syntactic/tests/integration/test_collection.py -v
```

## See Also

- [Unit Tests](../unit/README.md)
- [Syntactic Package](../../README.md)