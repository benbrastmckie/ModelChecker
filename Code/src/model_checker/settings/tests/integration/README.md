# Settings Integration Tests

## Overview

This directory contains integration tests for the settings package, validating configuration pipelines and settings integration with other packages.

## Modules

### test_settings_pipeline.py
**Purpose**: Tests complete settings pipeline from loading to validation
**Dependencies**: `pytest`, `settings`, configuration modules

## Usage

```bash
# Run all integration tests
./run_tests.py --integration settings

# Run specific test
pytest src/model_checker/settings/tests/integration/test_settings_pipeline.py -v
```

## See Also

- [Unit Tests](../unit/README.md)
- [Settings Package](../../README.md)