# Utils Integration Tests

## Overview

This directory contains integration tests for the utils package. Currently, there are no integration tests as utils functions are primarily tested through unit tests and their usage in other packages' integration tests.

## Future Tests

Potential integration tests could cover:
- Z3 context management across multiple packages
- Formatting utilities with actual output systems
- Parsing utilities with syntactic package integration

## Usage

```bash
# Run if integration tests are added
./run_tests.py --integration utils
```

## See Also

- [Unit Tests](../unit/README.md)
- [Utils Package](../../README.md)