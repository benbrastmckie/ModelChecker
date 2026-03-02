# Jupyter Integration Tests

## Overview

This directory contains integration tests for the jupyter package, validating notebook integration, widget interactions, and display functionality in Jupyter environments.

## Modules

### test_widget_interaction.py
**Purpose**: Tests interactive widget functionality and user interactions
**Dependencies**: `pytest`, `jupyter.widgets`, `ipywidgets`

### __init__.py
**Purpose**: Package initialization for test discovery

## Usage

```bash
# Run all integration tests
./run_tests.py --integration jupyter

# Run specific test
pytest src/model_checker/jupyter/tests/integration/test_widget_interaction.py -v
```

## See Also

- [Unit Tests](../unit/README.md)
- [Jupyter Package](../../README.md)