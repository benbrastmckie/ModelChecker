# Iterate Integration Tests

## Overview

This directory contains integration tests for the iterate package, validating the iteration framework's interaction with models, constraints, and build systems. These tests ensure that model exploration, isomorphism detection, and constraint preservation work correctly in realistic scenarios.

## Modules

### test_build_example.py
**Purpose**: Tests integration with BuildExample for iterative model finding
**Dependencies**: `pytest`, `iterate`, `builder.example`

### test_constraint_preservation.py
**Purpose**: Tests constraint preservation across iteration steps
**Dependencies**: `pytest`, `iterate.constraints`, `z3`

### test_core_orchestration.py
**Purpose**: Tests orchestration of core iteration components
**Dependencies**: `pytest`, `iterate.core`

### test_enhanced_tracking.py
**Purpose**: Tests enhanced tracking features during iteration
**Dependencies**: `pytest`, `iterate.tracking`

### test_error_handling.py
**Purpose**: Tests error handling across integrated components
**Dependencies**: `pytest`, `iterate.errors`

### test_generator_interface.py
**Purpose**: Tests generator-based iteration interfaces
**Dependencies**: `pytest`, `iterate.generator`

### test_graph_isomorphism_integration.py
**Purpose**: Tests graph isomorphism detection in model exploration
**Dependencies**: `pytest`, `iterate.isomorphism`

### test_graph_utils.py
**Purpose**: Tests graph utility integration with models
**Dependencies**: `pytest`, `iterate.graph_utils`

### test_isomorphism.py
**Purpose**: Tests isomorphism detection algorithms
**Dependencies**: `pytest`, `iterate.isomorphism`

### test_iteration_control.py
**Purpose**: Tests iteration control flow and termination
**Dependencies**: `pytest`, `iterate.control`

### test_iterator_generator.py
**Purpose**: Tests iterator and generator patterns
**Dependencies**: `pytest`, `iterate.generator`

### test_metrics.py
**Purpose**: Tests iteration metrics and performance tracking
**Dependencies**: `pytest`, `iterate.metrics`

### test_models.py
**Purpose**: Tests model handling during iteration
**Dependencies**: `pytest`, `iterate.models`

### test_real_theory_integration.py
**Purpose**: Tests iteration with actual theory implementations
**Dependencies**: `pytest`, `iterate`, theory modules

## Usage

```bash
# Run all integration tests
./run_tests.py --integration iterate

# Run specific test
pytest src/model_checker/iterate/tests/integration/test_isomorphism.py -v
```

## See Also

- [Unit Tests](../unit/README.md)
- [Iterate Package](../../README.md)