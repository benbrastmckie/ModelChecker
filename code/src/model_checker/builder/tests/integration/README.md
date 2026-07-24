# Builder Integration Tests

## Overview

This directory contains integration tests for the builder package, validating interactions between builder components and with other packages. These tests ensure that the complete build pipeline, project generation, and theory integration work correctly together.

## Modules

### test_build_module_theories.py
**Purpose**: Tests BuildModule integration with various theory implementations
**Key Classes**: Tests for theory-specific build configurations
**Key Functions**: Tests theory loading, semantic integration, model generation
**Dependencies**: `pytest`, `builder`, theory modules
**Used By**: Theory integration validation

### test_cli_interactive_integration.py
**Purpose**: Tests CLI and interactive mode integration
**Key Classes**: Tests for command-line interface with user interaction
**Key Functions**: Tests prompt handling, interactive project creation, user input
**Dependencies**: `pytest`, `builder.cli`, `output.prompts`
**Used By**: CLI interaction validation

### test_component_integration.py
**Purpose**: Tests integration between builder package components
**Key Classes**: Tests for component interactions
**Key Functions**: Tests data flow between modules, component coordination
**Dependencies**: `pytest`, all builder modules
**Used By**: Internal integration validation

### test_error_propagation.py
**Purpose**: Tests error propagation through the build pipeline
**Key Classes**: Tests for error handling across components
**Key Functions**: Tests error bubbling, context preservation, recovery
**Dependencies**: `pytest`, `builder`, error handling modules
**Used By**: Error flow validation

### test_generated_projects.py
**Purpose**: Tests complete project generation and validation
**Key Classes**: Tests for generated project structures
**Key Functions**: Tests project creation, file generation, structure validation
**Dependencies**: `pytest`, `builder.project`, filesystem
**Used By**: Project generation validation

### test_interactive.py
**Purpose**: Tests interactive build features and user workflows
**Key Classes**: Tests for interactive mode operations
**Key Functions**: Tests user prompts, input validation, workflow completion
**Dependencies**: `pytest`, `builder`, `output.input_provider`
**Used By**: Interactive feature validation

### test_output_directory_guidance.py
**Purpose**: Tests output directory management and guidance
**Key Classes**: Tests for output directory handling
**Key Functions**: Tests directory creation, naming, organization
**Dependencies**: `pytest`, `builder`, `pathlib`
**Used By**: Output management validation

### test_performance.py
**Purpose**: Tests build performance and optimization
**Key Classes**: Performance benchmarking tests
**Key Functions**: Tests build times, memory usage, optimization effectiveness
**Dependencies**: `pytest`, `builder`, timing utilities
**Used By**: Performance validation

### test_workflow.py
**Purpose**: Tests complete build workflows end-to-end
**Key Classes**: Tests for full build pipelines
**Key Functions**: Tests workflow orchestration, step sequencing, result generation
**Dependencies**: `pytest`, `builder`, all components
**Used By**: Workflow validation

## Usage

### Running All Integration Tests
```bash
# From project root
./run_tests.py --integration builder

# Or directly with pytest
pytest src/model_checker/builder/tests/integration/ -v
```

### Running Specific Test Module
```python
# Run a specific integration test
pytest src/model_checker/builder/tests/integration/test_workflow.py -v

# Run with detailed output
pytest src/model_checker/builder/tests/integration/test_generated_projects.py -vv

# Run performance tests
pytest src/model_checker/builder/tests/integration/test_performance.py --benchmark
```

## Test Scenarios

These integration tests cover:
- Complete build pipelines from input to output
- Theory loading and integration
- Project generation and validation
- Interactive mode workflows
- Error propagation across components
- Performance characteristics

## Dependencies

Integration tests may require:
- Actual theory implementations
- Filesystem access for project generation
- Z3 solver for model building
- Interactive input simulation

## Contributing

When adding integration tests:
1. Test realistic workflows and use cases
2. Verify component interactions thoroughly
3. Test both success and failure paths
4. Ensure cleanup of generated artifacts
5. Document complex test scenarios

## See Also

- [Unit Tests](../unit/README.md)
- [E2E Tests](../e2e/README.md)
- [Builder Package](../../README.md)