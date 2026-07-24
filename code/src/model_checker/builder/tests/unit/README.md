# Builder Unit Tests

## Overview

This directory contains unit tests for the builder package, providing comprehensive coverage of the core model checking and theory building functionality. These tests validate individual components in isolation, ensuring each module functions correctly according to its specifications.

## Modules

### test_comparison.py
**Purpose**: Tests comparison operations for build results and model structures
**Key Classes**: 
- `TestBuildComparison` - Tests for comparing build outputs
- `TestModelComparison` - Tests for model equality and difference detection
**Key Functions**: Tests comparison logic for build artifacts
**Dependencies**: `pytest`, `builder.comparison`
**Used By**: Builder package validation suite

### test_example.py
**Purpose**: Tests the BuildExample core functionality for model finding
**Key Classes**: 
- `TestBuildExampleCore` - Core BuildExample instantiation and validation
- `TestBuildExampleMethods` - Tests for model finding and countermodel generation
**Key Functions**: Tests `find_models()`, `check_validity()`, `generate_countermodels()`
**Dependencies**: `pytest`, `builder.example`, `z3`
**Used By**: Main builder functionality testing

### test_helpers.py
**Purpose**: Tests utility helper functions for the builder package
**Key Classes**: 
- `TestHelperFunctions` - Tests for builder utility functions
**Key Functions**: Tests string manipulation, path resolution, configuration helpers
**Dependencies**: `pytest`, `builder.helpers`
**Used By**: Builder utility validation

### test_loader.py
**Purpose**: Tests dynamic loading of theories and semantic modules
**Key Classes**: 
- `TestTheoryLoader` - Tests for loading theory modules
- `TestSemanticLoader` - Tests for semantic component loading
**Key Functions**: Tests `load_theory()`, `import_semantics()`, `validate_module()`
**Dependencies**: `pytest`, `builder.loader`, `importlib`
**Used By**: Theory integration testing

### test_progress.py
**Purpose**: Tests progress tracking and reporting functionality
**Key Classes**: 
- `TestProgressTracker` - Tests for build progress monitoring
**Key Functions**: Tests progress callbacks, status updates, completion tracking
**Dependencies**: `pytest`, `builder.progress`
**Used By**: Build monitoring validation

### test_project.py
**Purpose**: Tests project creation and management functionality
**Key Classes**: 
- `TestProjectCreation` - Tests for creating new theory projects
- `TestProjectStructure` - Tests for project directory structure
**Key Functions**: Tests `create_project()`, `setup_directories()`, `initialize_theory()`
**Dependencies**: `pytest`, `builder.project`, `pathlib`
**Used By**: Project scaffolding validation

### test_project_version.py
**Purpose**: Tests project versioning and migration functionality
**Key Classes**: 
- `TestProjectVersion` - Tests for version management
- `TestMigration` - Tests for project migration between versions
**Key Functions**: Tests version detection, compatibility checks, migration paths
**Dependencies**: `pytest`, `builder.project_version`
**Used By**: Version management validation

### test_runner.py
**Purpose**: Tests the main runner component for executing build processes
**Key Classes**: 
- `TestBuildRunner` - Tests for build execution orchestration
**Key Functions**: Tests `run_build()`, `execute_example()`, `process_results()`
**Dependencies**: `pytest`, `builder.runner`
**Used By**: Build execution validation

### test_serialize.py
**Purpose**: Tests serialization and deserialization of build artifacts
**Key Classes**: 
- `TestSerialization` - Tests for converting build results to/from various formats
**Key Functions**: Tests JSON, pickle, and custom serialization formats
**Dependencies**: `pytest`, `builder.serialize`, `json`
**Used By**: Data persistence validation

### test_translation.py
**Purpose**: Tests translation between different logical representations
**Key Classes**: 
- `TestFormulaTranslation` - Tests for formula format conversions
- `TestModelTranslation` - Tests for model representation conversions
**Key Functions**: Tests LaTeX to internal format, ASCII to Unicode conversions
**Dependencies**: `pytest`, `builder.translation`
**Used By**: Format conversion validation

### test_validation.py
**Purpose**: Tests validation logic for inputs and configurations
**Key Classes**: 
- `TestInputValidation` - Tests for validating user inputs
- `TestConfigValidation` - Tests for configuration validation
**Key Functions**: Tests formula validation, settings validation, constraint checking
**Dependencies**: `pytest`, `builder.validation`
**Used By**: Input validation suite

### test_z3_isolation.py
**Purpose**: Tests Z3 solver isolation and context management
**Key Classes**: 
- `TestZ3Isolation` - Tests for Z3 context isolation between builds
**Key Functions**: Tests context creation, cleanup, isolation verification
**Dependencies**: `pytest`, `builder.z3_isolation`, `z3`
**Used By**: Solver isolation validation

### test_z3_utils.py
**Purpose**: Tests Z3 utility functions and helpers
**Key Classes**: 
- `TestZ3Utils` - Tests for Z3-specific utility functions
**Key Functions**: Tests constraint building, solver configuration, result extraction
**Dependencies**: `pytest`, `builder.z3_utils`, `z3`
**Used By**: Z3 integration validation

## Usage

### Running All Unit Tests
```bash
# From project root
./run_tests.py --unit builder

# Or directly with pytest
pytest src/model_checker/builder/tests/unit/ -v
```

### Running Specific Test Module
```python
# Run a specific test file
pytest src/model_checker/builder/tests/unit/test_example.py -v

# Run a specific test class
pytest src/model_checker/builder/tests/unit/test_example.py::TestBuildExampleCore -v

# Run a specific test method
pytest src/model_checker/builder/tests/unit/test_example.py::TestBuildExampleCore::test_init_with_valid_inputs_succeeds -v
```

## Test Fixtures

Common fixtures are defined in `../conftest.py` and include:
- Mock theory configurations
- Sample formulas and models
- Z3 solver instances
- Temporary directories for project tests

## Coverage

These unit tests aim for >90% code coverage of the builder package, with particular focus on:
- Core BuildExample functionality
- Project creation and management
- Z3 integration and isolation
- Validation and error handling
- Serialization and format conversion

## Contributing

When adding new unit tests:
1. Follow the naming convention: `test_<module_name>.py`
2. Group related tests in classes: `Test<ComponentName>`
3. Use descriptive test method names: `test_<scenario>_<expected_outcome>`
4. Include docstrings explaining what each test validates
5. Use appropriate fixtures to avoid code duplication
6. Ensure tests are isolated and don't depend on execution order

## See Also

- [Builder Package Documentation](../../README.md)
- [Integration Tests](../integration/README.md)
- [E2E Tests](../e2e/README.md)
- [Test Utilities](../utils/README.md)