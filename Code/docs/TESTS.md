# ModelChecker Test Suite Guide

This document provides a comprehensive overview of the testing infrastructure for the ModelChecker project, explaining how to use the available test suites, what they cover, and how to extend them.

## Overview

The ModelChecker project has two main test runners:

1. **test_package.py**: Tests core framework components, utilities, and common functionality
2. **test_theories.py**: Tests theory-specific implementations and their logical properties

These test runners provide a unified interface for testing different aspects of the codebase, ensuring both the framework and individual theories work correctly.

## test_package.py: Core Framework Testing

### What It Tests

`test_package.py` runs tests for:

- **Core Components**: Base functionality independent of specific theories
- **Builder**: Project creation and management tools
- **Settings**: Configuration and settings management
- **Utils**: Utility functions and shared helpers
- **Theory Library**: Common functionality across theories (e.g., metadata, versioning, discovery)
- **Iterator**: Model iteration and enumeration
- Other non-theory specific components

#### Theory Library Infrastructure Testing

The theory library includes specialized infrastructure tests in `src/model_checker/theory_lib/tests/` that verify:

- **Metadata Management**: Version tracking, citation files, license generation across all theories
- **Theory Discovery**: Automatic loading and registration of semantic theories
- **Cross-Theory Integration**: Compatibility and consistency between different theories
- **Library Infrastructure**: Core functionality that all theories depend on

These infrastructure tests are run via:
```bash
python test_package.py --components theory_lib
```

For detailed documentation on theory library testing, including theory-specific tests and debugging guides, see [theory_lib/tests/README.md](src/model_checker/theory_lib/tests/README.md).

### Usage

Basic usage:

```bash
python test_package.py
```

This runs all tests for all discovered components.

### Command-Line Options

#### Test Options

- `--components COMPONENT [COMPONENT ...]`: Test specific components
- `--verbose, -v`: Enable verbose output
- `--failfast, -x`: Stop after the first failure
- `--list, -l`: List available components without running tests

Example:
```bash
python test_package.py --components settings builder --verbose
```

#### Metadata Management

The test_package.py runner also includes tools for managing theory metadata:

- `--metadata-report`: Print a report on version/license consistency
- `--update-versions VERSION`: Update all theory versions to a specific value
- `--create-licenses`: Create license files for all theories
- `--create-citations`: Create citation files for all theories 
- `--author NAME`: Specify author name for license/citation files
- `--license-type TYPE`: Specify license type (default: GPL-3.0)

Example:
```bash
python test_package.py --metadata-report
python test_package.py --update-versions 1.1.0 --author "Author Name"
```

### Available Components

Components are automatically discovered by scanning for test directories. Common components include:

- `builder`: Tests for the project creation system
- `settings`: Tests for the settings management system
- `theory_lib`: Tests for common theory library functionality
- `iterate`: Tests for the model iteration system

To see all available components:
```bash
python test_package.py --list
```

### Output Format

The output follows a clear format:
1. Standard pytest output for each component
2. A summary of test results for each component
3. An overall success/failure message

## test_theories.py: Theory-Specific Testing

### What It Tests

`test_theories.py` tests the logical correctness of semantic theories, including:

- **Semantic Clauses**: Tests the semantic definitions of operators
- **Logical Principles**: Tests expected logical properties and principles
- **Countermodels**: Tests the correctness of countermodel construction
- **Integration**: Tests how different components of a theory work together
- **Edge Cases**: Tests behavior in corner cases and boundary conditions

### Usage

Basic usage:

```bash
python test_theories.py
```

This runs tests for all available theories.

### Command-Line Options

- `--theories THEORY [THEORY ...]`: Test specific theories
- `--verbose, -v`: Enable verbose output 
- `--failfast, -x`: Stop after the first failure
- `--list, -l`: List available theories without running tests

Example:
```bash
python test_theories.py --theories default bimodal --verbose
```

### Available Theories

Theories are automatically discovered from the `theory_lib` directory. Current theories include:

- `logos`: Tests for modular hyperintensional truthmaker semantics with comprehensive subtheory testing
- `default`: Tests for the default bilateral truthmaker semantics  
- `exclusion`: Tests for unilateral semantics with exclusion relations
- `imposition`: Tests for semantics with imposition relations
- `bimodal`: Tests for bimodal temporal semantics

Each theory includes its own comprehensive test suite - see individual theory documentation:
- [theory_lib/logos/tests/README.md](src/model_checker/theory_lib/logos/tests/README.md) - Logos theory testing
- [theory_lib/default/tests/README.md](src/model_checker/theory_lib/default/tests/README.md) - Default theory testing
- Additional theory-specific testing documentation in respective theory directories

To see all available theories:
```bash
python test_theories.py --list
```

### Advanced Theory Testing: Logos Example

The **logos theory** implements a comprehensive **dual-testing framework** that serves as a template for other theories. It demonstrates advanced testing capabilities with **inclusive-by-default** CLI control:

#### Dual Testing Architecture

**Two Test Types**:
- **Example Tests** (129 tests): Integration tests using real logical arguments
- **Unit Tests** (109 tests): Implementation tests for individual components

#### Inclusive-by-Default CLI

The logos theory supports granular test control while defaulting to maximum coverage:

```bash
# All logos tests (examples + unit tests = 238+ total)
python test_theories.py --theories logos

# Restrict to examples only (129 tests)
python test_theories.py --theories logos --examples

# Restrict to unit tests only (109 tests) 
python test_theories.py --theories logos --package
```

#### Subtheory-Specific Testing

```bash
# All extensional tests (examples + unit tests)
python test_theories.py --theories logos --extensional

# Modal examples only (~23 tests)
python test_theories.py --theories logos --modal --examples

# Counterfactual unit tests only
python test_theories.py --theories logos --counterfactual --package
```

#### Precise Example Targeting

```bash
# Single example (appears in multiple test files)
python test_theories.py --theories logos --examples EXT_CM_1

# Multiple specific examples
python test_theories.py --theories logos --examples EXT_CM_1 CF_TH_2

# Wildcard patterns
python test_theories.py --theories logos --examples "CF_*"    # All CF examples
python test_theories.py --theories logos --examples "*_TH_*" # All theorems
```

#### Unit Test Categories

```bash
# Operator implementation tests only
python test_theories.py --theories logos --package --operators

# Semantic method tests only  
python test_theories.py --theories logos --package --semantics

# Error condition tests only
python test_theories.py --theories logos --package --error-conditions
```

#### Complex Combinations

```bash
# Modal semantic tests only
python test_theories.py --theories logos --modal --package --semantics

# Extensional examples with verbose output
python test_theories.py --theories logos --extensional --examples -v
```

This testing approach provides:
- **No Duplication**: Single source of truth for each test
- **Inclusive-by-Default**: Maximum coverage without explicit flags
- **Granular Control**: Precise targeting for debugging
- **Fast Development**: Quick testing of specific components

**Template Available**: See [Theory Testing Framework Guide](../src/model_checker/theory_lib/tests/README.md#theory-testing-framework-guide) for implementing similar testing in other theories.

### Output Format

Similar to `test_package.py`, the output includes:
1. Standard pytest output for each theory's tests
2. A summary of test results for each theory
3. An overall success/failure message

## Writing New Tests

### For Core Components (`test_package.py`)

1. **Directory Structure**: Create or use existing tests directory:
   ```
   src/model_checker/component_name/tests/
   ```

2. **Test Files**: Add test files named `test_*.py` within the tests directory.

3. **Test Classes and Functions**: Use pytest fixtures and assertions:
   ```python
   import pytest
   from model_checker.component_name import SomeClass
   
   class TestSomeClass:
       def test_some_function(self):
           instance = SomeClass()
           result = instance.some_function()
           assert result == expected_result
   ```

### For Theories (`test_theories.py`)

1. **Directory Structure**: Add tests in theory's tests directory:
   ```
   src/model_checker/theory_lib/theory_name/tests/
   ```

2. **Test Files**: Add test files named `test_*.py` within the tests directory.

3. **Test Structure**: Follow existing test patterns for logical tests:
   ```python
   import pytest
   from model_checker.theory_lib.theory_name import Semantics, Proposition
   
   def test_logical_principle():
       # Set up model
       semantics = Semantics(settings)
       
       # Test logical principle
       model = run_test_example("principle_name", semantics)
       assert model.is_valid == expected_result
   ```

## Metadata Testing

The `test_package.py` runner includes a comprehensive metadata testing system that verifies:

- **Version Consistency**: Ensures all theories have proper version information
- **Licensing**: Validates that license files exist and have the correct format
- **Citation**: Checks that citation files exist for academic attribution
- **Compatibility**: Verifies that theories are compatible with the core framework version

The metadata tests help maintain consistency across the project and ensure proper licensing and attribution.

## Test Coverage

The test suites aim to provide comprehensive coverage:

1. **Unit Tests**: Test individual components in isolation
2. **Integration Tests**: Test components working together
3. **Functional Tests**: Test end-to-end workflows
4. **Logical Tests**: Test semantic properties and logical principles
5. **Edge Cases**: Test boundary conditions and special cases

## Best Practices

1. **Run Tests Regularly**: Run tests after making changes
2. **Run All Tests**: Before submitting contributions, run both test suites
3. **Add Tests for New Features**: Include tests for any new functionality
4. **Maintain Test Independence**: Tests should not depend on each other
5. **Use Descriptive Names**: Name tests clearly to describe what they're testing

## Debugging Test Failures

When tests fail:

1. **Examine Output**: Read the test failure message carefully
2. **Check Assertions**: Verify what was expected versus what was received
3. **Use Verbose Mode**: Run with `-v` for more detailed output
4. **Isolate Failures**: Run specific tests to narrow down the issue
5. **Check Test Environment**: Ensure proper environment setup

## Running Tests in Development

For development work, it's recommended to:

1. Run specific component tests when making localized changes:
   ```bash
   python test_package.py --components component_name
   ```

2. Run theory-specific tests when modifying a theory:
   ```bash
   python test_theories.py --theories theory_name
   ```

3. Run all tests before submitting contributions:
   ```bash
   python test_package.py && python test_theories.py
   ```

4. Check metadata consistency when modifying versioning or licensing:
   ```bash
   python test_package.py --metadata-report
   ```

## NixOS-specific Testing

When working on NixOS, always use the provided scripts rather than direct Python commands to ensure proper PYTHONPATH configuration. The test scripts automatically handle path setup for NixOS environments.

## Test Organization Philosophy

The ModelChecker testing approach follows these principles:

1. **Separation of Concerns**: Core framework tests are separate from theory-specific tests
2. **Comprehensive Coverage**: Tests cover both functionality and logical correctness
3. **Automation**: Tests are automated and easily run from command line
4. **Clear Feedback**: Test output clearly indicates what passed and failed
5. **Test as Documentation**: Tests serve as executable documentation for expected behavior
6. **Fail Fast**: Tests fail immediately on issues to provide quick feedback

## Continuous Integration

While not currently implemented, the test suite structure is designed to work well with continuous integration systems. Running both `test_package.py` and `test_theories.py` provides comprehensive verification of the codebase.