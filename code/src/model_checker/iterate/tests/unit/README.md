# Iterate Unit Tests

## Overview

This directory contains unit tests for the iterate package, which provides the iteration framework for exploring model spaces and finding counterexamples. These tests validate the core iteration logic, constraint management, and model exploration strategies.

## Modules

### test_base_iterator.py
**Purpose**: Tests the base iterator class and its abstract interface
**Key Classes**: 
- `TestBaseIterator` - Tests for base iterator initialization
- `TestIteratorInterface` - Tests for abstract method requirements
**Key Functions**: Tests initialization, interface contracts, method signatures
**Dependencies**: `pytest`, `iterate.base_iterator`
**Used By**: Iterator framework validation

### test_constraints.py
**Purpose**: Tests constraint management during iteration
**Key Classes**: 
- `TestConstraintManager` - Tests for constraint accumulation
- `TestConstraintApplication` - Tests for applying constraints to models
**Key Functions**: Tests constraint addition, removal, combination
**Dependencies**: `pytest`, `iterate.constraints`, `z3`
**Used By**: Constraint system validation

### test_constraints_error_paths.py
**Purpose**: Tests error handling in constraint operations
**Key Classes**: 
- `TestConstraintErrors` - Tests for constraint error conditions
- `TestErrorRecovery` - Tests for error recovery mechanisms
**Key Functions**: Tests invalid constraints, conflict detection, recovery
**Dependencies**: `pytest`, `iterate.constraints`
**Used By**: Error handling validation

### test_core.py
**Purpose**: Tests core iteration logic and model exploration
**Key Classes**: 
- `TestIterationCore` - Tests for main iteration loop
- `TestModelExploration` - Tests for model space exploration
**Key Functions**: Tests iteration steps, termination conditions, result collection
**Dependencies**: `pytest`, `iterate.core`
**Used By**: Core iteration validation

### test_core_abstract_methods.py
**Purpose**: Tests abstract method implementations in core classes
**Key Classes**: 
- `TestAbstractMethods` - Tests for required method implementations
**Key Functions**: Tests method overrides, interface compliance
**Dependencies**: `pytest`, `iterate.core`
**Used By**: Interface compliance validation

### test_core_no_state_transfer.py
**Purpose**: Tests iteration without state transfer between steps
**Key Classes**: 
- `TestStatelessIteration` - Tests for stateless iteration mode
**Key Functions**: Tests independent iteration steps, no state leakage
**Dependencies**: `pytest`, `iterate.core`
**Used By**: Stateless iteration validation

### test_coverage_improvements.py
**Purpose**: Tests for improving code coverage and edge cases
**Key Classes**: 
- `TestCoverageGaps` - Tests for previously uncovered code paths
**Key Functions**: Tests rare conditions, boundary cases, error paths
**Dependencies**: `pytest`, `iterate`
**Used By**: Coverage improvement validation

### test_errors.py
**Purpose**: Tests error handling and custom exceptions
**Key Classes**: 
- `TestIterateErrors` - Tests for custom error classes
- `TestErrorFormatting` - Tests for error message formatting
**Key Functions**: Tests error creation, context preservation, formatting
**Dependencies**: `pytest`, `iterate.errors`
**Used By**: Error system validation

### test_models_edge_cases.py
**Purpose**: Tests edge cases in model handling during iteration
**Key Classes**: 
- `TestModelEdgeCases` - Tests for unusual model configurations
**Key Functions**: Tests empty models, single-state models, cyclic models
**Dependencies**: `pytest`, `iterate.models`
**Used By**: Edge case validation

### test_simplified_iterator.py
**Purpose**: Tests the simplified iterator implementation
**Key Classes**: 
- `TestSimplifiedIterator` - Tests for simplified iteration interface
**Key Functions**: Tests simple iteration patterns, basic functionality
**Dependencies**: `pytest`, `iterate.simplified_iterator`
**Used By**: Simplified interface validation

### test_validation.py
**Purpose**: Tests input validation for iteration parameters
**Key Classes**: 
- `TestValidation` - Tests for parameter validation
- `TestConfigValidation` - Tests for configuration validation
**Key Functions**: Tests input validation, type checking, range validation
**Dependencies**: `pytest`, `iterate.validation`
**Used By**: Input validation system

## Usage

### Running All Unit Tests
```bash
# From project root
./run_tests.py --unit iterate

# Or directly with pytest
pytest src/model_checker/iterate/tests/unit/ -v
```

### Running Specific Test Module
```python
# Run a specific test file
pytest src/model_checker/iterate/tests/unit/test_core.py -v

# Run with detailed failure output
pytest src/model_checker/iterate/tests/unit/test_constraints.py -vv

# Run coverage analysis
pytest src/model_checker/iterate/tests/unit/ --cov=model_checker.iterate --cov-report=term-missing
```

## Test Fixtures

Common fixtures are defined in `../conftest.py` and include:
- Mock iteration configurations
- Sample model spaces
- Pre-built constraint sets
- Test iteration scenarios

## Coverage

These unit tests provide comprehensive coverage of:
- Base iterator interface and implementations
- Constraint management during iteration
- Model exploration strategies
- Error handling and recovery
- Edge cases and boundary conditions
- Simplified iteration patterns

## Contributing

When adding new unit tests:
1. Test iteration termination conditions thoroughly
2. Verify constraints are properly accumulated
3. Test both finite and infinite iteration scenarios
4. Ensure state isolation between iterations
5. Test error recovery mechanisms

## See Also

- [Iterate Package Documentation](../../README.md)
- [Integration Tests](../integration/README.md)
- [Core Module](../../core.py)
- [Constraints Module](../../constraints.py)