# Logos Theory Tests

This directory contains the core test suite for the Logos theory implementation, focusing on general theory functionality, cross-subtheory integration, and implementation-level unit testing.

## Directory Structure
```
tests/
├── README.md                  # This file
├── __init__.py               # Test package initialization
├── conftest.py               # Pytest configuration and fixtures
├── test_iterate.py           # Model iteration tests
├── test_operators.py         # Operator implementation tests
├── test_proposition.py       # Proposition class tests
├── test_registry.py          # Operator registry tests
├── test_semantic_coverage.py # Additional semantic method coverage
└── test_semantic_methods.py  # Core semantic method tests
```

## Test Files Overview

### Unit Tests

#### test_iterate.py
**Purpose**: Tests for model iteration functionality in logos theory

**Coverage**:
- `LogosModelIterator` class functionality
- `iterate_example()` function for finding multiple models
- Basic iteration with different subtheory combinations
- Model difference detection and constraints

**Key Test Areas**:
- **Basic Iteration**: Simple tests with minimal settings
- **Subtheory Combinations**: Iteration with different loaded subtheories
- **Mock Integration**: Tests using mock build modules

#### test_semantic_coverage.py
**Purpose**: Additional test coverage for LogosSemantics methods

**Coverage**: Tests for semantic methods identified as needing additional coverage
- Semantic method availability checks
- World-related method testing
- Core semantic relation methods

**Key Test Areas**:
- **Method Availability**: Verifies key semantic methods exist
- **World Methods**: Tests world-related semantic operations
- **Semantic Relations**: Tests compatibility, maximality, and other relations

#### test_semantic_methods.py
**Purpose**: Tests for the core LogosSemantics class and LogosProposition implementation

**Coverage**:
- `LogosSemantics` class methods and state management
- `LogosProposition` evaluation and truth conditions
- Semantic clause implementations across all operators
- State fusion and part-hood operations
- Verifier and falsifier set operations
- Error handling in semantic evaluation

**Key Test Areas**:
- **State Management**: Creation, fusion, and manipulation of semantic states
- **Truth Evaluation**: Proposition evaluation at different states and worlds
- **Operator Semantics**: Verification that all operators implement correct truth conditions
- **Edge Cases**: Boundary conditions and error states

#### test_operators.py
**Purpose**: Tests for all operator implementations across all subtheories

**Coverage**: Systematic testing of all 20+ operators in the Logos theory
- **Extensional**: ¬, ∧, ∨, →, ↔, ⊤, ⊥ (7 operators)
- **Modal**: □, ◇, CFBox, CFDiamond (4 operators)
- **Constitutive**: ≡, ≤, ⊑, ≼, reduction (5 operators)
- **Counterfactual**: □→, ◇→, imposition, could (4 operators)
- **Relevance**: All relevance-sensitive operators

**Key Test Areas**:
- **Operator Construction**: Proper instantiation and configuration
- **Semantic Clauses**: Correct implementation of truth conditions
- **Arity and Type Checking**: Parameter validation and type safety
- **Performance**: Efficiency of operator evaluation

#### test_registry.py
**Purpose**: Tests for the LogosOperatorRegistry system

**Coverage**: Dynamic operator loading and dependency management
- Subtheory loading and unloading
- Dependency resolution (extensional → modal → constitutive, etc.)
- Operator registration and discovery
- Error handling for missing dependencies
- Registry state management

**Key Test Areas**:
- **Dynamic Loading**: Loading specific subtheory combinations
- **Dependency Resolution**: Automatic loading of required dependencies
- **Error Conditions**: Handling of invalid subtheory names or circular dependencies
- **State Consistency**: Registry state across multiple loading operations

#### test_proposition.py
**Purpose**: Focused tests for LogosProposition class functionality

**Coverage**: Detailed testing of proposition-specific features
- Proposition creation and initialization
- Truth evaluation at specific states
- Proposition composition and decomposition
- Integration with different operator types
- Memory management and performance

**Key Test Areas**:
- **Proposition Lifecycle**: Creation, evaluation, and cleanup
- **State Interaction**: How propositions interact with semantic states
- **Operator Integration**: Proposition behavior with different operator types
- **Performance**: Efficiency of proposition evaluation

## Running Tests

### Basic Execution
```bash
# Run all logos core tests
pytest src/model_checker/theory_lib/logos/tests/

# Run specific test file
pytest src/model_checker/theory_lib/logos/tests/test_logos_examples.py

# Run with verbose output
pytest -v src/model_checker/theory_lib/logos/tests/
```

### Specific Test Categories
```bash
# Run only specific test files
pytest src/model_checker/theory_lib/logos/tests/test_iterate.py  # Iteration tests
pytest src/model_checker/theory_lib/logos/tests/test_semantic_coverage.py  # Coverage tests

# Run only unit tests
pytest src/model_checker/theory_lib/logos/tests/test_semantic_methods.py src/model_checker/theory_lib/logos/tests/test_operators.py src/model_checker/theory_lib/logos/tests/test_registry.py src/model_checker/theory_lib/logos/tests/test_proposition.py

# Run specific unit test categories
pytest src/model_checker/theory_lib/logos/tests/test_operators.py  # Operator tests only
pytest src/model_checker/theory_lib/logos/tests/test_registry.py  # Registry tests only
```

### Integration with Project Testing
```bash
# Run via project test runner (includes these tests)
python test_theories.py --theories logos

# Run only logos unit tests via project runner
python test_theories.py --theories logos --package

# Run with additional flags
python test_theories.py --theories logos --package -v
```

## Test Structure and Standards

### Integration Test Format
Integration tests follow the standard ModelChecker format:
```python
example_name = {
    'premises': ['(A \\rightarrow B)', 'A'],
    'conclusions': ['B'],
    'settings': {
        'N': 3,
        'contingent': True,
        'max_time': 3,
        'expectation': False  # False = valid, True = invalid
    }
}
```

### Unit Test Format
Unit tests use pytest conventions with fixtures and parametrization:
```python
@pytest.fixture
def logos_semantics():
    return LogosSemantics({'N': 3})

@pytest.mark.parametrize("operator_name,operator_class", [
    ("\\neg", NegationOperator),
    ("\\wedge", AndOperator),
    # ...
])
def test_operator_implementation(operator_name, operator_class):
    # Test implementation
    pass
```

## Test Dependencies and Setup

### Required Dependencies
All tests in this directory require:
- **Full Logos Theory**: All subtheories must be available
- **LogosSemantics**: Core semantic framework
- **LogosOperatorRegistry**: For dynamic operator loading
- **pytest**: Testing framework with fixtures

### Test Fixtures
Common fixtures available in `conftest.py`:
- `logos_semantics`: Pre-configured LogosSemantics instance
- `operator_registry`: LogosOperatorRegistry with all subtheories loaded
- `sample_propositions`: Standard test propositions for reuse
- `test_settings`: Standard settings dictionaries

## Debugging Failed Tests

### Test Failures
When tests fail:
1. **Check Subtheory Loading**: Ensure all required subtheories are available
2. **Verify Test Logic**: Confirm the logical argument or test case is correct
3. **Model Size**: Some tests may need larger N values
4. **Operator Interactions**: Check for conflicts between subtheory operators
5. **Timeout Issues**: Complex tests may need longer timeouts

### Unit Test Failures
When unit tests fail:
1. **Isolate the Component**: Run specific test files to narrow down issues
2. **Check Dependencies**: Ensure all required operators/classes are available
3. **Verify Test Data**: Confirm test fixtures are properly configured
4. **Implementation Changes**: Check if recent changes broke existing functionality

### Common Issues
- **Import Errors**: Missing subtheory dependencies
- **Registry State**: Registry not properly reset between tests
- **Memory Issues**: Large test suites may hit memory limits
- **Timeout Errors**: Complex semantic evaluation taking too long

## Test Coverage Goals

### Coverage Goals
- **All Subtheory Combinations**: Test major combinations of 2-3 subtheories
- **Cross-Operator Validation**: Ensure operators from different subtheories work together
- **Complex Reasoning**: Advanced tests that stress-test the complete system
- **Regression Prevention**: Critical tests that catch breaking changes

### Unit Coverage
- **All Public Methods**: Every public method in core classes should be tested
- **Error Conditions**: Expected failure modes should be tested
- **Edge Cases**: Boundary conditions and unusual inputs
- **Performance**: Basic performance characteristics should be validated

## Integration with Overall Testing Strategy

### Relationship to Subtheory Tests
- **Core Tests (This Directory)**: General theory functionality and cross-subtheory integration
- **Subtheory Tests**: Located in `subtheories/*/tests/` for theory-specific validation
- **Complementary Coverage**: Core tests focus on integration, subtheory tests focus on specific functionality

### Test Hierarchy
1. **Unit Tests (This Directory)**: Test individual components in isolation
2. **Subtheory Tests**: Test specific logical systems and their principles
3. **System Tests**: End-to-end testing via project test runners

## Documentation Links

For related testing documentation:
- **Overall Testing Strategy**: [../UNIT_TESTS.md](../UNIT_TESTS.md)
- **Logos Theory Overview**: [../README.md](../README.md)
- **Subtheory-Specific Tests**:
  - [../subtheories/extensional/tests/README.md](../subtheories/extensional/tests/README.md)
  - [../subtheories/modal/tests/README.md](../subtheories/modal/tests/README.md)
  - [../subtheories/constitutive/tests/README.md](../subtheories/constitutive/tests/README.md)
  - [../subtheories/counterfactual/tests/README.md](../subtheories/counterfactual/tests/README.md)
  - [../subtheories/relevance/tests/README.md](../subtheories/relevance/tests/README.md)

## Contributing to Tests

### Adding New Integration Tests
1. Add integration tests to appropriate test files based on the feature being tested
2. Follow standard example format with premises, conclusions, settings
3. Include proper expectation values
4. Document the logical principle being tested

### Adding New Unit Tests
1. Choose appropriate test file based on component being tested
2. Use existing fixtures where possible
3. Follow pytest naming conventions (`test_*`)
4. Include docstrings explaining what is being tested
5. Add parametrized tests for systematic coverage

### Test Maintenance
1. **Update Tests with API Changes**: Keep tests current with implementation
2. **Preserve Regression Tests**: Don't remove tests that caught bugs
3. **Improve Coverage**: Add tests for uncovered code paths
4. **Performance Monitoring**: Watch for tests that become slow over time

---

[← Back to Logos Theory Documentation](../README.md) | [Back to Theory Library](../../README.md)