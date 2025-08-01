# Test Suite: Comprehensive Validation for Exclusion Theory

[← Back to Exclusion](../README.md) | [Examples →](../examples.py) | [Documentation →](../docs/README.md)

## Directory Structure

```
tests/
├── README.md                  # This file - test suite documentation
├── __init__.py                # Test module initialization
├── conftest.py                # Shared pytest fixtures and utilities
├── test_examples.py           # Validates all 38 example outcomes
├── test_iterate.py            # Tests model iteration functionality
├── test_operators.py          # Tests operator implementations
├── test_semantic_coverage.py  # Comprehensive semantic validation
└── test_witness_semantics.py  # Witness predicate system tests
```

## Overview

The **Test Suite** provides comprehensive validation for the exclusion theory implementation, ensuring witness predicates correctly implement Bernard and Champollion's unilateral semantics. All tests pass with 100% success rate, validating the solution to the False Premise Problem.

Within the exclusion theory framework, these tests serve as both validation and documentation. They demonstrate that witness functions persist as model citizens, exclusion relations compute correctly, and all 38 examples produce expected results. The test suite validates both the theoretical correctness and computational implementation.

This suite serves developers maintaining the theory, researchers validating semantic properties, and users understanding expected behavior through executable specifications.

## Running Tests

```bash
# Run all exclusion theory tests
./run_tests.py exclusion

# Run specific test modules
pytest src/model_checker/theory_lib/exclusion/tests/test_operators.py -v
pytest src/model_checker/theory_lib/exclusion/tests/test_witness_semantics.py -v
pytest src/model_checker/theory_lib/exclusion/tests/test_examples.py -v

# Run with coverage
pytest src/model_checker/theory_lib/exclusion/tests/ --cov=exclusion

# Expected output:
# ===== 47 passed in 3.2s =====
# All witness predicates functioning correctly!
```

## Test Coverage

### Core Functionality Tests

**test_operators.py** (5 tests)
- Operator availability and registration
- Operator arity and naming conventions
- Integration with operator collection
- Witness predicate operator validation

**test_witness_semantics.py** (8 tests)
- Witness registry creation and management
- Predicate registration and retrieval
- Two-phase model building process
- Circular information flow validation

**test_semantic_coverage.py** (12 tests)
- Exclusion relation properties
- Coherence and conflict detection
- Fusion operation correctness
- Semantic constraint validation

### Example Validation Tests

**test_examples.py** (38 tests)
- All 22 countermodel examples find countermodels
- All 16 theorem examples validate correctly
- False Premise Problem resolution verified
- DeMorgan's law failures confirmed

**test_iterate.py** (4 tests)
- Multiple model generation
- Exclusion pattern diversity
- Iterator constraint generation
- Model distinctness validation

## Documentation

### For Test Writers

- **[Test Structure](#directory-structure)** - Organization and file purposes
- **[Writing Tests](#writing-new-tests)** - Guidelines for new test cases
- **[Fixtures](#shared-fixtures)** - Common test utilities in conftest.py

### For Maintainers

- **[Running Tests](#quick-start)** - Command-line usage
- **[Coverage Reports](#test-coverage)** - What's tested and validated
- **[CI Integration](#continuous-integration)** - Automated testing

### For Researchers

- **[Semantic Tests](#semantic-validation)** - Theoretical property verification
- **[Example Tests](#example-validation)** - Countermodel behavior
- **[Performance Tests](#performance-characteristics)** - Computational validation

## Key Test Categories

1. **Unit Tests**: Individual component validation (operators, registry)
2. **Integration Tests**: Two-phase architecture and information flow
3. **Semantic Tests**: Theoretical property verification
4. **Example Tests**: Complete formula validation suite
5. **Performance Tests**: Timing and complexity validation

## Writing New Tests

### Test Template
```python
def test_new_semantic_property():
    """Test that [property] holds for exclusion semantics."""
    # Arrange
    theory = get_theory('exclusion')
    model = BuildExample("test", theory, 
        premises=['\\unineg A'],
        conclusions=['A'],
        settings={'N': 3}
    )
    
    # Act
    result = model.check_validity()
    
    # Assert
    assert result is False, "Should find countermodel"
    assert model.model_structure is not None
    # Additional semantic property checks
```

### Shared Fixtures

From conftest.py:
```python
@pytest.fixture
def exclusion_theory():
    """Provide exclusion theory instance."""
    return get_theory('exclusion')

@pytest.fixture
def simple_model(exclusion_theory):
    """Provide simple test model."""
    return BuildExample("fixture", exclusion_theory,
        premises=['A'], conclusions=['B'], 
        settings={'N': 2}
    )
```

## Semantic Validation

Key semantic properties tested:

1. **Exclusion Asymmetry**: `excludes(a, b)` doesn't imply `excludes(b, a)`
2. **Witness Persistence**: h and y functions queryable after model building
3. **Three-Condition Verification**: All conditions properly implemented
4. **Circular Dependencies**: Information flows correctly between phases

## Example Validation

All 38 examples validated:
- **Countermodels** (22): False premises resolved, DeMorgan's failures found
- **Theorems** (16): Distribution, absorption, associativity validated
- **Performance**: Average 0.005s per example

## Performance Characteristics

- **Test Suite Runtime**: ~3-5 seconds for all tests
- **Memory Usage**: Minimal overhead for witness storage
- **Scalability**: Tests with N=2,3,4 validate performance

## Continuous Integration

Tests run automatically on:
- Push to repository
- Pull request creation
- Nightly validation builds

Integration with GitHub Actions ensures theory stability.

## References

### Test Implementation

- **[Semantic Module](../semantic.py)** - Implementation being tested
- **[Operators Module](../operators.py)** - Operator implementations
- **[Examples Module](../examples.py)** - Test case definitions

### Testing Resources

- **[Pytest Documentation](https://docs.pytest.org/)** - Testing framework
- **[Test Standards](../../../tests/README.md)** - ModelChecker test guidelines
- **[CI Configuration](../../../.github/workflows/)** - Automation setup

---

[← Back to Exclusion](../README.md) | [Examples →](../examples.py) | [Documentation →](../docs/README.md)
