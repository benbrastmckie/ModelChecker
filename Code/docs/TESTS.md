# Testing Guide

[← Back to Technical Docs](README.md) | [Implementation →](IMPLEMENTATION.md) | [Style Guide →](STYLE_GUIDE.md) | [Development →](DEVELOPMENT.md) | [Architecture →](ARCHITECTURE.md)

## Table of Contents

1. [Testing Philosophy](#testing-philosophy)
2. [Test Organization](#test-organization)
3. [Test Categories](#test-categories)
4. [Running Tests](#running-tests)
5. [Writing Tests](#writing-tests)
6. [Theory-Specific Testing](#theory-specific-testing)
7. [Infrastructure Testing](#infrastructure-testing)
8. [Test Utilities](#test-utilities)
9. [Best Practices](#best-practices)

## Testing Philosophy

Following the project's design philosophy outlined in [CLAUDE.md](../CLAUDE.md), our testing approach emphasizes:

- **Fail Fast**: Tests should expose errors clearly rather than masking them with complex conditional logic
- **Deterministic Behavior**: No fallbacks or implicit conversions that could hide issues
- **Clear Data Flow**: Explicit parameter passing and error propagation
- **Root Cause Analysis**: Tests should identify structural problems, not just symptoms

## Test Organization

The ModelChecker project has two main test runners:

### test_package.py
Tests core framework components, utilities, and common functionality:
- Core components (base functionality)
- Builder (project creation and management)
- Settings (configuration management)
- Utils (utility functions)
- Theory library infrastructure
- Iterator (model iteration)

### test_theories.py
Tests theory-specific implementations and logical properties:
- Semantic implementations
- Operator behavior
- Example validation
- Theory-specific features

## Test Categories

### 1. Example Tests (Integration Tests)

**Purpose**: Validate that the model checker produces correct results for logical examples

**Characteristics**:
- Test complete model checking pipeline from formula parsing to result validation
- Use realistic logical examples that demonstrate theory capabilities
- Validate both valid arguments (no countermodel) and invalid arguments (countermodel found)
- Cover all operator types and their interactions

**Location**: 
- `theory_lib/*/tests/test_*_examples.py`
- `theory_lib/*/subtheories/*/tests/test_*_examples.py`

### 2. Unit Tests (Implementation Tests)

**Purpose**: Validate individual software components work correctly

**Characteristics**:
- Test semantic methods directly (without full model checking pipeline)
- Test operator implementations and their semantic clauses
- Test registry and loading mechanisms
- Test error conditions and edge cases
- Validate API contracts and data structures

**Location**:
- `theory_lib/*/tests/test_*.py` (non-example tests)
- Component-specific test directories

### 3. Infrastructure Tests

**Purpose**: Verify cross-theory functionality and framework infrastructure

**Characteristics**:
- Metadata management (versions, citations, licenses)
- Theory discovery and loading
- Cross-theory compatibility
- Common functionality validation

**Location**: `theory_lib/tests/`

## Running Tests

### Basic Usage

```bash
# Run all tests
python test_package.py
python test_theories.py

# Run specific component tests
python test_package.py --components builder settings
python test_theories.py --theories logos bimodal

# Verbose output
python test_package.py -v
python test_theories.py -v

# Stop on first failure
python test_package.py -x
python test_theories.py -x
```

### Theory-Specific Testing

The testing framework follows an **inclusive-by-default** approach:

```bash
# Test everything for logos (all examples + all unit tests)
python test_theories.py --theories logos

# Test specific subtheory
python test_theories.py --theories logos --modal
python test_theories.py --theories logos --counterfactual

# Restrict to examples only
python test_theories.py --theories logos --examples

# Restrict to unit tests only
python test_theories.py --theories logos --unit
```

### Advanced Options

```bash
# List available components
python test_package.py --list

# Metadata management
python test_package.py --metadata-report
python test_package.py --update-versions 1.0.0
python test_package.py --create-licenses --author "Your Name"
python test_package.py --create-citations
```

### NixOS Testing

On NixOS, use the provided wrapper script:

```bash
./run_tests.py          # Run all tests
./run_tests.py logos    # Test specific theory
./run_tests.py --unit   # Unit tests only
./run_tests.py --examples # Examples only
```

## Writing Tests

### Test Structure

```python
import unittest
from model_checker import BuildExample
from model_checker.theory_lib.logos import logos_theory

class TestLogosExamples(unittest.TestCase):
    """Test logos theory examples."""
    
    def setUp(self):
        """Set up test fixtures."""
        self.theory = logos_theory
        
    def test_modus_ponens(self):
        """Test that modus ponens is valid."""
        premises = ["A", "(A \\rightarrow B)"]
        conclusions = ["B"]
        settings = {'N': 3, 'expectation': False}
        
        model = BuildExample("test", self.theory)
        model.premises = premises
        model.conclusions = conclusions
        model.set_settings(settings)
        
        result = model.run_single_test()
        self.assertFalse(result, "Modus ponens should be valid")
```

### Example Test Pattern

For testing logical examples:

```python
def test_example_validity(self):
    """Test a specific logical example."""
    # Define the example
    example = [
        ["A", "(A \\rightarrow B)"],  # Premises
        ["B"],                         # Conclusions
        {'N': 3, 'expectation': False} # Settings
    ]
    
    # Build and run
    model = BuildExample("test", self.theory)
    model.premises, model.conclusions = example[0], example[1]
    model.set_settings(example[2])
    
    # Verify result
    result = model.run_single_test()
    expectation = example[2]['expectation']
    
    if expectation:  # Expecting countermodel
        self.assertTrue(result, "Should find countermodel")
    else:  # Expecting validity
        self.assertFalse(result, "Should be valid")
```

### Unit Test Pattern

For testing individual components:

```python
def test_semantic_method(self):
    """Test a specific semantic method."""
    from model_checker.theory_lib.logos.semantic import LogosSemantics
    
    semantics = LogosSemantics()
    semantics.N = 3
    
    # Test specific functionality
    result = semantics.some_method(parameters)
    
    # Verify behavior
    self.assertEqual(result, expected_value)
```

## Theory-Specific Testing

Each theory should have:

### Directory Structure

```
theory_name/
├── tests/
│   ├── README.md                    # Test documentation
│   ├── __init__.py
│   ├── test_examples.py            # Example validation tests
│   ├── test_semantic.py            # Semantic method tests
│   ├── test_operators.py           # Operator tests
│   ├── test_iterate.py             # Model iteration tests
│   └── conftest.py                 # Pytest configuration
└── subtheories/ (if applicable)
    └── subtheory_name/tests/
        └── test_subtheory_examples.py
```

### Required Test Coverage

1. **All examples in examples.py** must have corresponding tests
2. **Core semantic methods** must be unit tested
3. **Each operator** must have behavioral tests
4. **Error conditions** must be tested
5. **Model iteration** (if supported) must be tested

## Infrastructure Testing

The theory library includes specialized infrastructure tests:

### Metadata Testing

```bash
# Check version consistency
python test_package.py --metadata-report

# Update all versions
python test_package.py --update-versions 1.2.0

# Create missing files
python test_package.py --create-licenses --author "Author Name"
python test_package.py --create-citations
```

### Theory Discovery Testing

Tests in `theory_lib/tests/test_meta_data.py` verify:
- All theories are discoverable
- Metadata files are consistent
- Version numbers match
- Required files exist

## Test Utilities

### Common Test Fixtures

```python
# In conftest.py
import pytest

@pytest.fixture
def basic_theory():
    """Provide a basic theory for testing."""
    from model_checker.theory_lib.logos import logos_theory
    return logos_theory

@pytest.fixture
def example_settings():
    """Provide standard test settings."""
    return {
        'N': 3,
        'contingent': False,
        'non_empty': False,
        'max_time': 10,
        'iterate': 1
    }
```

### Test Helpers

```python
def validate_countermodel(model, expected_properties):
    """Validate countermodel has expected properties."""
    # Check model structure
    assert hasattr(model, 'z3_model')
    assert hasattr(model, 'world_states')
    
    # Verify properties
    for prop, expected in expected_properties.items():
        actual = getattr(model, prop)
        assert actual == expected, f"{prop} mismatch"
```

## Best Practices

### Test Naming

- Use descriptive names: `test_modus_ponens_valid` not `test_1`
- Group related tests in classes
- Prefix with `test_` for discovery

### Test Independence

- Each test should be independent
- Use setUp/tearDown for initialization
- Don't rely on test execution order

### Error Messages

```python
# Good
self.assertTrue(result, 
    f"Double negation elimination should be valid in {theory_name}")

# Bad
self.assertTrue(result)
```

### Performance

- Keep individual tests fast (< 1 second)
- Use smaller N values for unit tests
- Mark slow tests with `@pytest.mark.slow`

### Documentation

- Include docstrings explaining what is tested
- Reference the logical principle being tested
- Document any special setup requirements

---

[← Back to Technical Docs](README.md) | [Implementation →](IMPLEMENTATION.md) | [Style Guide →](STYLE_GUIDE.md) | [Development →](DEVELOPMENT.md) | [Examples →](EXAMPLES.md)