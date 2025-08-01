# Testing Standards

[← Code Organization](CODE_ORGANIZATION.md) | [Back to Maintenance](README.md) | [Error Handling →](ERROR_HANDLING.md)

## Overview

This document defines testing standards for the ModelChecker codebase, including test organization, documentation, and execution guidelines.

## Test Directory Structure

```
theory_name/
└── tests/
    ├── README.md           # Test documentation with file tree
    ├── __init__.py
    ├── test_semantic.py    # Test semantic components
    ├── test_operators.py   # Test individual operators
    ├── test_examples.py    # Test example formulas
    └── test_iterate.py     # Test model iteration
```

## Test File Naming

- Prefix with `test_`: `test_semantic.py`
- Match the module being tested: `semantic.py` → `test_semantic.py`
- Use descriptive names for integration tests: `test_cross_theory_compatibility.py`

## Test Documentation Requirements

Every `tests/` directory must have a README.md that includes:

1. **Complete file tree** of test files
2. **Description** of each test file's purpose
3. **How to run** the tests
4. **Test categories** and coverage metrics

Example structure:
```markdown
# Theory Tests

## Test Suite Structure

```
tests/
├── README.md               # This file
├── test_semantic.py        # Core semantic functionality
├── test_operators.py       # Operator behavior validation
└── test_examples.py        # Example formula verification
```

## Running Tests

```bash
# Run all tests
pytest tests/

# Run specific test file
pytest tests/test_semantic.py

# Run with coverage
pytest --cov=theory_name tests/
```
```

## Test Organization

### Test Class Structure

```python
import unittest
from model_checker.theory_lib.theory_name import TheorySemantics

class TestTheorySemantics(unittest.TestCase):
    """Test core semantic functionality."""
    
    def setUp(self):
        """Set up test fixtures."""
        self.semantics = TheorySemantics()
    
    def test_specific_behavior(self):
        """Test description of specific behavior."""
        # Arrange
        input_data = ...
        
        # Act
        result = self.semantics.method(input_data)
        
        # Assert
        self.assertEqual(result, expected_value)
```

### Test Method Naming

Use descriptive names that explain what is being tested:

```python
def test_negation_operator_reverses_truth_value(self):
    """Test that negation reverses truth values."""
    pass

def test_conjunction_requires_both_operands_true(self):
    """Test conjunction truth conditions."""
    pass
```

## Test Categories

### Unit Tests
Test individual components in isolation:
- Operator definitions
- Semantic functions
- Utility methods

### Integration Tests
Test component interactions:
- Theory loading
- Example execution
- Cross-theory compatibility

### Example Tests
Validate all examples in examples.py:
- Countermodels are found where expected
- Theorems validate correctly
- Settings produce expected behavior

## Test Coverage Requirements

- Minimum 80% code coverage for semantic modules
- 100% coverage for operator definitions
- All examples must have corresponding tests

## Testing Best Practices

### Use Descriptive Assertions

```python
# GOOD - Clear failure message
self.assertEqual(
    len(operators), 
    5, 
    f"Expected 5 operators but found {len(operators)}: {list(operators.keys())}"
)

# BAD - Generic failure
assert len(operators) == 5
```

### Test Edge Cases

```python
def test_empty_formula_list(self):
    """Test behavior with empty formulas."""
    result = check_validity([], [])
    self.assertIsNotNone(result)

def test_maximum_atomic_propositions(self):
    """Test with maximum allowed N value."""
    settings = {'N': 64}  # Maximum bit vector size
    # Test behavior at limits
```

### Mock External Dependencies

```python
from unittest.mock import patch, MagicMock

@patch('z3.Solver')
def test_solver_timeout(self, mock_solver):
    """Test handling of Z3 solver timeout."""
    mock_solver.return_value.check.return_value = z3.unknown
    # Test timeout handling
```

## Running Tests

### Command Line

```bash
# Run all tests in a directory
pytest src/model_checker/theory_lib/theory_name/tests/

# Run specific test
pytest -k "test_negation_operator"

# Verbose output
pytest -v

# Stop on first failure
pytest -x
```

### Continuous Integration

Tests should be run automatically on:
- Pull requests
- Commits to main branch
- Release candidates

## Test Fixtures and Data

### Shared Test Data

```python
# tests/fixtures.py
VALID_FORMULAS = [
    "A",
    "(A \\wedge B)",
    "\\neg \\Box A",
]

INVALID_FORMULAS = [
    "A ∧ B",  # Unicode not allowed
    "(\\neg A)",  # Extra parentheses
]
```

### Parameterized Tests

```python
import pytest

@pytest.mark.parametrize("formula,expected", [
    ("A", True),
    ("(A \\wedge B)", True),
    ("A ∧ B", False),
])
def test_formula_validation(formula, expected):
    """Test formula validation with various inputs."""
    assert is_valid_formula(formula) == expected
```

---

[← Code Organization](CODE_ORGANIZATION.md) | [Back to Maintenance](README.md) | [Error Handling →](ERROR_HANDLING.md)