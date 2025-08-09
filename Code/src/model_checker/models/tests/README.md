# Models Package Tests

[← Back to Models](../README.md) | [Testing Guide →](../../../../docs/TESTS.md)

## Overview

This test suite validates the refactored model checking components moved from the original `model.py` module. Tests are organized following the ModelChecker testing philosophy of fail-fast behavior and deterministic validation.

## Test Organization

```
tests/
├── README.md                   # This documentation
├── __init__.py                # Test package initialization
├── test_semantic.py           # SemanticDefaults unit tests
├── test_proposition.py        # PropositionDefaults unit tests
├── test_constraints.py        # ModelConstraints unit tests
├── test_structure.py          # ModelDefaults unit tests
├── test_printing.py           # Printing functionality tests
├── test_analysis.py           # Analysis utilities tests
├── test_integration.py        # Cross-component integration tests
└── conftest.py               # Pytest configuration and fixtures
```

## Running Tests

### Using run_tests.py (Recommended)

```bash
# Run all models tests
./run_tests.py --package --components models

# Run with verbose output
./run_tests.py --package --components models -v

# Stop on first failure
./run_tests.py --package --components models -x
```

### Direct pytest execution

```bash
# Run all tests in this directory
pytest src/model_checker/models/tests/

# Run specific test file
pytest src/model_checker/models/tests/test_semantic.py -v

# Run specific test
pytest src/model_checker/models/tests/test_semantic.py::TestSemanticDefaults::test_fusion_operation -v
```

## Test Categories

### Unit Tests

Each component has dedicated unit tests that validate:
- Initialization and configuration
- Core method functionality
- Edge cases and error conditions
- API contracts

### Integration Tests

The `test_integration.py` file validates:
- Inter-component communication
- Import compatibility
- Inheritance relationships
- Full pipeline functionality

## Test Coverage Goals

- **SemanticDefaults**: 100% coverage of public methods
- **PropositionDefaults**: Core proposition operations
- **ModelConstraints**: Constraint generation logic
- **ModelDefaults**: Solver interaction and model building
- **Utilities**: All helper functions

## Writing New Tests

Follow the patterns established in the existing test files:

```python
import unittest
from model_checker.models.semantic import SemanticDefaults

class TestSemanticDefaults(unittest.TestCase):
    """Test SemanticDefaults functionality."""
    
    def setUp(self):
        """Set up test fixtures."""
        self.settings = {'N': 3}
        self.semantics = SemanticDefaults(self.settings)
    
    def test_specific_behavior(self):
        """Test description following naming convention."""
        # Arrange
        input_data = ...
        
        # Act
        result = self.semantics.method(input_data)
        
        # Assert
        self.assertEqual(result, expected)
```

## Regression Testing

During refactoring, these tests ensure:
- No functionality is lost during extraction
- All imports continue to work
- Performance characteristics are maintained
- Error handling remains consistent

---

[← Back to Models](../README.md) | [Testing Guide →](../../../../docs/TESTS.md)