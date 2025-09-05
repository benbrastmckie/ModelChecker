# Test Organization Standards

[← Testing Standards](TESTING_STANDARDS.md) | [Back to Maintenance](README.md)

## Overview

This document defines the organization standards for test suites across the ModelChecker codebase, ensuring consistency, maintainability, and comprehensive coverage.

## Test Suite Structure

### Standard Test Directory Layout

```
package_name/
├── tests/
│   ├── README.md                    # Comprehensive test documentation
│   ├── __init__.py                  # Test package initialization
│   ├── conftest.py                  # Pytest configuration and shared fixtures
│   ├── fixtures.py                  # Shared test data and utilities
│   │
│   ├── Unit Tests (Component-Specific)
│   ├── test_[component].py          # Individual component tests
│   ├── test_[feature].py            # Feature-specific tests
│   │
│   ├── Integration Tests
│   ├── test_components.py           # Consolidated component interactions
│   ├── test_integration.py          # Cross-component workflows
│   ├── test_error_propagation.py    # Error handling across components
│   ├── test_full_pipeline.py        # End-to-end execution tests
│   │
│   └── Specialized Tests
│       ├── test_edge_cases.py       # Boundary conditions
│       └── test_performance.py      # Performance benchmarks
```

## Test File Standards

### 1. File Naming Convention

- **Unit tests**: `test_[component].py` - matches the component being tested
- **Integration tests**: `test_[workflow]_integration.py` - describes the integration scenario
- **Consolidated tests**: `test_components.py` - for grouping related component tests
- **Edge cases**: `test_edge_cases.py` or `test_[component]_edge_cases.py`

### 2. File Organization Template

```python
"""
Test module description following docstring standards.

This module tests [specific functionality] ensuring [key properties].
"""
import unittest
from unittest.mock import Mock, patch
from typing import Any, Dict, List

# Import fixtures
from .fixtures import (
    create_mock_flags,
    create_test_module,
    VALID_FORMULAS,
    INVALID_SETTINGS
)

# Import components being tested
from model_checker.package.component import Component


class TestComponentBase(unittest.TestCase):
    """Base class with common setup if needed."""
    
    def setUp(self):
        """Set up test fixtures."""
        self.component = Component()


class TestComponentCore(TestComponentBase):
    """Test core functionality of Component."""
    
    def test_initialization(self):
        """Test component initializes correctly."""
        # Arrange
        config = {"key": "value"}
        
        # Act
        component = Component(config)
        
        # Assert with descriptive message
        self.assertIsNotNone(
            component,
            "Component should initialize with valid config"
        )


class TestComponentEdgeCases(TestComponentBase):
    """Test edge cases and boundary conditions."""
    
    def test_empty_input(self):
        """Test handling of empty input."""
        with self.assertRaises(ValueError) as context:
            self.component.process([])
        
        self.assertIn("empty", str(context.exception).lower())


class TestComponentParameterized(unittest.TestCase):
    """Parameterized tests for various scenarios."""
    
    def test_various_inputs(self):
        """Test component with various input types."""
        test_cases = [
            # (input, expected_output, description)
            ("valid", True, "Valid input"),
            ("", False, "Empty string"),
            (None, False, "None input"),
        ]
        
        for input_val, expected, description in test_cases:
            with self.subTest(case=description):
                result = validate_input(input_val)
                self.assertEqual(
                    result, expected,
                    f"{description}: expected {expected}, got {result}"
                )


if __name__ == '__main__':
    unittest.main()
```

## Shared Fixtures Standards

### fixtures.py Structure

```python
"""
Shared test fixtures and utilities for [package] tests.

Provides standardized test data, mock objects, and helper functions
following TESTING_STANDARDS.md.
"""

# Test Data Constants
VALID_INPUTS = [...]
INVALID_INPUTS = [...]

# Mock Object Factories
def create_mock_component(**kwargs) -> Mock:
    """Create properly configured mock with defaults."""
    defaults = {...}
    defaults.update(kwargs)
    return Mock(**defaults)

# Test Data Generators
def generate_test_cases(pattern: str, count: int) -> List[Dict]:
    """Generate test cases following pattern."""
    pass

# Assertion Helpers
def assert_valid_structure(obj: Any, test_case: unittest.TestCase) -> None:
    """Assert object has valid structure with descriptive errors."""
    pass

# Cleanup Utilities
class TempFileCleanup:
    """Context manager for automatic cleanup."""
    pass

# Test Decorators
def requires_dependency(dependency: str):
    """Skip test if dependency not available."""
    pass
```

## Test Categories

### 1. Unit Tests

**Purpose**: Test individual components in isolation  
**Structure**:
- One test class per component class/function
- Mock all external dependencies
- Test all public methods
- Include edge cases

**Example**:
```python
class TestModuleLoader(unittest.TestCase):
    """Test ModuleLoader in isolation."""
    
    @patch('importlib.import_module')
    def test_load_module(self, mock_import):
        """Test loading with mocked import."""
        # Isolated test with mocks
```

### 2. Integration Tests

**Purpose**: Test component interactions  
**Structure**:
- Test real component instances together
- Minimal mocking (only external systems)
- Focus on data flow between components
- Verify error propagation

**Example**:
```python
class TestLoaderRunnerIntegration(unittest.TestCase):
    """Test loader and runner work together."""
    
    def test_load_and_execute(self):
        """Test complete workflow."""
        # Real components, minimal mocks
```

### 3. Consolidated Tests

**Purpose**: Group related component tests  
**Structure**:
- Combine tests for tightly coupled components
- Reduce test file proliferation
- Maintain clear organization with test classes

**Example**: See `test_components.py` in builder tests

### 4. Edge Case Tests

**Purpose**: Test boundary conditions  
**Structure**:
- Unicode handling
- Empty inputs
- Very large inputs
- Concurrent access
- Resource limits

### 5. Error Propagation Tests

**Purpose**: Ensure errors handled correctly  
**Structure**:
- Test each component's error cases
- Verify error messages are informative
- Check error recovery
- Test cascading failures

## Test Documentation

### README.md Requirements

Each test directory must have a comprehensive README.md including:

1. **Test Suite Structure** - Complete file tree
2. **Test Categories** - Description of each category
3. **Running Tests** - Commands for different scenarios
4. **Coverage Requirements** - Targets and current status
5. **Test Writing Guidelines** - Patterns and practices
6. **Maintenance Notes** - How to add/update tests

See builder tests README.md for reference implementation.

## Coverage Standards

### Coverage Requirements by Component Type

| Component Type | Line Coverage | Branch Coverage | Notes |
|---------------|--------------|-----------------|-------|
| Core Logic | ≥90% | ≥85% | Critical paths 100% |
| Utilities | ≥85% | ≥80% | All public functions |
| Error Handling | 100% | 100% | All error paths |
| Integration Points | ≥80% | ≥75% | Key workflows |

### Coverage Commands

```bash
# Generate coverage report
pytest --cov=package --cov-report=html

# Enforce minimum coverage
pytest --cov=package --cov-fail-under=80

# Show missing lines
pytest --cov=package --cov-report=term-missing
```

## Best Practices

### 1. Test Independence
- Each test must be independent
- No shared state between tests
- Use setUp/tearDown for initialization
- Clean up resources

### 2. Descriptive Naming
- Test method names describe what is tested
- Use `test_[what]_[when]_[expected]` pattern
- Example: `test_validation_empty_input_raises_error`

### 3. Assertion Messages
- Always include descriptive assertion messages
- Help debugging when tests fail
- Include actual vs expected values

### 4. Mock Management
- Mock at appropriate boundaries
- Don't over-mock (hides integration issues)
- Verify mock interactions

### 5. Parameterized Testing
- Use for testing multiple similar scenarios
- Keep test data close to tests
- Use descriptive subtest names

## Migration Guidelines

When refactoring existing tests:

1. **Assess Current State** - Identify gaps and organization issues
2. **Create Fixtures** - Extract common test data and utilities
3. **Consolidate When Appropriate** - Combine related test files
4. **Add Missing Categories** - Ensure all test types represented
5. **Update Documentation** - Create/update README.md
6. **Verify Coverage** - Ensure no regression in coverage

## CI/CD Integration

Tests should support continuous integration:

- Fast unit tests run on every commit
- Integration tests run on PR
- Full test suite runs before merge
- Performance tests run nightly
- Manual tests documented and run before release

---

[← Testing Standards](TESTING_STANDARDS.md) | [Back to Maintenance](README.md)