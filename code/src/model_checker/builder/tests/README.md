# Builder Package Tests

[← Back to Builder](../README.md) | [Test Standards →](../../../../maintenance/TESTING_STANDARDS.md)

## Overview

Comprehensive test suite for the ModelChecker builder package, ensuring reliability and maintainability of the build system through systematic unit, integration, and manual testing protocols.

## Test Suite Structure

```
tests/
├── README.md                               # This file - test suite documentation
├── __init__.py                             # Test package initialization
├── conftest.py                             # Pytest configuration and shared fixtures
├── improvements.md                         # Test improvement suggestions
│
├── unit/                                   # Component isolation tests (102 tests)
│   ├── test_comparison.py                  # ModelComparison component (15 tests)
│   ├── test_example.py                     # BuildExample component (15 tests)
│   ├── test_helpers.py                     # Helper functions (8 tests)
│   ├── test_loader.py                      # ModuleLoader component (12 tests)
│   ├── test_progress.py                    # Progress tracking (5 tests)
│   ├── test_project.py                     # BuildProject component (10 tests)
│   ├── test_project_version.py             # Project version detection (6 tests)
│   ├── test_runner.py                      # ModelRunner component (7 tests)
│   ├── test_serialize.py                   # Serialization utilities (8 tests)
│   ├── test_translation.py                 # OperatorTranslation (4 tests)
│   ├── test_validation.py                  # Input validation logic (5 tests)
│   ├── test_z3_isolation.py                # Z3 context isolation (3 tests)
│   └── test_z3_utils.py                    # Z3 utility functions (4 tests)
│
├── integration/                            # Component interaction tests (96 tests)
│   ├── test_build_module_theories.py       # Theory loading integration (15 tests)
│   ├── test_cli_interactive_integration.py # CLI interactive mode (10 tests)
│   ├── test_component_integration.py       # Cross-component workflows (20 tests)
│   ├── test_error_propagation.py           # Error handling flow (15 tests)
│   ├── test_generated_projects.py          # Generated project structure (8 tests)
│   ├── test_interactive.py                 # Interactive save features (7 tests)
│   ├── test_output_directory_guidance.py   # Output directory handling (5 tests)
│   ├── test_performance.py                 # Performance tests (11 tests)
│   └── test_workflow.py                    # Complete workflows (5 tests)
│
├── e2e/                                    # End-to-end tests (17 tests)
│   ├── test_full_pipeline.py               # Complete execution pipeline (12 tests)
│   └── test_project_edge_cases.py          # Project generation edge cases (5 tests)
│
├── fixtures/                              # Centralized test data and utilities
│   ├── __init__.py                        # Export commonly used fixtures
│   ├── assertions.py                      # Custom assertion helpers
│   ├── mock_objects.py                    # Standardized mock factories
│   ├── temp_resources.py                  # Temporary resource management
│   └── test_data.py                       # Shared test constants
│
└── utils/                                 # Test utility functions
    ├── __init__.py
    ├── cleanup.py                         # Test environment cleanup
    ├── file_helpers.py                    # File operation utilities
    └── validation_helpers.py              # Validation test helpers
```

**Total**: 215 tests across 24 test files

## Test Categories

### 1. Unit Tests
**Purpose**: Test individual components in isolation  
**Coverage Goal**: 100% of public methods  
**Key Files**:
- `test_module.py` - BuildModule core functionality
- `test_loader.py` - Module loading and discovery
- `test_serialize.py` - Data serialization integrity

**Example Structure**:
```python
class TestModuleLoader(unittest.TestCase):
    """Test module loading functionality."""
    
    def setUp(self):
        """Set up test fixtures."""
        self.loader = ModuleLoader("test_module", "/test/path")
    
    def test_load_module_success(self):
        """Test successful module loading."""
        # Uses descriptive assertions per TESTING_STANDARDS.md
```

### 2. Integration Tests
**Purpose**: Verify component interactions  
**Coverage Goal**: All critical workflows  
**Key Files**:
- `test_components.py` - Component delegation and interaction
- `test_full_pipeline.py` - Complete execution without mocks
- `test_error_propagation.py` - Cross-component error handling

### 3. Interactive/CLI Tests
**Purpose**: Test user-facing interfaces  
**Coverage Goal**: All user interaction paths  
**Key Files**:
- `test_build_module_interactive.py` - Interactive prompts and flows
- `test_cli_interactive_integration.py` - Command-line integration

### 4. Manual Testing
**Purpose**: Catch integration issues mocks miss  
**Protocol**: See [MANUAL_TESTING.md](../../../../maintenance/MANUAL_TESTING.md)  
**Required**: Before all PR merges

## Running Tests

### Quick Start
```bash
# Run all builder tests
./run_tests.py --package builder

# Run with coverage
pytest --cov=model_checker.builder src/model_checker/builder/tests/

# Run specific test category
pytest src/model_checker/builder/tests/test_components.py -v
```

### Development Workflow
```bash
# 1. Run unit tests during development
pytest src/model_checker/builder/tests/test_module.py -x

# 2. Run integration tests before commit
pytest src/model_checker/builder/tests/test_*integration*.py

# 3. Run manual tests before PR
./dev_cli.py src/model_checker/theory_lib/logos/examples.py
```

### Continuous Integration
```bash
# Full test suite with coverage requirements
pytest --cov=model_checker.builder \
       --cov-fail-under=80 \
       --cov-report=term-missing \
       src/model_checker/builder/tests/
```

## Coverage Requirements

Per [TESTING_STANDARDS.md](../../../../maintenance/TESTING_STANDARDS.md):

| Component | Requirement | Current | Status |
|-----------|------------|---------|---------|
| Semantic Modules | ≥80% | 85% | ✅ |
| Operator Definitions | 100% | 100% | ✅ |
| Core Components | ≥90% | 92% | ✅ |
| Edge Cases | Full Coverage | 78% | ⚠️ |

### Coverage Commands
```bash
# Generate HTML coverage report
pytest --cov=model_checker.builder --cov-report=html

# Check specific module coverage
pytest --cov=model_checker.builder.loader test_loader.py

# Identify missing coverage
pytest --cov-report=term-missing
```

## Test Writing Standards

### 1. File Organization
```python
"""Test module docstring explaining purpose."""
import unittest
from unittest.mock import Mock, patch
from model_checker.builder.component import Component

# Test fixtures at module level
VALID_CONFIGS = [...]
INVALID_CONFIGS = [...]

class TestComponent(unittest.TestCase):
    """Test class with clear purpose."""
    
    def setUp(self):
        """Standard fixture setup."""
        self.component = Component()
```

### 2. Test Method Standards
```python
def test_specific_behavior_with_context(self):
    """Test that [behavior] when [condition].
    
    Validates [specific requirement or edge case].
    """
    # Arrange - Set up test data
    input_data = {"key": "value"}
    expected = "result"
    
    # Act - Execute the behavior
    result = self.component.process(input_data)
    
    # Assert - Verify with descriptive message
    self.assertEqual(
        result, expected,
        f"Processing {input_data} should return {expected}, got {result}"
    )
```

### 3. Mock Usage Guidelines
```python
@patch('module.external_dependency')
def test_with_mock(self, mock_dep):
    """Test behavior with mocked dependency."""
    # Configure mock
    mock_dep.return_value = "mocked_result"
    
    # Test interaction
    result = self.component.method_using_dep()
    
    # Verify mock called correctly
    mock_dep.assert_called_once_with(expected_args)
```

### 4. Parameterized Testing
```python
@pytest.mark.parametrize("input,expected", [
    ("valid", True),
    ("", False),
    (None, False),
])
def test_validation_cases(self, input, expected):
    """Test validation with various inputs."""
    assert self.validator.is_valid(input) == expected
```

## Common Testing Patterns

### Error Testing
```python
def test_error_handling(self):
    """Test appropriate error raised with context."""
    with self.assertRaises(ValueError) as context:
        self.component.process_invalid(bad_data)
    
    self.assertIn("specific error message", str(context.exception))
```

### Fixture Reuse
```python
# In fixtures.py
def create_test_module(theory_name="test", **kwargs):
    """Create a test module with standard configuration."""
    flags = Mock(
        file_path=f"/tmp/{theory_name}.py",
        print_constraints=False,
        **kwargs
    )
    return BuildModule(flags)

# In test file
from .fixtures import create_test_module

def test_with_fixture(self):
    module = create_test_module(print_constraints=True)
    # Test with configured module
```

## Maintenance Guidelines

### Adding New Tests
1. **Choose appropriate category** - Unit, Integration, or Interactive
2. **Follow naming convention** - `test_[component]_[behavior].py`
3. **Use standard structure** - setUp, descriptive test names, AAA pattern
4. **Update this README** - Add to file tree and category description
5. **Verify coverage** - Ensure new code is tested

### Debugging Test Failures
1. **Run specific test** - `pytest path/to/test.py::TestClass::test_method -v`
2. **Check recent changes** - API modifications, moved methods
3. **Verify mocks** - Ensure mocks match actual interfaces
4. **Use debugging** - `pytest --pdb` for interactive debugging

### Test Refactoring
When refactoring tests:
1. **Maintain coverage** - Don't reduce test effectiveness
2. **Update documentation** - Keep README current
3. **Run full suite** - Ensure no regressions
4. **Check manual tests** - Verify integration still works

## CI/CD Integration

Tests run automatically on:
- **Pull Requests** - Must pass for merge
- **Main Branch** - Post-merge validation
- **Release Tags** - Full regression suite
- **Nightly** - Extended integration tests

### PR Checklist
- [ ] All unit tests pass
- [ ] Integration tests pass
- [ ] Coverage ≥80%
- [ ] Manual tests completed (see MANUAL_TESTING.md)
- [ ] No new test warnings

## References

- [TESTING_STANDARDS.md](../../../../maintenance/TESTING_STANDARDS.md) - Framework-wide testing standards
- [MANUAL_TESTING.md](../../../../maintenance/MANUAL_TESTING.md) - Required manual test protocol
- [CODE_STANDARDS.md](../../../../maintenance/CODE_STANDARDS.md) - Code quality guidelines
- [Builder README](../README.md) - Builder package documentation

---

[← Back to Builder](../README.md) | [Test Standards →](../../../../maintenance/TESTING_STANDARDS.md)
