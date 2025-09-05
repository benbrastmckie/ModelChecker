# Builder Test Suite Improvements

## Files to Remove (Cruft)

1. **migrate_tests.py** - One-time migration script, no longer needed
2. **test_refactor_baseline.py** - Temporary validation for refactoring, now redundant
3. **baseline/*.txt** - Verify usage and remove if outdated

## Systematic Improvements

### 1. Test Organization

#### Current Issues:
- Some test files are very large (test_module.py has 463 lines)
- Mixed concerns in single test files
- Duplicate test patterns across files

#### Proposed Structure:
```
tests/
├── unit/                      # Pure unit tests
│   ├── test_loader.py
│   ├── test_runner.py
│   ├── test_comparison.py
│   ├── test_translation.py
│   ├── test_serialization.py
│   └── test_validation.py
├── integration/               # Integration tests
│   ├── test_module_workflow.py
│   ├── test_cli_integration.py
│   ├── test_project_generation.py
│   └── test_interactive_mode.py
├── fixtures/                  # Test data and mocks
│   ├── __init__.py
│   ├── mock_modules.py
│   ├── test_data.py
│   └── builders.py
└── conftest.py               # Pytest configuration

```

### 2. Test Consolidation

#### Merge Related Tests:
- **test_runner_extraction.py** + **test_comparison_extraction.py** + **test_translation_extraction.py** 
  → **test_components.py** (they all test component extraction)

- **test_build_module_interactive.py** + **test_cli_interactive_integration.py**
  → **test_interactive_mode.py** (both test interactive features)

- **test_edge_cases.py** + **test_generated_projects.py** + **test_integration_workflow.py**
  → Split into focused integration tests

### 3. Fixture Improvements

Create a centralized fixture system:

```python
# conftest.py
import pytest
from pathlib import Path
from unittest.mock import Mock

@pytest.fixture
def mock_flags():
    """Standard mock flags for testing."""
    return Mock(spec=['file_path', 'print_constraints', 'print_z3', 'save_output'])

@pytest.fixture
def temp_module(tmp_path):
    """Create a temporary test module."""
    module_path = tmp_path / "test_module.py"
    module_path.write_text('''
from model_checker.theory_lib import logos

semantic_theories = {"Test": logos.get_theory(['extensional'])}
example_range = {"TEST": [[], ["A"], {"N": 2}]}
general_settings = {}
''')
    return str(module_path)

@pytest.fixture
def build_module(mock_flags, temp_module):
    """Create a BuildModule instance for testing."""
    mock_flags.file_path = temp_module
    return BuildModule(mock_flags)
```

### 4. Test Patterns

Standardize test patterns across the suite:

```python
# Standard test class structure
class TestComponent:
    """Test {Component} functionality."""
    
    def test_initialization(self, build_module):
        """Test component is properly initialized."""
        assert hasattr(build_module, 'component')
        assert isinstance(build_module.component, ExpectedClass)
    
    def test_core_functionality(self, build_module):
        """Test main component function."""
        result = build_module.component.method()
        assert result == expected
    
    def test_error_handling(self, build_module):
        """Test component handles errors gracefully."""
        with pytest.raises(ExpectedError):
            build_module.component.method(invalid_input)
```

### 5. Remove Test Duplication

Many tests check the same functionality:
- Module initialization is tested in multiple files
- Component delegation is tested redundantly
- Mock creation is duplicated

Create shared test mixins:

```python
# test_mixins.py
class ComponentTestMixin:
    """Mixin for testing component initialization and delegation."""
    
    component_name = None  # Override in subclass
    expected_methods = []  # Override in subclass
    
    def test_component_exists(self, build_module):
        assert hasattr(build_module, self.component_name)
    
    def test_component_methods(self, build_module):
        component = getattr(build_module, self.component_name)
        for method in self.expected_methods:
            assert hasattr(component, method)
```

### 6. Performance Improvements

- Use pytest's parametrize instead of loops in tests
- Share expensive fixtures using scope='session'
- Use pytest-xdist for parallel test execution

### 7. Documentation

Update tests/README.md to:
- Remove references to deleted files
- Add testing best practices section
- Include examples of new fixture usage
- Document the improved structure

### 8. Mock Improvements

Create a mock builder factory:

```python
# fixtures/builders.py
class MockBuilder:
    """Factory for creating configured mock objects."""
    
    @staticmethod
    def flags(**kwargs):
        """Create mock flags with sensible defaults."""
        defaults = {
            'file_path': '/tmp/test.py',
            'print_constraints': False,
            'print_z3': False,
            'save_output': False
        }
        defaults.update(kwargs)
        return Mock(spec=list(defaults.keys()), **defaults)
    
    @staticmethod
    def module(theory='logos', has_examples=True):
        """Create a mock module with theory."""
        # Implementation
```

## Implementation Priority

1. **High Priority** (Do immediately):
   - Remove cruft files (migrate_tests.py, test_refactor_baseline.py)
   - Update tests/README.md
   - Fix Mock objects to use proper spec

2. **Medium Priority** (Next sprint):
   - Consolidate related test files
   - Create shared fixtures in conftest.py
   - Standardize test patterns

3. **Low Priority** (Future improvement):
   - Reorganize into unit/integration structure
   - Add performance optimizations
   - Create comprehensive mock builders

## Benefits

- **Reduced Maintenance**: Less duplicate code to update
- **Faster Tests**: Shared fixtures and parallel execution
- **Better Coverage**: Clearer structure reveals gaps
- **Easier Onboarding**: Consistent patterns and organization
- **Less Cruft**: Regular cleanup prevents accumulation