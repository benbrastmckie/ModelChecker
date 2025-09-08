# Test Organization Standards

[← Testing Standards](TESTING_STANDARDS.md) | [Back to Maintenance](README.md) | [Code Standards →](CODE_STANDARDS.md)

## Overview

This document defines test organization standards for the ModelChecker codebase, establishing clear patterns for test structure, categorization, and maintenance based on lessons learned from the builder test suite quality analysis.

**Core Organizational Principles:**
- **Clear Test Type Separation**: Unit, integration, and e2e tests in distinct directories
- **Centralized Test Data**: Shared fixtures prevent duplication and ensure consistency
- **Logical Component Grouping**: Related tests organized by functional boundaries
- **Comprehensive Documentation**: Every test suite has clear navigation and purpose documentation

---

## 1. Directory Structure Standards

### 1.1 Modern Test Architecture

**Recommended Structure** (replacing legacy flat organization):
```
package_name/
└── tests/
    ├── unit/                    # Pure unit tests - single component focus
    │   ├── test_component1.py   # Individual component unit tests
    │   ├── test_component2.py
    │   ├── test_utilities.py    # Utility function tests
    │   └── test_validation.py   # Validation logic tests
    │
    ├── integration/             # Component interaction tests
    │   ├── test_workflow.py     # Multi-component workflows
    │   ├── test_cross_component.py # Component integration
    │   ├── test_error_propagation.py # Cross-component error handling
    │   └── test_data_flow.py    # Data flow between components
    │
    ├── e2e/                     # Full pipeline/system tests
    │   ├── test_cli_execution.py # Complete command-line workflows
    │   ├── test_user_scenarios.py # End-to-end user scenarios
    │   └── test_performance.py  # System-wide performance (optional)
    │
    ├── fixtures/                # Centralized test data and utilities
    │   ├── __init__.py          # Export commonly used fixtures
    │   ├── test_data.py         # Shared constants and test data
    │   ├── mock_objects.py      # Standardized mock object factories
    │   ├── temp_resources.py    # Resource management utilities
    │   └── assertions.py        # Custom assertion helpers
    │
    ├── utils/                   # Test utility functions
    │   ├── __init__.py
    │   ├── file_helpers.py      # File/directory test utilities
    │   └── validation_helpers.py # Test validation utilities
    │
    ├── conftest.py              # Pytest configuration and shared fixtures
    └── README.md                # Comprehensive test suite documentation
```

### 1.2 Theory Library Structure

**For Theory Packages** (now following builder pattern):
```
theory_name/
└── tests/
    ├── unit/                   # Core theory logic tests
    │   ├── test_semantic.py    # Semantic functionality
    │   ├── test_operators.py   # Operator validation
    │   └── test_proposition.py # Proposition handling
    ├── integration/            # Theory integration tests
    │   ├── test_examples.py    # Example verification
    │   ├── test_iterate.py     # Model iteration
    │   └── test_injection.py   # Constraint injection
    ├── e2e/                    # Complete workflows
    │   └── test_cli_execution.py # CLI testing
    ├── fixtures/               # Theory-specific test data
    ├── utils/                  # Theory test utilities
    ├── conftest.py            # Pytest configuration
    └── README.md              # Test documentation
```

### 1.3 Test Migration Complete

**Previous State**: 17 packages with flat test structures
**Current State**: All packages following builder pattern with unit/integration/e2e separation

**Completed Migration:**
- ✅ iterate/tests/ - 17 tests organized (unit: 7, integration: 9, e2e: 1)
- ✅ output/tests/ - 21 tests organized (unit: 9, integration: 10, e2e: 1)
- ✅ models/tests/ - 8 tests organized (unit: 5, integration: 3)
- ✅ syntactic/tests/ - 5 tests organized (unit: 4, integration: 1)
- ✅ utils/tests/ - 4 tests organized (unit: 4)
- ✅ settings/tests/ - 2 tests organized (unit: 1, integration: 1)
- ✅ All theory tests following builder pattern
- ✅ Code/tests/ reorganized for system-level tests only
3. **Consolidate Related Tests**: Combine tests that belong together
4. **Remove Redundancy**: Eliminate duplicate coverage

---

## 2. Test File Organization

### 2.1 File Naming Conventions

**Unit Tests**: `test_[component].py`
- Examples: `test_loader.py`, `test_runner.py`, `test_translation.py`
- Focus: Single component behavior

**Integration Tests**: `test_[workflow_or_interaction].py`  
- Examples: `test_workflow.py`, `test_build_module_integration.py`
- Focus: Component interactions and data flow

**End-to-End Tests**: `test_[user_scenario].py`
- Examples: `test_cli_execution.py`, `test_project_generation.py`
- Focus: Complete user workflows

**Specialized Tests**: `test_[category]_[component].py`
- Examples: `test_edge_cases_serialization.py`, `test_performance_comparison.py`
- Focus: Specific testing concerns

### 2.2 File Structure Template

```python
"""
Test [component/workflow] functionality.

This module tests [specific scope] ensuring [key behaviors].
Tests are organized into [categories] covering [coverage areas].
"""

import unittest
import tempfile
import os
from unittest.mock import Mock, patch

# Standard library imports first
from typing import Any, Dict, List, Optional

# Third-party imports
import pytest

# Local imports - fixtures first
from fixtures.test_data import TestTheories, TestExamples, TestModules
from fixtures.mock_objects import MockObjectFactory
from fixtures.assertions import assert_valid_theory_structure
from fixtures.temp_resources import TempFileCleanup

# Component imports
from package.component import ComponentClass


class TestComponentCore(unittest.TestCase):
    """Test core [component] functionality."""
    
    def setUp(self):
        """Set up test fixtures."""
        self.component = ComponentClass()
        self.test_data = TestTheories.MINIMAL
    
    def test_component_method_with_valid_input_succeeds(self):
        """Test [component].method succeeds with valid input.
        
        This verifies the primary success path for the component's
        main functionality under normal conditions.
        """
        # Arrange
        input_data = TestExamples.SIMPLE_VALID
        expected_result = "expected_output"
        
        # Act  
        result = self.component.method(input_data)
        
        # Assert
        self.assertEqual(result, expected_result,
                        f"Component should process valid input successfully, "
                        f"expected {expected_result}, got {result}")
    
    def test_component_method_raises_error_with_invalid_input(self):
        """Test [component].method raises appropriate error with invalid input.
        
        This ensures proper error handling and user feedback when
        invalid data is provided to the component.
        """
        # Arrange
        invalid_input = TestExamples.INVALID_SETTINGS
        
        # Act & Assert
        with self.assertRaises(ValueError) as context:
            self.component.method(invalid_input)
        
        error_msg = str(context.exception).lower()
        self.assertIn("invalid", error_msg,
                      "Error message should indicate invalid input")
        self.assertIn("settings", error_msg,
                      "Error message should specify problematic settings")


class TestComponentEdgeCases(unittest.TestCase):
    """Test [component] edge cases and boundary conditions."""
    
    def setUp(self):
        """Set up edge case testing environment."""
        self.component = ComponentClass()
        self.cleanup = TempFileCleanup()
        self.addCleanup(self.cleanup.__exit__, None, None, None)
    
    def test_component_handles_empty_input_gracefully(self):
        """Test [component] handles empty input without crashing."""
        # Test with various empty input types
        empty_inputs = [[], {}, None, ""]
        
        for empty_input in empty_inputs:
            with self.subTest(input_type=type(empty_input).__name__):
                # Should either handle gracefully or raise informative error
                try:
                    result = self.component.method(empty_input)
                    self.assertIsNotNone(result,
                                       f"Should handle {type(empty_input).__name__} input")
                except ValueError as e:
                    self.assertIn("empty", str(e).lower(),
                                f"Should provide clear error for empty {type(empty_input).__name__}")


class TestComponentIntegration(unittest.TestCase):
    """Test [component] integration with other components."""
    
    def setUp(self):
        """Set up integration testing environment."""
        self.component1 = ComponentClass()
        self.component2 = RelatedComponent()
        self.test_data = TestModules.MINIMAL_CONTENT
    
    def test_components_work_together_in_workflow(self):
        """Test components integrate properly in complete workflow."""
        # Arrange
        workflow_data = TestExamples.WORKFLOW_DATA
        
        # Act - Test real component interaction
        intermediate_result = self.component1.process(workflow_data)
        final_result = self.component2.finalize(intermediate_result)
        
        # Assert
        self.assertIsNotNone(final_result,
                           "Workflow should complete successfully")
        self.assertEqual(final_result.status, "success",
                        "Integrated workflow should succeed")


if __name__ == '__main__':
    unittest.main()
```

---

## 3. Centralized Test Data Management

### 3.1 Fixtures Directory Structure

```
fixtures/
├── __init__.py                  # Export commonly used fixtures
├── test_data.py                 # All test constants and data structures
├── mock_objects.py              # Standardized mock object factories  
├── temp_resources.py            # Resource management and cleanup
└── assertions.py                # Custom assertion helpers
```

### 3.2 Test Data Organization

```python
# fixtures/test_data.py
"""
Centralized test data for consistent testing across entire test suite.

This module provides standardized test data, preventing duplication
and ensuring consistency across all test files.
"""

class TestTheories:
    """Standard theory configurations for testing."""
    
    MINIMAL = {
        "semantics": "MockSemantics",
        "proposition": "MockProposition", 
        "model": "MockModel",
        "operators": {},
        "dictionary": {}
    }
    
    WITH_OPERATORS = {
        "semantics": "MockSemantics",
        "proposition": "MockProposition",
        "model": "MockModel",
        "operators": {
            "\\neg": "MockNegation",
            "\\wedge": "MockConjunction"
        },
        "dictionary": {"&": "∧", "!": "¬"}
    }
    
    COMPLEX = {
        "semantics": "MockSemantics", 
        "proposition": "MockProposition",
        "model": "MockModel",
        "operators": {
            "\\neg": "MockNegation",
            "\\wedge": "MockConjunction",
            "\\vee": "MockDisjunction",
            "\\Box": "MockNecessity"
        },
        "dictionary": {"&": "∧", "|": "∨", "[]": "□"},
        "settings": {"N": 3, "modal": True}
    }

class TestExamples:
    """Standard example cases for testing."""
    
    SIMPLE_VALID = [["A"], ["B"], {"N": 2}]
    EMPTY_PREMISES = [[], ["A"], {"N": 2}]
    EMPTY_CONCLUSIONS = [["A"], [], {"N": 2}]
    MODAL_EXAMPLE = [["□A"], ["A"], {"N": 2}]
    INVALID_SETTINGS = [["A"], ["B"], {"N": -1}]
    
    # Workflow-specific data
    WORKFLOW_DATA = {
        "input": TestExamples.SIMPLE_VALID,
        "expected_stages": ["load", "process", "output"],
        "expected_output_format": "models"
    }

class TestModules:
    """Standard module content for file-based testing."""
    
    MINIMAL_CONTENT = '''
from model_checker.theory_lib.logos import get_theory

theory = get_theory(['extensional'])
semantic_theories = {"Test": theory}
example_range = {"TEST": [[], ["A"], {"N": 2}]}
general_settings = {}
'''
    
    WITH_EXAMPLES = '''
from model_checker.theory_lib.logos import get_theory

theory = get_theory(['extensional'])
semantic_theories = {"Test": theory}
example_range = {
    "SIMPLE": [["A"], ["B"], {"N": 2}],
    "MODAL": [["□A"], ["A"], {"N": 2}],
    "EMPTY": [[], ["A"], {"N": 2}]
}
general_settings = {"print_impossible": False}
'''
    
    SYNTAX_ERROR_CONTENT = '''
this is not valid python syntax !
semantic_theories = undefined_variable
'''
    
    IMPORT_ERROR_CONTENT = '''
from nonexistent_package import something
semantic_theories = {}
example_range = {}
'''

class TestFlags:
    """Standard flag configurations for testing."""
    
    @staticmethod
    def create_minimal(**overrides):
        """Create minimal flags with optional overrides."""
        defaults = {
            "file_path": "/tmp/test.py",
            "comparison": False, 
            "interactive": False,
            "iterations": False,
            "quiet": False
        }
        defaults.update(overrides)
        return Mock(**defaults)
    
    @staticmethod  
    def create_with_comparison(**overrides):
        """Create flags with comparison enabled."""
        return TestFlags.create_minimal(comparison=True, **overrides)
    
    @staticmethod
    def create_interactive(**overrides):
        """Create flags with interactive mode enabled."""  
        return TestFlags.create_minimal(interactive=True, **overrides)
```

### 3.3 Mock Object Factories

```python
# fixtures/mock_objects.py
"""
Standardized mock object factories for consistent testing.

Provides factory functions for creating properly configured mock objects
with reasonable defaults and customization options.
"""

from unittest.mock import Mock, MagicMock
from typing import Any, Dict, Optional

class MockObjectFactory:
    """Factory for creating standardized mock objects."""
    
    @staticmethod
    def create_build_module(components: Optional[Dict[str, Any]] = None) -> Mock:
        """Create BuildModule mock with specified components."""
        mock = Mock()
        mock.general_settings = {}
        mock.output_manager = Mock()
        mock.output_manager.should_save.return_value = False
        mock.interactive_manager = None
        
        # Add component mocks
        if components:
            for component_name, component_mock in components.items():
                setattr(mock, component_name, component_mock)
        else:
            # Default minimal components
            mock.loader = Mock()
            mock.runner = Mock()
            mock.comparison = Mock()
            mock.translation = Mock()
        
        return mock
    
    @staticmethod
    def create_theory_dict(theory_type: str = "minimal") -> Dict[str, Any]:
        """Create theory dictionary based on type."""
        if theory_type == "minimal":
            return TestTheories.MINIMAL.copy()
        elif theory_type == "with_operators":
            return TestTheories.WITH_OPERATORS.copy()
        elif theory_type == "complex":
            return TestTheories.COMPLEX.copy()
        else:
            raise ValueError(f"Unknown theory type: {theory_type}")
    
    @staticmethod
    def create_runner(build_module: Optional[Mock] = None) -> Mock:
        """Create ModelRunner mock with build_module reference."""
        runner = Mock()
        runner.build_module = build_module or MockObjectFactory.create_build_module()
        runner.run_model_check.return_value = Mock(status="success")
        runner.run_examples.return_value = []
        return runner
    
    @staticmethod
    def create_comparison(build_module: Optional[Mock] = None) -> Mock:
        """Create ModelComparison mock with build_module reference."""
        comparison = Mock()
        comparison.build_module = build_module or MockObjectFactory.create_build_module()
        comparison.compare_semantics.return_value = []
        comparison.run_comparison.return_value = Mock(status="success")
        return comparison
```

---

## 4. Test Categories and Standards

### 4.1 Unit Test Organization

**Purpose**: Test individual components in isolation
**Location**: `tests/unit/`
**Standards**:
- One test file per major component
- Mock external dependencies only
- Fast execution (<50ms per test)
- Comprehensive coverage of public methods

**Example Organization**:
```python
# tests/unit/test_loader.py
class TestModuleLoaderCore(unittest.TestCase):
    """Test ModuleLoader core functionality."""

class TestModuleLoaderErrorHandling(unittest.TestCase):
    """Test ModuleLoader error conditions."""

class TestModuleLoaderEdgeCases(unittest.TestCase):
    """Test ModuleLoader boundary conditions."""
```

### 4.2 Integration Test Organization

**Purpose**: Test component interactions and workflows
**Location**: `tests/integration/`
**Standards**:
- Test real component instances together
- Minimal mocking (external systems only)
- Moderate execution time (<500ms per test)
- Focus on component boundaries and data flow

**Example Organization**:
```python
# tests/integration/test_build_module_workflow.py
class TestBuildModuleInitialization(unittest.TestCase):
    """Test BuildModule component initialization and setup."""

class TestBuildModuleWorkflow(unittest.TestCase):
    """Test complete BuildModule workflows."""

class TestBuildModuleErrorPropagation(unittest.TestCase):
    """Test error handling across BuildModule components."""
```

### 4.3 End-to-End Test Organization

**Purpose**: Test complete user workflows
**Location**: `tests/e2e/`
**Standards**:
- Minimal to no mocking
- Real file operations and external interactions
- Slower execution (<5 seconds per test)
- Cover major user scenarios

**Example Organization**:
```python
# tests/e2e/test_cli_execution.py
class TestCLIBasicExecution(unittest.TestCase):
    """Test basic CLI execution workflows."""

class TestCLIInteractiveMode(unittest.TestCase):
    """Test CLI interactive mode workflows."""

class TestCLIErrorScenarios(unittest.TestCase):
    """Test CLI error handling and recovery."""
```

---

## 5. Test Documentation Standards

### 5.1 Test Suite README Requirements

**Every test directory MUST have a comprehensive README.md:**

```markdown
# [Component] Test Suite

## Overview
Brief description of what this test suite covers and its scope.

## Test Structure
```
tests/
├── unit/                  # Component isolation tests (X tests)
│   ├── test_component1.py # Component1 unit tests (Y tests)
│   └── test_component2.py # Component2 unit tests (Z tests)
├── integration/          # Component interaction tests (A tests)
│   ├── test_workflow.py  # Workflow integration tests (B tests)  
│   └── test_errors.py    # Error propagation tests (C tests)
├── e2e/                 # Full workflow tests (D tests)
│   └── test_cli.py      # CLI execution tests (E tests)
└── fixtures/            # Shared test data and utilities
    ├── test_data.py     # Centralized test constants
    ├── mock_objects.py  # Mock object factories
    └── assertions.py    # Custom assertion helpers
```

## Test Categories

### Unit Tests (X tests)
- **Purpose**: Test individual components in isolation
- **Coverage**: >90% line coverage for core components
- **Execution**: <2 seconds total

### Integration Tests (A tests)  
- **Purpose**: Test component interactions and workflows
- **Coverage**: All component boundaries and major workflows
- **Execution**: <10 seconds total

### End-to-End Tests (D tests)
- **Purpose**: Test complete user workflows
- **Coverage**: All major user scenarios
- **Execution**: <30 seconds total

## Running Tests

```bash
# Run all tests
pytest tests/

# Run specific test category
pytest tests/unit/         # Fast unit tests only
pytest tests/integration/  # Integration tests only  
pytest tests/e2e/          # End-to-end tests only

# Run with coverage
pytest --cov=package_name --cov-report=html tests/

# Run specific test file
pytest tests/unit/test_component1.py

# Run single test method
pytest tests/unit/test_component1.py::TestComponent::test_method
```

## Test Data and Fixtures

### Centralized Test Data
All test data is centralized in `fixtures/test_data.py` to ensure consistency and prevent duplication.

### Mock Objects
Standardized mock objects are created using factories in `fixtures/mock_objects.py`.

### Resource Management
Temporary files and resources are managed using utilities in `fixtures/temp_resources.py`.

## Adding New Tests

### For New Components
1. Create unit tests in `tests/unit/test_[component].py`
2. Add integration tests to appropriate workflow test file
3. Update test counts in this README
4. Add test data to `fixtures/test_data.py` if needed

### For New Features
1. Add unit tests for new functionality
2. Add integration tests if feature crosses components
3. Add end-to-end tests if feature affects user workflows
4. Update documentation

## Maintenance

### Coverage Requirements
- Unit tests: >90% line coverage
- Integration tests: >80% line coverage
- Overall: >85% line coverage

### Performance Targets
- Unit tests: <50ms per test, <2s total
- Integration tests: <500ms per test, <10s total  
- End-to-end tests: <5s per test, <30s total

### Quality Standards
- All tests have descriptive names and documentation
- All assertions include descriptive error messages
- Tests follow centralized fixture patterns
- No excessive mocking in unit tests
```

### 5.2 Test Method Documentation Standards

**Every test method MUST have:**
- Descriptive name following `test_[component]_[action]_[condition]_[expected]` pattern
- Comprehensive docstring explaining what is tested and why
- Clear Arrange-Act-Assert structure
- Descriptive assertion messages

---

## 6. Migration and Maintenance Guidelines

### 6.1 Legacy Test Refactoring

**Assessment Phase:**
1. **Categorize Existing Tests**: Determine if each test is unit/integration/e2e
2. **Identify Common Data**: Find duplicated test data and fixture patterns
3. **Assess Mock Usage**: Identify excessive or inappropriate mocking
4. **Check Documentation**: Evaluate test naming and documentation quality

**Refactoring Phase:**
1. **Create Directory Structure**: Set up unit/integration/e2e directories
2. **Centralize Test Data**: Extract common data to fixtures/test_data.py
3. **Consolidate Related Tests**: Combine tests that belong together logically
4. **Improve Documentation**: Add missing docstrings and improve naming
5. **Reduce Redundancy**: Remove or combine duplicate test coverage

**Validation Phase:**
1. **Verify Coverage**: Ensure no loss of test coverage during refactoring
2. **Check Performance**: Validate test execution performance
3. **Review Quality**: Ensure all tests follow updated standards
4. **Update Documentation**: Create comprehensive README for test suite

### 6.2 New Test Development

**All new tests MUST:**
- Follow directory structure standards (unit/integration/e2e)
- Use centralized test data from fixtures
- Have descriptive names and comprehensive documentation
- Include appropriate level of mocking for test type
- Meet performance targets for test category
- Follow assertion standards with descriptive error messages

---

## 7. Continuous Integration Integration

### 7.1 Test Execution Strategy

**Development Workflow:**
```bash
# Fast feedback - unit tests only
pytest tests/unit/ --maxfail=3

# Pre-commit - unit + integration
pytest tests/unit/ tests/integration/ --maxfail=1

# Pre-merge - full suite
pytest tests/ --cov=package --cov-fail-under=85
```

**CI/CD Pipeline:**
- **Commit**: Unit tests only (fast feedback)
- **Pull Request**: Unit + Integration tests
- **Merge**: Full test suite with coverage requirements
- **Release**: Full suite + performance validation + manual testing

### 7.2 Test Reporting

**Required Metrics:**
- Pass/fail status by test category
- Code coverage by component and overall
- Test execution performance trends
- Failed test details with clear error messages

---

## 8. Quality Metrics and Success Criteria

### 8.1 Organizational Quality Metrics

**Test Structure:**
- ✅ Clear separation of unit/integration/e2e tests
- ✅ Centralized test data with no duplication
- ✅ Consistent naming and documentation patterns
- ✅ Appropriate mocking levels for each test type

**Test Maintainability:**
- ✅ New developers can understand test organization within 30 minutes
- ✅ Adding new tests follows clear, documented patterns
- ✅ Test failures provide obvious diagnosis and fix guidance
- ✅ Refactoring components requires minimal test changes

### 8.2 Performance Metrics

**Execution Performance:**
- Unit tests: <2 seconds total
- Integration tests: <10 seconds total  
- End-to-end tests: <30 seconds total
- Full test suite: <45 seconds total

**Development Efficiency:**
- Test writing follows standard patterns (no custom setup needed)
- Test debugging is straightforward with clear error messages
- Test maintenance overhead is minimal

---

## Conclusion

These test organization standards establish a clear, maintainable structure that supports long-term codebase evolution. By following these guidelines, teams can:

- **Quickly locate and understand relevant tests**
- **Add new tests following consistent, documented patterns**  
- **Maintain tests efficiently with minimal overhead**
- **Execute tests at appropriate granularity for different scenarios**

**Key Success Factors:**
- Clear separation of test types with appropriate boundaries
- Centralized test data management prevents duplication
- Comprehensive documentation supports team collaboration  
- Performance targets ensure fast feedback cycles

The organized structure supports both automated CI/CD workflows and manual development processes, providing reliable test feedback while maintaining development velocity.

---

**Document Status**: Updated to complement TESTING_STANDARDS.md refactor  
**Implementation**: Required for new test suites, recommended for legacy refactoring  
**Next Review**: After completing builder test suite comprehensive refactor

---

[← Testing Standards](TESTING_STANDARDS.md) | [Back to Maintenance](README.md) | [Code Standards →](CODE_STANDARDS.md)