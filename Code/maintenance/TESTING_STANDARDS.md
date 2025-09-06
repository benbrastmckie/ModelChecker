# Testing Standards

[← Performance](PERFORMANCE.md) | [Back to Maintenance](README.md) | [Test Organization →](TEST_ORGANIZATION.md)

## Overview

This document defines comprehensive testing standards for the ModelChecker codebase, incorporating lessons learned from the builder test suite quality analysis. These standards ensure maintainable, reliable, and efficient tests that support long-term codebase evolution.

**Key Principles:**
- **Minimal Mocking**: Use real objects wherever possible, mock only external dependencies
- **Clear Separation**: Distinct unit, integration, and end-to-end test categories
- **Descriptive Documentation**: Every test method explains what behavior is verified
- **Centralized Data**: Shared fixtures and test data prevent duplication

---

## 1. Test Architecture Standards

### 1.1 Test Directory Structure

**For Components/Packages:**
```
package_name/
└── tests/
    ├── unit/                    # Pure unit tests - single component, minimal deps
    │   ├── test_component1.py   # Individual component unit tests
    │   ├── test_component2.py
    │   └── test_utilities.py    # Utility function tests
    ├── integration/             # Component interaction tests
    │   ├── test_workflow.py     # Multi-component workflows  
    │   ├── test_cross_component.py # Component integration
    │   └── test_error_propagation.py # Error handling across components
    ├── e2e/                     # Full pipeline/system tests
    │   ├── test_cli_execution.py # Complete command-line workflows
    │   ├── test_user_scenarios.py # End-to-end user scenarios
    │   └── test_performance.py  # System-wide performance (optional)
    ├── fixtures/                # Centralized test data and utilities
    │   ├── __init__.py
    │   ├── test_data.py         # Shared constants and test data
    │   ├── mock_objects.py      # Standardized mock object factories
    │   ├── temp_resources.py    # Resource management utilities
    │   └── assertions.py        # Custom assertion helpers
    ├── utils/                   # Test utility functions
    │   ├── __init__.py
    │   ├── file_helpers.py      # File/directory test utilities
    │   └── validation_helpers.py # Test validation utilities
    ├── conftest.py              # Pytest configuration and shared fixtures
    └── README.md                # Test suite documentation
```

**For Theory Libraries:**
```
theory_name/
└── tests/
    ├── README.md               # Test documentation
    ├── __init__.py
    ├── test_semantic.py        # Core semantic functionality
    ├── test_operators.py       # Individual operator validation
    ├── test_examples.py        # Example formula verification
    ├── test_iterate.py         # Model iteration testing
    └── fixtures.py             # Theory-specific test data
```

### 1.2 Test Type Classification

#### **Unit Tests** (`tests/unit/`)
**Purpose**: Test individual components in isolation
**Characteristics:**
- Tests single class or function
- Minimal external dependencies
- Fast execution (milliseconds)
- Mock only external services (file system, network, databases)

```python
# Good unit test - tests single component
class TestModelRunner(unittest.TestCase):
    """Test ModelRunner component in isolation."""
    
    def test_run_model_check_with_valid_example(self):
        """Test ModelRunner processes valid example successfully."""
        # Use real objects for internal components
        mock_build_module = create_minimal_build_module()
        runner = ModelRunner(mock_build_module)
        
        # Only mock external dependencies like Z3
        with patch('z3.Solver') as mock_solver:
            mock_solver.return_value.check.return_value = z3.sat
            
            result = runner.run_model_check(VALID_EXAMPLE_CASE)
            
            self.assertEqual(result.status, "success")
```

#### **Integration Tests** (`tests/integration/`)
**Purpose**: Test component interactions and workflows  
**Characteristics:**
- Tests multiple components together
- Verifies component boundaries and communication
- Uses real objects for internal architecture
- Moderate execution time (seconds)

```python
# Good integration test - tests component interaction
class TestBuildModuleWorkflow(unittest.TestCase):
    """Test BuildModule component integration."""
    
    def test_complete_model_checking_workflow(self):
        """Test complete workflow from loading to result output."""
        # Use real BuildModule with all components
        flags = create_test_flags()
        build_module = BuildModule(flags)
        
        # Test real component interaction without excessive mocking
        result = build_module.runner.run_examples()
        
        self.assertIsNotNone(result)
        self.assertTrue(hasattr(build_module, 'loader'))
        self.assertTrue(hasattr(build_module, 'runner'))
```

#### **End-to-End Tests** (`tests/e2e/`)
**Purpose**: Test complete user workflows and system behavior
**Characteristics:**
- Tests full user scenarios from start to finish  
- Minimal to no mocking
- Real file operations and external interactions
- Slower execution (seconds to minutes)

```python
# Good e2e test - tests complete user workflow
class TestCLIExecution(unittest.TestCase):
    """Test complete CLI execution workflows."""
    
    def test_theory_execution_from_command_line(self):
        """Test complete theory execution via CLI."""
        # Create real test file
        with tempfile.NamedTemporaryFile(mode='w', suffix='.py', delete=False) as f:
            f.write(TEST_MODULE_CONTENT)
            test_file = f.name
        
        try:
            # Execute real CLI command
            result = subprocess.run(
                [sys.executable, 'dev_cli.py', test_file],
                capture_output=True, text=True
            )
            
            self.assertEqual(result.returncode, 0)
            self.assertIn("EXAMPLE", result.stdout)
            self.assertNotIn("Traceback", result.stderr)
        finally:
            os.unlink(test_file)
```

---

## 2. Mocking Standards

### 2.1 When to Mock

**DO Mock:**
- External services (databases, APIs, network calls)
- File system operations (when not testing file handling)  
- Time-dependent operations (`time.sleep`, `datetime.now`)
- Expensive operations (Z3 solver in unit tests)
- Non-deterministic operations (random number generation)

**DO NOT Mock:**
- Internal components being tested
- Simple data structures (dictionaries, lists)
- Pure functions without side effects  
- Components within the same module/package

### 2.2 Mock Creation Standards

```python
# GOOD - Mock external dependencies only
def test_solver_integration(self):
    """Test integration with Z3 solver."""
    runner = ModelRunner(create_test_build_module())
    
    with patch('z3.Solver') as mock_solver:
        mock_solver.return_value.check.return_value = z3.sat
        result = runner.run_model_check(test_example)
    
    self.assertEqual(result.status, "success")

# BAD - Excessive internal mocking
def test_component_interaction(self):
    """BAD: Over-mocking internal components."""
    with patch('package.Component1') as mock1, \
         patch('package.Component2') as mock2, \
         patch('package.Component3') as mock3:
        # This tests mocks, not real behavior!
        pass
```

### 2.3 Mock Object Standards

**Use Centralized Mock Factories:**
```python
# fixtures/mock_objects.py
class MockObjectFactory:
    """Centralized factory for creating standardized mock objects."""
    
    @staticmethod
    def create_minimal_build_module():
        """Create minimal BuildModule mock for unit testing."""
        mock = Mock()
        mock.general_settings = {}
        mock.translation = Mock()
        mock.output_manager = Mock()
        return mock
    
    @staticmethod
    def create_test_theory():
        """Create standard test theory object."""
        return {
            "semantics": MockSemantics,
            "proposition": MockProposition,
            "model": MockModel,
            "operators": {},
            "dictionary": {}
        }
```

---

## 3. Test Documentation Standards

### 3.1 Test Method Documentation

**Every test method MUST have a docstring that:**
- Explains what behavior is being tested
- Uses present tense ("Test that X does Y")
- Describes the expected outcome

```python
def test_module_loader_raises_import_error_when_file_not_found(self):
    """Test that ModuleLoader raises ImportError when module file does not exist.
    
    This ensures proper error handling for missing module files and helps
    users understand what went wrong during module loading.
    """
    loader = ModuleLoader("nonexistent", "/path/that/does/not/exist.py")
    
    with self.assertRaises(ImportError) as context:
        loader.load_module()
    
    self.assertIn("not found", str(context.exception).lower())
```

### 3.2 Test Method Naming

**Naming Pattern:** `test_[component]_[action]_[condition]_[expected_result]`

**Examples:**
```python
# Component behavior tests
def test_module_loader_loads_valid_theory_successfully(self):
def test_model_runner_raises_error_with_invalid_settings(self):
def test_build_module_initializes_all_components_correctly(self):

# Edge case tests  
def test_operator_translation_handles_empty_dictionary_gracefully(self):
def test_serialization_preserves_unicode_characters_correctly(self):
def test_comparison_returns_empty_list_with_no_theories(self):

# Error condition tests
def test_loader_raises_syntax_error_with_malformed_python(self):
def test_runner_propagates_z3_timeout_errors_appropriately(self):
```

### 3.3 Test Suite Documentation

**Every `tests/` directory MUST have a README.md with:**
```markdown
# Component Test Suite

## Test Structure
```
tests/
├── unit/                  # Component isolation tests
├── integration/          # Component interaction tests  
├── e2e/                 # Full workflow tests
└── fixtures/            # Shared test data
```

## Running Tests
```bash
# Run all tests
pytest tests/

# Run specific test type
pytest tests/unit/
pytest tests/integration/  
pytest tests/e2e/

# Run with coverage
pytest --cov=package_name tests/
```

## Test Categories
- **Unit Tests (45 tests)**: Individual component behavior
- **Integration Tests (23 tests)**: Component interactions
- **E2E Tests (8 tests)**: Complete user workflows

## Coverage Requirements
- Unit Tests: >90% line coverage
- Integration Tests: Cover all component boundaries
- E2E Tests: Cover all major user scenarios
```

---

## 4. Assertion Standards

### 4.1 Descriptive Assertions

**Every assertion MUST include a descriptive error message:**

```python
# GOOD - Descriptive assertions
self.assertEqual(result.status, "success",
                f"BuildModule should succeed with valid config, got: {result.status}")

self.assertIn("State Space", result.output,
             "Output should contain state space visualization for debugging")

self.assertEqual(len(theories), 3,
                f"Should load exactly 3 theories, found {len(theories)}: "
                f"{list(theories.keys())}")

# BAD - Generic assertions
self.assertTrue(result)              # What should be true?
self.assertIsNotNone(data)          # What should data contain?
self.assertEqual(len(items), 3)     # Why 3? What are the items?
```

### 4.2 Specific vs Generic Assertions

**Use specific assertions over generic ones:**
```python
# GOOD - Specific assertions
self.assertEqual(result.count, 5)           # vs assertTrue(result.count == 5)
self.assertIn(key, dictionary)             # vs assertTrue(key in dictionary)
self.assertIsInstance(obj, MyClass)        # vs assertTrue(isinstance(obj, MyClass))
self.assertGreater(value, 0)               # vs assertTrue(value > 0)

# GOOD - Multiple specific assertions vs single complex assertion
self.assertEqual(result.status, "success")
self.assertEqual(len(result.models), 2)
self.assertIn("countermodel", result.output)
# vs
# self.assertTrue(result.status == "success" and len(result.models) == 2 and "countermodel" in result.output)
```

### 4.3 Custom Assertion Helpers

**Create reusable assertion helpers for common patterns:**
```python
# fixtures/assertions.py
def assert_valid_theory_structure(test_case, theory, theory_name=""):
    """Assert that theory dictionary has all required components."""
    required_keys = ["semantics", "proposition", "model", "operators"]
    for key in required_keys:
        test_case.assertIn(key, theory,
                          f"Theory {theory_name} missing required key: {key}")

def assert_build_module_initialized(test_case, build_module):
    """Assert that BuildModule has all components properly initialized."""
    components = ["loader", "runner", "comparison", "translation"]
    for component in components:
        test_case.assertTrue(hasattr(build_module, component),
                           f"BuildModule missing component: {component}")
        test_case.assertIsNotNone(getattr(build_module, component),
                                f"BuildModule component {component} is None")
```

---

## 5. Test Data Management

### 5.1 Centralized Test Data

**All test data MUST be centralized in `fixtures/test_data.py`:**

```python
# fixtures/test_data.py
"""Centralized test data for consistent testing across suite."""

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

class TestExamples:
    """Standard example cases for testing."""
    
    SIMPLE_VALID = [["A"], ["B"], {"N": 2}]
    EMPTY_PREMISES = [[], ["A"], {"N": 2}]
    MODAL_EXAMPLE = [["□A"], ["A"], {"N": 2}]
    INVALID_SETTINGS = [["A"], ["B"], {"N": -1}]

class TestModules:
    """Standard module content for file-based testing."""
    
    MINIMAL_CONTENT = '''
from model_checker.theory_lib.logos import get_theory

theory = get_theory(['extensional'])
semantic_theories = {"Test": theory}
example_range = {"TEST": [[], ["A"], {"N": 2}]}
general_settings = {}
'''
    
    SYNTAX_ERROR_CONTENT = '''
this is not valid python syntax !
semantic_theories = undefined_variable
'''
```

### 5.2 Test Data Usage

```python
# Use centralized data consistently across all tests
from fixtures.test_data import TestTheories, TestExamples

class TestSerialization(unittest.TestCase):
    """Test serialization with consistent test data."""
    
    def test_serialize_minimal_theory(self):
        """Test serialization of minimal theory structure."""
        result = serialize_theory("minimal", TestTheories.MINIMAL)
        self.assertIn("theory_name", result)
        self.assertEqual(result["theory_name"], "minimal")
        
    def test_serialize_theory_with_operators(self):
        """Test serialization preserves operator information."""
        result = serialize_theory("operators", TestTheories.WITH_OPERATORS)
        self.assertEqual(len(result["operators"]), 2)
        self.assertIn("\\neg", result["operators"])
```

---

## 6. Performance and Execution Standards

### 6.1 Test Execution Time Targets

**Unit Tests:**
- Individual test: <50ms
- Full unit test suite: <2 seconds  
- Fail fast on first error in development

**Integration Tests:**
- Individual test: <500ms
- Full integration suite: <10 seconds
- Acceptable for some file I/O operations

**End-to-End Tests:**
- Individual test: <5 seconds
- Full e2e suite: <30 seconds
- May include real external operations

### 6.2 Performance Optimization

```python
# GOOD - Fast in-memory testing
def setUp(self):
    self.test_theory = TestTheories.MINIMAL  # Use pre-created objects
    self.mock_module = create_mock_module()  # Factory function

# BAD - Slow file operations in every test
def setUp(self):
    self.temp_dir = tempfile.mkdtemp()        # File system operation
    self.test_file = os.path.join(self.temp_dir, "test.py")
    with open(self.test_file, 'w') as f:      # File I/O in unit test
        f.write(test_content)

# GOOD - Batch setup for multiple tests needing files
@classmethod  
def setUpClass(cls):
    """Set up test files once for entire test class."""
    cls.temp_dir = tempfile.mkdtemp()
    cls.test_files = {}
    for name, content in TEST_FILE_CONTENTS.items():
        file_path = os.path.join(cls.temp_dir, f"{name}.py")
        with open(file_path, 'w') as f:
            f.write(content)
        cls.test_files[name] = file_path
```

---

## 7. Error Testing Standards

### 7.1 Error Condition Coverage

**Every component MUST have tests for:**
- Invalid input handling
- Missing dependencies  
- Boundary conditions
- Resource exhaustion scenarios
- External service failures

### 7.2 Error Testing Patterns

```python
# GOOD - Specific error testing
def test_module_loader_handles_missing_file_gracefully(self):
    """Test ModuleLoader provides helpful error for missing files."""
    loader = ModuleLoader("test", "/nonexistent/path.py")
    
    with self.assertRaises(ImportError) as context:
        loader.load_module()
    
    error_msg = str(context.exception).lower()
    self.assertIn("not found", error_msg,
                  "Error message should indicate file not found")
    self.assertIn("/nonexistent/path.py", str(context.exception),
                  "Error message should include the problematic file path")

# GOOD - Multiple error conditions
def test_build_module_validates_theory_structure(self):
    """Test BuildModule rejects theories missing required components."""
    test_cases = [
        ({}, "Empty theory should be rejected"),
        ({"semantics": None}, "Theory missing other components should be rejected"),
        ({"invalid_key": "value"}, "Theory with wrong structure should be rejected")
    ]
    
    for invalid_theory, description in test_cases:
        with self.subTest(theory=invalid_theory):
            with self.assertRaises((TypeError, ValueError, KeyError)) as context:
                validate_semantic_theory(invalid_theory)
            
            self.assertIsNotNone(str(context.exception), description)
```

---

## 8. Continuous Integration Requirements

### 8.1 Automated Test Execution

**Tests MUST run automatically on:**
- Every pull request
- Every commit to main branch
- Scheduled nightly builds
- Pre-release validation

### 8.2 Test Quality Gates

**Pull requests MUST NOT be merged unless:**
- All tests pass (zero failures)
- Code coverage meets minimum thresholds:
  - Unit tests: 90% line coverage
  - Integration tests: 80% line coverage  
  - Overall: 85% line coverage
- No test execution warnings or errors
- Performance regression tests pass

### 8.3 Test Reporting

**Test results MUST include:**
- Pass/fail status for each test category
- Code coverage reports with highlighted gaps
- Performance metrics and regression detection
- Failed test details with clear error messages

```bash
# Example CI test execution
pytest tests/unit/ --cov=src/ --cov-report=html --cov-fail-under=90
pytest tests/integration/ --cov=src/ --cov-append --cov-fail-under=80  
pytest tests/e2e/ --maxfail=1 --tb=short
```

---

## 9. Migration Guidelines

### 9.1 Legacy Test Improvement

**When updating existing tests:**
1. **Audit Current State**: Identify mocking patterns, documentation gaps, naming issues
2. **Incremental Improvement**: Fix one issue at a time to avoid breaking changes
3. **Validate Functionality**: Ensure test still verifies the same behavior
4. **Update Documentation**: Add or improve docstrings and error messages
5. **Centralize Data**: Move hardcoded test data to fixtures

### 9.2 New Test Requirements

**All new tests MUST follow these standards:**
- Proper test type categorization (unit/integration/e2e)
- Minimal appropriate mocking
- Comprehensive documentation
- Descriptive naming and assertions
- Use of centralized test data

---

## 10. Examples and Templates

### 10.1 Unit Test Template

```python
# tests/unit/test_component.py
"""Unit tests for ComponentClass."""

import unittest
from unittest.mock import Mock, patch

from fixtures.test_data import TestTheories, TestExamples
from fixtures.mock_objects import MockObjectFactory
from fixtures.assertions import assert_valid_theory_structure

from package.component import ComponentClass


class TestComponentClass(unittest.TestCase):
    """Test ComponentClass behavior in isolation."""
    
    def setUp(self):
        """Set up test fixtures."""
        self.component = ComponentClass()
    
    def test_component_method_with_valid_input_returns_expected_result(self):
        """Test ComponentClass.method returns expected result with valid input."""
        # Arrange
        input_data = TestExamples.SIMPLE_VALID
        expected_result = "expected_value"
        
        # Act
        result = self.component.method(input_data)
        
        # Assert
        self.assertEqual(result, expected_result,
                        f"Component should return {expected_result} for valid input")
    
    def test_component_method_raises_error_with_invalid_input(self):
        """Test ComponentClass.method raises ValueError with invalid input."""
        # Arrange
        invalid_input = TestExamples.INVALID_SETTINGS
        
        # Act & Assert
        with self.assertRaises(ValueError) as context:
            self.component.method(invalid_input)
        
        self.assertIn("invalid", str(context.exception).lower(),
                      "Error message should indicate invalid input")


if __name__ == '__main__':
    unittest.main()
```

### 10.2 Integration Test Template

```python
# tests/integration/test_workflow.py
"""Integration tests for multi-component workflows."""

import unittest
import tempfile
import os

from fixtures.test_data import TestModules, TestFlags
from package.main import MainWorkflow


class TestMainWorkflow(unittest.TestCase):
    """Test MainWorkflow component integration."""
    
    def setUp(self):
        """Set up integration test environment."""
        self.temp_dir = tempfile.mkdtemp()
        self.addCleanup(lambda: shutil.rmtree(self.temp_dir))
        
    def test_complete_workflow_with_valid_module_succeeds(self):
        """Test complete workflow processes valid module successfully."""
        # Arrange - Create real test file
        module_path = os.path.join(self.temp_dir, "test_module.py")
        with open(module_path, 'w') as f:
            f.write(TestModules.MINIMAL_CONTENT)
        
        flags = TestFlags.MINIMAL
        flags.file_path = module_path
        
        # Act - Run real workflow
        workflow = MainWorkflow(flags)
        result = workflow.execute()
        
        # Assert - Verify end-to-end behavior
        self.assertEqual(result.status, "success",
                        "Workflow should succeed with valid module")
        self.assertIsNotNone(result.output,
                           "Workflow should produce output")
        self.assertGreater(len(result.models), 0,
                          "Workflow should generate at least one model")


if __name__ == '__main__':
    unittest.main()
```

---

## Conclusion

These testing standards provide a comprehensive framework for creating maintainable, reliable tests that support long-term codebase evolution. By following these guidelines, developers can:

- **Write tests that verify behavior, not implementation details**
- **Minimize maintenance overhead through consistent patterns**  
- **Provide clear debugging information through descriptive assertions**
- **Ensure reliable test execution through appropriate mocking strategies**

**Key Success Metrics:**
- Tests clearly document what behavior they verify
- Test failures provide obvious diagnosis and fix guidance
- New developers can understand and extend tests quickly
- Refactoring is safe and supported by reliable test feedback

## 8. Test Isolation and Environment Management

### 8.1 Test Environment Isolation

**Goal**: Ensure tests run independently without contaminating the development environment or affecting other tests.

#### Test Cleanup Patterns

**Automatic cleanup using proven conftest.py patterns:**

```python
# Package-level conftest.py (e.g., builder/tests/conftest.py)
import pytest
import tempfile
import shutil
import glob
import atexit
from pathlib import Path

@pytest.fixture(autouse=True, scope='function')
def cleanup_test_artifacts():
    """Automatically clean up test artifacts after each test."""
    # Store initial state
    initial_output_dirs = set(glob.glob('output_*'))
    initial_cwd = os.getcwd()
    
    yield  # Run the test
    
    # Cleanup only if we're in the same directory
    if os.getcwd() == initial_cwd:
        final_output_dirs = set(glob.glob('output_*'))
        new_dirs = final_output_dirs - initial_output_dirs
        
        for output_dir in new_dirs:
            try:
                if os.path.exists(output_dir):
                    shutil.rmtree(output_dir)
            except (OSError, PermissionError):
                # Directory might be in use or already removed
                pass

@pytest.fixture(autouse=True, scope='session')
def session_cleanup():
    """Clean up at session end with exit handler."""
    def final_cleanup():
        """Remove all test artifacts from working directory."""
        for pattern in ['output_*', 'temp_test_*', '*.tmp']:
            for artifact in glob.glob(pattern):
                try:
                    if os.path.isdir(artifact):
                        shutil.rmtree(artifact)
                    else:
                        os.remove(artifact)
                except (OSError, PermissionError):
                    pass
    
    # Register cleanup for interpreter exit
    atexit.register(final_cleanup)
    
    yield  # Run all tests
    
    # Final cleanup when session ends
    final_cleanup()
```

#### Temporary Resource Management

**Use proper temporary resource handling:**

```python
@pytest.fixture
def temp_module_file(tmp_path):
    """Create temporary module file for testing."""
    module_content = '''
from model_checker.theory_lib import logos

theory = logos.get_theory(['extensional'])
semantic_theories = {"TestTheory": theory}
example_range = {"TEST": [[], ["A"], {"N": 2}]}
'''
    
    module_path = tmp_path / "test_module.py"
    module_path.write_text(module_content)
    return str(module_path)  # Return path, cleanup handled by tmp_path

@pytest.fixture  
def temp_directory(tmp_path):
    """Create temporary directory structure for testing."""
    test_dir = tmp_path / "test_project"
    test_dir.mkdir()
    
    # Create expected subdirectories
    (test_dir / "examples").mkdir()
    (test_dir / "tests").mkdir()
    
    return test_dir  # Cleanup automatic via tmp_path
```

### 8.2 Output Directory Management

**Problem**: Tests that create output directories can clutter the working directory and interfere with development.

**Solution**: Implement comprehensive output directory cleanup.

#### Root-level Cleanup (conftest.py)

```python
# Root conftest.py - Global cleanup for all tests
import pytest
import glob
import shutil
import atexit
import os

@pytest.fixture(autouse=True, scope='function')
def cleanup_output_directories():
    """Automatically clean up output directories after each test."""
    original_cwd = os.getcwd()
    initial_dirs = set(glob.glob('output_*'))
    
    yield  # Run the test
    
    # Clean up any new output directories created during the test
    if os.getcwd() == original_cwd:
        final_dirs = set(glob.glob('output_*'))
        new_dirs = final_dirs - initial_dirs
        
        for output_dir in new_dirs:
            try:
                if os.path.exists(output_dir):
                    shutil.rmtree(output_dir)
            except (OSError, PermissionError):
                pass  # Directory might be in use

def pytest_runtest_teardown(item):
    """Hook that runs after each test item completes."""
    # Additional safety net for cleanup
    for output_dir in glob.glob('output_*'):
        try:
            if os.path.exists(output_dir):
                shutil.rmtree(output_dir)
        except (OSError, PermissionError):
            pass

def pytest_sessionfinish(session, exitstatus):
    """Hook that runs when the entire test session is finished."""
    # Final cleanup of all output directories
    for output_dir in glob.glob('output_*'):
        try:
            if os.path.exists(output_dir):
                shutil.rmtree(output_dir)
        except (OSError, PermissionError):
            pass
```

### 8.3 Environment Contamination Prevention

#### Test Data Management

**Use isolated test data to prevent cross-test contamination:**

```python
# fixtures/test_data.py
"""Isolated test data that doesn't affect other tests."""

class TestDataFactory:
    """Factory for creating test data that's isolated per test."""
    
    @staticmethod
    def create_minimal_example():
        """Create minimal example that doesn't require cleanup."""
        return [
            ["A"],  # assumptions  
            ["B"],  # formulas
            {"N": 2, "max_time": 5}  # settings
        ]
    
    @staticmethod
    def create_theory_config(theory_name="test_theory"):
        """Create theory config isolated to this test run."""
        return {
            "name": theory_name,
            "settings": {"N": 2},
            "operators": {"wedge": {"symbol": "∧", "arity": 2}}
        }

# Usage in tests
def test_example_processing():
    """Test example processing with isolated data."""
    example_data = TestDataFactory.create_minimal_example()
    result = process_example(example_data)
    assert result.is_successful()
```

#### Mock Object Isolation

**Create fresh mocks for each test to prevent state leakage:**

```python
@pytest.fixture
def fresh_mock_flags():
    """Create a fresh mock flags object for each test."""
    return Mock(
        spec=['file_path', 'print_constraints', 'print_z3', 'save_output'],
        print_constraints=False,
        print_z3=False,
        save_output=False  # Default to no output to prevent file creation
    )

@pytest.fixture
def isolated_build_module(fresh_mock_flags, temp_module_file):
    """Create isolated BuildModule that won't affect other tests."""
    fresh_mock_flags.file_path = temp_module_file
    return BuildModule(fresh_mock_flags)
```

### 8.4 Test Execution Environment

#### Working Directory Management

**Ensure tests don't change working directories permanently:**

```python
@pytest.fixture(autouse=True)
def preserve_working_directory():
    """Ensure working directory is restored after test."""
    original_cwd = os.getcwd()
    
    yield
    
    # Restore original working directory
    os.chdir(original_cwd)
```

#### System Path Isolation

**Prevent sys.path modifications from affecting other tests:**

```python
@pytest.fixture
def isolated_sys_path():
    """Provide isolated sys.path that doesn't affect other tests."""
    original_path = sys.path.copy()
    
    yield sys.path  # Test can modify this
    
    # Restore original sys.path
    sys.path.clear()
    sys.path.extend(original_path)
```

### 8.5 Integration with Existing Test Organization

#### Building on Current Standards

**The test isolation patterns integrate with existing test architecture:**

```python
# Example: Integration test with proper isolation
class TestBuildModuleIntegration:
    """Integration tests with proper environment isolation."""
    
    def test_complete_workflow_isolated(self, temp_module_file, 
                                       fresh_mock_flags):
        """Test complete workflow without environment contamination."""
        # Test uses isolated fixtures
        fresh_mock_flags.file_path = temp_module_file
        fresh_mock_flags.save_output = False  # Prevent output creation
        
        build_module = BuildModule(fresh_mock_flags)
        result = build_module.process_examples()
        
        assert result.is_successful()
        # No cleanup needed - fixtures handle isolation
```

### 8.6 Cleanup Validation

#### Testing the Cleanup Itself

**Ensure cleanup mechanisms work correctly:**

```python
def test_output_directory_cleanup():
    """Verify that output directory cleanup works correctly."""
    # Create a test output directory
    test_output = "output_test_12345"
    os.makedirs(test_output)
    assert os.path.exists(test_output)
    
    # This test should clean up after itself via conftest.py
    # The directory should be gone after the test runs

def test_no_test_artifacts_remain():
    """Verify no test artifacts remain after test execution."""
    # Check for common test pollution patterns
    artifacts = []
    artifacts.extend(glob.glob('output_*'))
    artifacts.extend(glob.glob('temp_test_*'))
    artifacts.extend(glob.glob('*.tmp'))
    
    # Should find no artifacts (cleanup working correctly)
    assert len(artifacts) == 0, f"Test artifacts found: {artifacts}"
```

### 8.7 Performance Considerations

#### Efficient Cleanup

**Balance thorough cleanup with test performance:**

```python
# Efficient cleanup - only clean what was created
@pytest.fixture(autouse=True)
def efficient_cleanup():
    """Clean up efficiently by tracking what was created."""
    created_files = []
    created_dirs = []
    
    # Monkey patch creation functions to track
    original_makedirs = os.makedirs
    def tracking_makedirs(path, **kwargs):
        result = original_makedirs(path, **kwargs)
        created_dirs.append(path)
        return result
    
    os.makedirs = tracking_makedirs
    
    yield
    
    # Clean up only what was created by this test
    for directory in created_dirs:
        try:
            shutil.rmtree(directory)
        except (OSError, PermissionError):
            pass
    
    # Restore original function
    os.makedirs = original_makedirs
```

## Conclusion

Effective test isolation ensures that:

1. **Tests run independently** without affecting each other
2. **Development environment stays clean** during and after test execution
3. **Test results are reliable** and not affected by previous test runs
4. **Continuous integration works smoothly** without artifact accumulation

These patterns build on the successful cleanup implementations from the builder/ package and provide **flexible, proven approaches** to test isolation without requiring major changes to existing test suites.

**Apply these patterns gradually:**
- **New tests**: Use isolation fixtures from the start
- **Existing tests**: Add cleanup when making other changes
- **Problem tests**: Fix isolation issues when they cause problems
- **CI/CD**: Implement comprehensive cleanup for automated testing

---

**Document Status**: Enhanced with test isolation patterns based on successful builder/ implementations  
**Next Review**: After applying isolation patterns to additional packages  
**Enforcement**: Required for all new tests, recommended for legacy test updates

---

[← Performance](PERFORMANCE.md) | [Back to Maintenance](README.md) | [Test Organization →](TEST_ORGANIZATION.md)