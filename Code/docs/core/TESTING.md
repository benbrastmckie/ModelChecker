# Comprehensive Testing Standards

[← Code Standards](CODE_STANDARDS.md) | [Back to Maintenance](../README.md) | [Architecture →](ARCHITECTURE.md)

## Overview

This document defines comprehensive testing standards for the ModelChecker codebase, consolidating testing practices, test organization, and Test-Driven Development requirements into a unified framework. These standards ensure maintainable, reliable, and efficient tests that support long-term codebase evolution.

**Core Testing Philosophy:**
- **Test-Driven Development**: Write tests BEFORE implementation code
- **Minimal Mocking**: Use real objects wherever possible, mock only external dependencies
- **Clear Separation**: Distinct unit, integration, and end-to-end test categories
- **Test Isolation**: Tests run independently without contaminating the environment
- **Comprehensive Documentation**: Every test explains what behavior is verified

---

## 1. Test-Driven Development Requirements

### 1.1 TDD Workflow

**MANDATORY Process**: All new features and fixes MUST follow TDD:

```python
# RED: Write failing test first
def test_new_feature_handles_valid_input_successfully(self):
    """Test new feature processes valid input correctly."""
    # This test will fail initially
    input_data = TestExamples.SIMPLE_VALID
    expected_output = "processed_successfully"
    
    result = new_feature(input_data)
    
    self.assertEqual(result, expected_output,
                    "New feature should process valid input successfully")

# GREEN: Write minimal implementation to pass
def new_feature(data):
    # Minimal implementation to make test pass
    if data == TestExamples.SIMPLE_VALID:
        return "processed_successfully"
    raise NotImplementedError("Additional cases not implemented yet")

# REFACTOR: Improve code quality while keeping tests passing
def new_feature(data):
    # Full implementation with proper logic
    validate_input(data)
    processed = process_data(data)
    return format_output(processed)
```

### 1.2 TDD Compliance Requirements

**Before any code implementation:**
1. **Write Failing Test**: Create test that describes desired behavior
2. **Run Test**: Verify test fails (RED state)
3. **Minimal Implementation**: Write just enough code to pass
4. **Run Test**: Verify test passes (GREEN state)
5. **Refactor**: Improve code quality while maintaining passing tests
6. **Repeat**: Continue cycle for next requirement

**TDD Verification Checklist:**
- [ ] Test written before implementation
- [ ] Test initially fails (proves it tests something)
- [ ] Minimal implementation makes test pass
- [ ] Code refactored for quality
- [ ] All tests still pass after refactoring

### 1.3 TDD for Bug Fixes

**Bug Fix Process:**
1. **Reproduce Bug**: Write test that demonstrates the bug
2. **Verify Failure**: Confirm test fails with current code
3. **Fix Bug**: Make minimal changes to pass the test
4. **Verify Fix**: Ensure test passes and bug is resolved
5. **Regression Prevention**: Test prevents bug from reoccurring

```python
def test_bug_fix_loader_handles_malformed_syntax_gracefully(self):
    """Test that ModuleLoader handles malformed syntax with helpful error.
    
    Bug: ModuleLoader crashes with unhelpful error when syntax is malformed.
    Expected: Should raise ImportError with clear message about syntax issues.
    """
    malformed_content = "this is not valid python !@#$"
    loader = ModuleLoader("test", create_temp_file(malformed_content))
    
    with self.assertRaises(ImportError) as context:
        loader.load_module()
    
    error_msg = str(context.exception).lower()
    self.assertIn("syntax", error_msg,
                  "Error should mention syntax problem")
    self.assertIn("malformed", error_msg,
                  "Error should indicate malformed code")
```

---

## 2. Test Architecture Standards

### 2.1 Test Directory Structure

**Standard Structure** (follows builder pattern):
```
package_name/
└── tests/
    ├── unit/                          # Pure unit tests - single component, minimal deps
    │   ├── test_component1.py         # Individual component unit tests
    │   ├── test_component2.py
    │   └── test_utilities.py          # Utility function tests
    ├── integration/                   # Component interaction tests
    │   ├── test_workflow.py           # Multi-component workflows
    │   ├── test_cross_component.py    # Component integration
    │   └── test_error_propagation.py  # Error handling across components
    ├── e2e/                           # Full pipeline/system tests
    │   ├── test_cli_execution.py      # Complete command-line workflows
    │   ├── test_user_scenarios.py     # End-to-end user scenarios
    │   └── test_performance.py        # System-wide performance (optional)
    ├── fixtures/                      # Centralized test data and utilities
    │   ├── __init__.py
    │   ├── test_data.py               # Shared constants and test data
    │   ├── mock_objects.py            # Standardized mock object factories
    │   ├── temp_resources.py          # Resource management utilities
    │   └── assertions.py              # Custom assertion helpers
    ├── utils/                         # Test utility functions
    │   ├── __init__.py
    │   ├── file_helpers.py            # File/directory test utilities
    │   └── validation_helpers.py      # Test validation utilities
    ├── conftest.py                    # Pytest configuration and shared fixtures
    └── README.md                      # Test suite documentation
```

### 2.2 Test Type Classification

#### **Unit Tests** (`tests/unit/`)
**Purpose**: Test individual components in isolation with TDD approach
**Characteristics:**
- Written BEFORE component implementation (TDD requirement)
- Tests single class or function
- Minimal external dependencies
- Fast execution (milliseconds)
- Mock only external services (file system, network, databases)

```python
# TDD Example: Write test first
class TestModelRunner(unittest.TestCase):
    """Test ModelRunner component in isolation."""
    
    def test_run_model_check_with_valid_example_returns_success(self):
        """Test ModelRunner processes valid example successfully.
        
        This test drives the implementation of ModelRunner.run_model_check()
        to ensure it handles valid examples correctly.
        """
        # Arrange (written before implementation exists)
        mock_build_module = create_minimal_build_module()
        runner = ModelRunner(mock_build_module)
        valid_example = TestExamples.SIMPLE_VALID
        
        # Mock external dependency only
        with patch('z3.Solver') as mock_solver:
            mock_solver.return_value.check.return_value = z3.sat
            
            # Act (this will initially fail - TDD RED state)
            result = runner.run_model_check(valid_example)
            
            # Assert (defines expected behavior)
            self.assertEqual(result.status, "success",
                           "ModelRunner should succeed with valid example")
            self.assertIsNotNone(result.models,
                               "Result should contain generated models")
```

#### **Integration Tests** (`tests/integration/`)
**Purpose**: Test component interactions following TDD for workflows
**Characteristics:**
- Tests multiple components together
- Verifies component boundaries and communication
- Uses real objects for internal architecture
- Moderate execution time (seconds)

```python
# TDD Integration Test: Write workflow test first
class TestBuildModuleWorkflow(unittest.TestCase):
    """Test BuildModule component integration."""
    
    def test_complete_model_checking_workflow_succeeds(self):
        """Test complete workflow from loading to result output.
        
        This integration test drives the implementation of the complete
        workflow between BuildModule components.
        """
        # Arrange (test written before workflow is fully implemented)
        flags = create_test_flags()
        build_module = BuildModule(flags)
        
        # Act (test real component interaction without excessive mocking)
        result = build_module.runner.run_examples()
        
        # Assert (defines expected integration behavior)
        self.assertIsNotNone(result,
                           "Workflow should produce results")
        self.assertTrue(hasattr(build_module, 'loader'),
                       "BuildModule should have loader component")
        self.assertTrue(hasattr(build_module, 'runner'),
                       "BuildModule should have runner component")
```

#### **End-to-End Tests** (`tests/e2e/`)
**Purpose**: Test complete user workflows with TDD for user scenarios
**Characteristics:**
- Tests full user scenarios from start to finish
- Minimal to no mocking
- Real file operations and external interactions
- Slower execution (seconds to minutes)

```python
# TDD E2E Test: Write user scenario test first
class TestCLIExecution(unittest.TestCase):
    """Test complete CLI execution workflows."""
    
    def test_theory_execution_from_command_line_produces_output(self):
        """Test complete theory execution via CLI produces expected output.
        
        This end-to-end test drives the implementation of the CLI interface
        to ensure it provides the expected user experience.
        """
        # Arrange (test written before CLI is fully implemented)
        with tempfile.NamedTemporaryFile(mode='w', suffix='.py', delete=False) as f:
            f.write(TestModules.MINIMAL_CONTENT)
            test_file = f.name
        
        try:
            # Act (execute real CLI command)
            result = subprocess.run(
                [sys.executable, 'dev_cli.py', test_file],
                capture_output=True, text=True
            )
            
            # Assert (defines expected user-facing behavior)
            self.assertEqual(result.returncode, 0,
                           "CLI should exit successfully with valid input")
            self.assertIn("EXAMPLE", result.stdout,
                         "CLI should show example processing")
            self.assertNotIn("Traceback", result.stderr,
                           "CLI should not show error traces on success")
        finally:
            os.unlink(test_file)
```

---

## 3. Test Coverage Requirements

### 3.1 Coverage Targets

**Unit Tests:**
- Line coverage: >90% for all core components
- Branch coverage: >85% for critical logic paths
- Function coverage: 100% for public APIs

**Integration Tests:**
- Component boundary coverage: 100% of public interfaces
- Workflow coverage: All major data flow paths
- Error propagation coverage: Cross-component error scenarios

**End-to-End Tests:**
- User scenario coverage: All documented use cases
- CLI coverage: All command-line options and workflows
- Error handling coverage: All user-facing error conditions

### 3.2 Coverage Measurement

```bash
# Unit test coverage
pytest tests/unit/ --cov=src/ --cov-report=html --cov-fail-under=90

# Integration test coverage
pytest tests/integration/ --cov=src/ --cov-append --cov-fail-under=80

# Full coverage report
pytest tests/ --cov=src/ --cov-report=html --cov-fail-under=85
```

### 3.3 Coverage Quality Requirements

**NOT just line coverage:**
- **Edge case coverage**: Boundary conditions and error cases
- **Logic branch coverage**: All conditional paths tested
- **State coverage**: All object states and transitions
- **Integration coverage**: All component interaction patterns

---

## 4. Test Isolation and Environment Management

### 4.1 Test Environment Isolation

**Goal**: Ensure tests run independently without contaminating the development environment or affecting other tests.

#### Automatic Cleanup Patterns

```python
# Package-level conftest.py
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
                pass  # Directory might be in use or already removed

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

### 4.2 Output Directory Management

```python
# Root conftest.py - Global cleanup for all tests
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
```

---

## 5. Mocking Standards

### 5.1 When to Mock

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

### 5.2 Mock Creation Standards

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

### 5.3 Centralized Mock Factories

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

## 6. Test Data Management

### 6.1 Centralized Test Data

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

### 6.2 Test Data Usage Standards

```python
# Use centralized data consistently across all tests
from fixtures.test_data import TestTheories, TestExamples

class TestSerialization(unittest.TestCase):
    """Test serialization with consistent test data."""
    
    def test_serialize_minimal_theory_produces_valid_output(self):
        """Test serialization of minimal theory structure produces valid output."""
        # Using centralized test data
        result = serialize_theory("minimal", TestTheories.MINIMAL)
        
        self.assertIn("theory_name", result,
                     "Serialized theory should include theory name")
        self.assertEqual(result["theory_name"], "minimal",
                        "Theory name should match input parameter")
```

---

## 7. Test Documentation Standards

### 7.1 Test Method Documentation

**Every test method MUST have a docstring that:**
- Explains what behavior is being tested
- Uses present tense ("Test that X does Y")
- Describes the expected outcome
- Indicates if it's driving implementation (TDD)

```python
def test_module_loader_raises_import_error_when_file_not_found(self):
    """Test that ModuleLoader raises ImportError when module file does not exist.
    
    This ensures proper error handling for missing module files and helps
    users understand what went wrong during module loading. This test drives
    the implementation of proper error handling in ModuleLoader.load_module().
    """
    loader = ModuleLoader("nonexistent", "/path/that/does/not/exist.py")
    
    with self.assertRaises(ImportError) as context:
        loader.load_module()
    
    self.assertIn("not found", str(context.exception).lower(),
                 "Error message should indicate file not found")
```

### 7.2 Test Method Naming

**Naming Pattern:** `test_[component]_[action]_[condition]_[expected_result]`

**Examples:**
```python
# Component behavior tests (TDD-driven)
def test_module_loader_loads_valid_theory_successfully(self):
def test_model_runner_raises_error_with_invalid_settings(self):
def test_build_module_initializes_all_components_correctly(self):

# Edge case tests (TDD for edge cases)
def test_operator_translation_handles_empty_dictionary_gracefully(self):
def test_serialization_preserves_unicode_characters_correctly(self):
def test_comparison_returns_empty_list_with_no_theories(self):

# Error condition tests (TDD for error handling)
def test_loader_raises_syntax_error_with_malformed_python(self):
def test_runner_propagates_z3_timeout_errors_appropriately(self):
```

---

## 8. Test Quality and Performance Standards

### 8.1 Test Execution Time Targets

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

### 8.2 Assertion Standards

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

### 8.3 Custom Assertion Helpers

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

## 9. Theory Compliance Testing

### 9.1 Theory Library Testing Requirements

**Every theory library MUST have tests for:**
- Semantic functionality (core logic)
- Operator validation (all defined operators)
- Example verification (provided examples work)
- Model iteration (if applicable)
- Constraint injection (integration with Z3)

### 9.2 Theory Test Structure

```
theory_name/
└── tests/
    ├── unit/                         # Core theory logic tests
    │   ├── test_semantic.py          # Semantic functionality
    │   ├── test_operators.py         # Operator validation
    │   └── test_proposition.py       # Proposition handling
    ├── integration/                  # Theory integration tests
    │   ├── test_examples.py          # Example verification
    │   ├── test_iterate.py           # Model iteration
    │   └── test_injection.py         # Constraint injection
    ├── e2e/                          # Complete workflows
    │   └── test_cli_execution.py     # CLI testing
    ├── fixtures/                     # Theory-specific test data
    ├── utils/                        # Theory test utilities
    ├── conftest.py                   # Pytest configuration
    └── README.md                     # Test documentation
```

### 9.3 Theory Testing Template

```python
# TDD Theory Test Example
class TestTheorySemantics(unittest.TestCase):
    """Test theory semantic functionality with TDD approach."""
    
    def test_theory_validates_modal_formulas_correctly(self):
        """Test theory correctly validates modal formulas.
        
        This test drives the implementation of modal formula validation
        in the theory's semantic component.
        """
        # Test written before semantic validation is implemented
        modal_formula = "□(A → B)"
        theory = get_theory(['modal'])
        
        # This will initially fail (TDD RED state)
        is_valid = theory.semantics.validate_formula(modal_formula)
        
        self.assertTrue(is_valid,
                       "Theory should validate well-formed modal formulas")
    
    def test_theory_rejects_malformed_modal_syntax(self):
        """Test theory rejects malformed modal syntax with helpful error."""
        malformed_formula = "□□□(A →"  # Incomplete formula
        theory = get_theory(['modal'])
        
        with self.assertRaises(SyntaxError) as context:
            theory.semantics.validate_formula(malformed_formula)
        
        self.assertIn("incomplete", str(context.exception).lower(),
                     "Error should indicate incomplete formula")
```

---

## 10. Continuous Integration and Quality Gates

### 10.1 Automated Test Execution

**Tests MUST run automatically on:**
- Every pull request
- Every commit to main branch
- Scheduled nightly builds
- Pre-release validation

### 10.2 Test Quality Gates

**Pull requests MUST NOT be merged unless:**
- All tests pass (zero failures)
- Code coverage meets minimum thresholds:
  - Unit tests: 90% line coverage
  - Integration tests: 80% line coverage
  - Overall: 85% line coverage
- No test execution warnings or errors
- Performance regression tests pass
- TDD compliance verified (tests exist before implementation)

### 10.3 TDD Compliance Verification

**Automated checks for TDD compliance:**
```bash
# Verify test-first development
git log --oneline --grep="test:" | wc -l  # Count test commits
git log --oneline --grep="implement:" | wc -l  # Count implementation commits

# Test coverage for new code
pytest --cov=src/ --cov-fail-under=90 --cov-branch

# Performance regression detection
pytest tests/ --benchmark-only --benchmark-sort=mean
```

---

## 11. Migration and Maintenance Guidelines

### 11.1 Legacy Test Improvement

**When updating existing tests:**
1. **Apply TDD Retroactively**: If tests don't exist, write them first before making changes
2. **Audit Current State**: Identify mocking patterns, documentation gaps, naming issues
3. **Incremental Improvement**: Fix one issue at a time to avoid breaking changes
4. **Validate Functionality**: Ensure test still verifies the same behavior
5. **Update Documentation**: Add or improve docstrings and error messages
6. **Centralize Data**: Move hardcoded test data to fixtures

### 11.2 New Test Requirements

**All new tests MUST follow these standards:**
- **TDD Compliance**: Written before implementation code
- Proper test type categorization (unit/integration/e2e)
- Minimal appropriate mocking
- Comprehensive documentation
- Descriptive naming and assertions
- Use of centralized test data
- Test isolation and cleanup

---

## 12. Templates and Examples

### 12.1 TDD Unit Test Template

```python
# tests/unit/test_component.py
"""Unit tests for ComponentClass following TDD approach."""

import unittest
from unittest.mock import Mock, patch

from fixtures.test_data import TestTheories, TestExamples
from fixtures.mock_objects import MockObjectFactory
from fixtures.assertions import assert_valid_theory_structure

from package.component import ComponentClass


class TestComponentClass(unittest.TestCase):
    """Test ComponentClass behavior in isolation using TDD."""
    
    def setUp(self):
        """Set up test fixtures."""
        self.component = ComponentClass()
    
    def test_component_method_with_valid_input_returns_expected_result(self):
        """Test ComponentClass.method returns expected result with valid input.
        
        This test drives the implementation of ComponentClass.method()
        to ensure it processes valid input correctly.
        """
        # Arrange (test written before method implementation)
        input_data = TestExamples.SIMPLE_VALID
        expected_result = "expected_value"
        
        # Act (this will initially fail in TDD RED state)
        result = self.component.method(input_data)
        
        # Assert (defines expected behavior for implementation)
        self.assertEqual(result, expected_result,
                        f"Component should return {expected_result} for valid input")
    
    def test_component_method_raises_error_with_invalid_input(self):
        """Test ComponentClass.method raises ValueError with invalid input.
        
        This test drives the implementation of proper error handling
        in ComponentClass.method().
        """
        # Arrange (test written before error handling is implemented)
        invalid_input = TestExamples.INVALID_SETTINGS
        
        # Act & Assert (defines expected error behavior)
        with self.assertRaises(ValueError) as context:
            self.component.method(invalid_input)
        
        self.assertIn("invalid", str(context.exception).lower(),
                      "Error message should indicate invalid input")


if __name__ == '__main__':
    unittest.main()
```

### 12.2 TDD Integration Test Template

```python
# tests/integration/test_workflow.py
"""Integration tests for multi-component workflows using TDD."""

import unittest
import tempfile
import os

from fixtures.test_data import TestModules, TestFlags
from package.main import MainWorkflow


class TestMainWorkflow(unittest.TestCase):
    """Test MainWorkflow component integration using TDD."""
    
    def setUp(self):
        """Set up integration test environment."""
        self.temp_dir = tempfile.mkdtemp()
        self.addCleanup(lambda: shutil.rmtree(self.temp_dir))
        
    def test_complete_workflow_with_valid_module_succeeds(self):
        """Test complete workflow processes valid module successfully.
        
        This integration test drives the implementation of the complete
        workflow between MainWorkflow components.
        """
        # Arrange - Create real test file
        module_path = os.path.join(self.temp_dir, "test_module.py")
        with open(module_path, 'w') as f:
            f.write(TestModules.MINIMAL_CONTENT)
        
        flags = TestFlags.MINIMAL
        flags.file_path = module_path
        
        # Act - Run real workflow (initially fails in TDD RED state)
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

## 13. Success Metrics and Quality Indicators

### 13.1 TDD Compliance Metrics

**TDD Success Indicators:**
- **Test-first ratio**: >95% of implementations have tests written first
- **Red-Green-Refactor cycles**: Clear commit history showing TDD cycles
- **Test failure rate**: Tests initially fail before implementation
- **Refactoring safety**: Code can be refactored without breaking tests

### 13.2 Test Quality Metrics

**Organizational Quality:**
- ✅ Clear separation of unit/integration/e2e tests
- ✅ Centralized test data with no duplication
- ✅ Consistent naming and documentation patterns
- ✅ Appropriate mocking levels for each test type

**Test Maintainability:**
- ✅ New developers can understand test organization within 30 minutes
- ✅ Adding new tests follows clear, documented patterns
- ✅ Test failures provide obvious diagnosis and fix guidance
- ✅ Refactoring components requires minimal test changes

### 13.3 Performance Metrics

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

These comprehensive testing standards establish a complete framework for Test-Driven Development and quality assurance in the ModelChecker codebase. By following these guidelines, developers can:

- **Write tests BEFORE implementation** following strict TDD methodology
- **Create maintainable, reliable tests** that verify behavior, not implementation details
- **Organize tests efficiently** with clear separation and centralized data management
- **Ensure test isolation** to prevent environment contamination
- **Maintain high code coverage** with meaningful, descriptive tests

**Key Success Factors:**
- **TDD Compliance**: All new code developed test-first
- **Clear test organization**: Proper separation of unit/integration/e2e tests
- **Comprehensive documentation**: Every test explains its purpose and expected behavior
- **Test isolation**: Tests run independently without side effects
- **Quality gates**: Automated verification of test quality and coverage

The framework supports both individual development workflows and automated CI/CD processes, ensuring reliable software delivery while maintaining development velocity through fast, reliable test feedback.

**Implementation Priority:**
1. **New development**: MUST follow TDD and all standards
2. **Bug fixes**: MUST write test first, then fix
3. **Legacy code**: Apply standards incrementally during maintenance
4. **CI/CD**: Implement quality gates and automated verification

---

**Document Status**: Comprehensive consolidation of testing standards with TDD requirements  
**Implementation**: MANDATORY for all new development, recommended for legacy improvements  
**Next Review**: After completing framework-wide TDD adoption

---

[← Code Standards](CODE_STANDARDS.md) | [Back to Maintenance](../README.md) | [Architecture →](ARCHITECTURE.md)