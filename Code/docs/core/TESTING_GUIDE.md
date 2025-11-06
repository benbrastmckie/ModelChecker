# Comprehensive Testing Guide

[← Code Standards](CODE_STANDARDS.md) | [Back to Core](README.md) | [Architecture →](ARCHITECTURE.md)

## Overview

This guide defines comprehensive testing standards for the ModelChecker codebase, consolidating testing practices, test organization, and Test-Driven Development requirements into a unified framework. These standards ensure maintainable, reliable, and efficient tests that support long-term codebase evolution.

**Core Testing Philosophy:**
- **Test-Driven Development**: Write tests BEFORE implementation code
- **Fail Fast**: Tests expose errors clearly rather than masking them
- **Minimal Mocking**: Use real objects wherever possible, mock only external dependencies
- **Clear Separation**: Distinct unit, integration, and end-to-end test categories
- **Test Isolation**: Tests run independently without contaminating the environment
- **Comprehensive Documentation**: Every test explains what behavior is verified

---

## Table of Contents

1. [Test-Driven Development Requirements](#1-test-driven-development-requirements)
2. [Test Organization and Structure](#2-test-organization-and-structure)
3. [Test Categories](#3-test-categories)
4. [Running Tests](#4-running-tests)
5. [Writing Effective Tests](#5-writing-effective-tests)
6. [Theory-Specific Testing](#6-theory-specific-testing)
7. [Test Coverage Requirements](#7-test-coverage-requirements)
8. [Best Practices and Patterns](#8-best-practices-and-patterns)

---

## 1. Test-Driven Development Requirements

### 1.1 TDD Workflow (RED-GREEN-REFACTOR)

**MANDATORY Process**: All new features and fixes MUST follow TDD:

```python
# RED: Write failing test first
def test_new_feature_handles_valid_input_successfully():
    """Test new feature processes valid input correctly."""
    # This test will fail initially
    input_data = TestExamples.SIMPLE_VALID
    expected_output = "processed_successfully"

    result = new_feature(input_data)

    assert result == expected_output, \
        "New feature should process valid input successfully"

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
def test_bug_fix_loader_handles_malformed_syntax_gracefully():
    """Test that ModuleLoader handles malformed syntax with helpful error.

    Bug: ModuleLoader crashes with unhelpful error when syntax is malformed.
    Expected: Should raise ImportError with clear message about syntax issues.
    """
    malformed_content = "this is not valid python !@#$"
    loader = ModuleLoader("test", create_temp_file(malformed_content))

    with pytest.raises(ImportError) as exc_info:
        loader.load_module()

    error_msg = str(exc_info.value).lower()
    assert "syntax" in error_msg, "Error should mention syntax problem"
    assert "malformed" in error_msg, "Error should indicate malformed code"
```

---

## 2. Test Organization and Structure

### 2.1 Test Directory Structure

```
Code/
├── tests/                         # Top-level test discovery
│   ├── unit/                      # Unit tests for packages
│   └── integration/               # Cross-package integration tests
└── src/model_checker/
    ├── theory_lib/
    │   ├── logos/
    │   │   └── tests/
    │   │       ├── unit/          # Theory unit tests
    │   │       └── integration/   # Theory integration tests
    │   ├── exclusion/
    │   │   └── tests/
    │   │       ├── unit/
    │   │       └── integration/
    │   └── tests/                 # Cross-theory infrastructure tests
    ├── builder/
    │   └── tests/
    │       └── unit/
    └── iterate/
        └── tests/
            └── unit/
```

### 2.2 Test File Naming Conventions

- **Unit tests**: `test_<module_name>.py` (e.g., `test_semantic.py`)
- **Integration tests**: `test_<feature>_integration.py`
- **Example tests**: `test_<theory>_examples.py`
- **Test modules**: Mirror the structure of source code

### 2.3 Test Runner Configuration

The ModelChecker project uses two complementary test approaches:

**Method 1: pytest (Primary)**
```bash
# From project root, run all tests
PYTHONPATH=Code/src pytest Code/tests/ -v

# Run specific theory tests
PYTHONPATH=Code/src pytest Code/src/model_checker/theory_lib/logos/tests/ -v

# Run with coverage
PYTHONPATH=Code/src pytest --cov=model_checker --cov-report=term-missing
```

**Method 2: dev_cli.py (Development)**
```bash
# Run tests through development CLI
cd Code
./dev_cli.py test
```

---

## 3. Test Categories

### 3.1 Example Tests (Integration Tests)

**Purpose**: Validate that the model checker produces correct results for logical examples

**Characteristics**:
- Test complete model checking pipeline from formula parsing to result validation
- Use realistic logical examples that demonstrate theory capabilities
- Validate both valid arguments (no countermodel) and invalid arguments (countermodel found)
- Cover all operator types and their interactions

**Location**:
- `theory_lib/*/tests/integration/test_*_examples.py`
- `theory_lib/*/subtheories/*/tests/integration/test_*_examples.py`

**Example Structure**:
```python
def test_logos_modus_ponens_is_valid():
    """Test that modus ponens is valid in logos theory.

    Formula: (p → q), p ⊢ q
    Expected: Valid (no countermodel)
    """
    premises = ["(p > q)", "p"]
    conclusion = "q"

    result = check_validity(premises, conclusion, theory="logos")

    assert result.is_valid, "Modus ponens should be valid"
    assert result.countermodel is None, "Should have no countermodel"
```

### 3.2 Unit Tests (Component Tests)

**Purpose**: Validate individual software components work correctly

**Characteristics**:
- Test semantic methods directly (without full model checking pipeline)
- Test operator implementations and their semantic clauses
- Test registry and loading mechanisms
- Test error conditions and edge cases
- Validate API contracts and data structures

**Location**:
- `theory_lib/*/tests/unit/test_*.py`
- `builder/tests/unit/test_*.py`
- `iterate/tests/unit/test_*.py`

**Example Structure**:
```python
def test_semantic_evaluates_conjunction_correctly():
    """Test that conjunction operator evaluates correctly."""
    semantic = LogosSemantic()
    model = semantic.create_base_model()

    # Set up: p=True, q=False
    model.add_constraint(semantic.atoms['p'] == True)
    model.add_constraint(semantic.atoms['q'] == False)

    # Test: p ∧ q should be False
    conjunction = semantic.evaluate_and(model, 'p', 'q')

    assert conjunction == False, "p ∧ q should be False when q is False"
```

### 3.3 Infrastructure Tests

**Purpose**: Verify cross-theory functionality and framework infrastructure

**Characteristics**:
- Metadata management (versions, citations, licenses)
- Theory discovery and loading
- Cross-theory compatibility
- Common functionality validation

**Location**: `theory_lib/tests/`

---

## 4. Running Tests

### 4.1 Dual Testing Methodology

The ModelChecker uses a **dual testing methodology** to ensure comprehensive validation. Both methods are REQUIRED for all changes:

**Method 1: pytest (Primary Test Runner)**
- **When**: Before every commit, during development
- **Coverage**: All unit tests, integration tests, and theory tests
- **Command**: `PYTHONPATH=Code/src pytest Code/tests/ -v`

**Method 2: dev_cli.py (Development Workflow)**
- **When**: During feature development, interactive testing
- **Coverage**: Full pipeline testing with real examples
- **Command**: `cd Code && ./dev_cli.py test`

### 4.2 Common Test Commands

```bash
# Run all tests with verbose output
PYTHONPATH=Code/src pytest Code/tests/ -v

# Run specific theory tests
PYTHONPATH=Code/src pytest Code/src/model_checker/theory_lib/logos/tests/unit/ -v

# Run with coverage report
PYTHONPATH=Code/src pytest --cov=model_checker --cov-report=term-missing --cov-report=html

# Run specific test file
PYTHONPATH=Code/src pytest Code/tests/unit/test_semantic.py -v

# Run specific test function
PYTHONPATH=Code/src pytest Code/tests/unit/test_semantic.py::test_conjunction_evaluates_correctly -v

# Run tests matching pattern
PYTHONPATH=Code/src pytest -k "test_logos" -v

# Stop on first failure
PYTHONPATH=Code/src pytest -x -v

# Show local variables on failure
PYTHONPATH=Code/src pytest -l -v
```

### 4.3 Continuous Integration

All tests must pass in CI before merging. CI runs:
1. Full test suite with pytest
2. Coverage analysis (must meet thresholds)
3. Type checking with mypy
4. Linting with flake8

---

## 5. Writing Effective Tests

### 5.1 Test Structure (AAA Pattern)

Follow the **Arrange-Act-Assert** pattern:

```python
def test_feature_handles_edge_case():
    """Test that feature handles edge case correctly."""
    # ARRANGE: Set up test conditions
    test_input = create_edge_case_input()
    expected_output = calculate_expected_result(test_input)

    # ACT: Execute the code under test
    actual_output = feature_under_test(test_input)

    # ASSERT: Verify results
    assert actual_output == expected_output, \
        f"Feature should handle edge case: expected {expected_output}, got {actual_output}"
```

### 5.2 Test Documentation

Every test MUST have a docstring explaining:
- What behavior is being tested
- Why this test exists (especially for bug fixes)
- Expected outcome

```python
def test_loader_rejects_invalid_package_marker():
    """Test that ModuleLoader rejects packages with invalid .modelchecker marker.

    The .modelchecker file must contain 'package=true' to be valid.
    This test ensures we fail fast on invalid package markers rather than
    allowing silent failures or unexpected behavior.

    Expected: ImportError with clear message about invalid marker.
    """
    # Test implementation...
```

### 5.3 Assertion Messages

Always include descriptive assertion messages:

```python
# Good: Clear message explaining what went wrong
assert result.is_valid, \
    f"Formula '{formula}' should be valid in {theory} theory"

# Bad: No message
assert result.is_valid
```

### 5.4 Test Isolation

Each test must be independent:

```python
# Good: Each test creates its own data
def test_feature_A():
    data = create_test_data()
    result = process(data)
    assert result.success

def test_feature_B():
    data = create_test_data()  # Fresh data, not shared
    result = process(data)
    assert result.success

# Bad: Tests share mutable state
shared_data = create_test_data()  # Don't do this

def test_feature_A():
    result = process(shared_data)
    assert result.success

def test_feature_B():
    result = process(shared_data)  # Depends on test_A's side effects
    assert result.success
```

---

## 6. Theory-Specific Testing

### 6.1 Testing Semantic Implementations

Every theory MUST test:
- All operators are correctly implemented
- Operator interactions work as expected
- Edge cases and boundary conditions
- Error handling for invalid formulas

```python
def test_logos_conditional_satisfies_modus_ponens():
    """Test that → operator supports modus ponens inference."""
    semantic = LogosSemantic()

    # Test: (p → q) ∧ p entails q
    premises = ["(p > q)", "p"]
    conclusion = "q"

    result = semantic.check_entailment(premises, conclusion)

    assert result.is_valid, "Modus ponens should be valid in logos"
```

### 6.2 Testing Examples

Every theory should have comprehensive examples covering:
- Valid arguments (should find no countermodel)
- Invalid arguments (should find countermodel)
- All operators in isolation
- Complex operator combinations
- Known logical principles

**Example Test Structure**:
```python
def test_exclusion_veridicality_principle():
    """Test that exclusion validates veridicality principle.

    Principle: ◻p ⊢ p (what is necessary is true)
    Expected: Valid in exclusion theory
    """
    premises = ["[]p"]
    conclusion = "p"

    result = check_validity(premises, conclusion, theory="exclusion")

    assert result.is_valid, "Veridicality should hold in exclusion"
```

### 6.3 Cross-Theory Compatibility

Test that theories can coexist and theory selection works:

```python
def test_theory_selection_loads_correct_semantics():
    """Test that specifying theory loads correct semantic implementation."""
    logos_result = run_model_checker(formula, theory="logos")
    exclusion_result = run_model_checker(formula, theory="exclusion")

    # Different theories may produce different results
    assert logos_result.theory_name == "logos"
    assert exclusion_result.theory_name == "exclusion"
```

---

## 7. Test Coverage Requirements

### 7.1 Coverage Targets

**Minimum Coverage Requirements**:
- **Overall codebase**: ≥85% coverage
- **Critical paths** (semantic evaluation, model iteration): ≥90% coverage
- **Utility functions**: ≥80% coverage
- **Error handling paths**: ≥75% coverage

**Coverage Measurement**:
```bash
# Generate coverage report
PYTHONPATH=Code/src pytest --cov=model_checker --cov-report=term-missing --cov-report=html

# View HTML report
# Open htmlcov/index.html in browser
```

### 7.2 What to Cover

**Must be tested**:
- All public API methods
- All semantic operators
- All error conditions
- All configuration options
- All file I/O operations

**Can skip testing**:
- Simple getters/setters with no logic
- Third-party library code
- Generated code (if any)

### 7.3 Coverage Gaps

When coverage is below target:
1. Identify uncovered lines with `--cov-report=term-missing`
2. Write tests for uncovered code
3. If code is truly untestable, refactor to make it testable
4. Document any intentional coverage exclusions

---

## 8. Best Practices and Patterns

### 8.1 Test Naming Conventions

Follow consistent naming:
- `test_<feature>_<condition>_<expected_outcome>()`
- Examples:
  - `test_loader_accepts_valid_package_marker()`
  - `test_semantic_rejects_invalid_formula()`
  - `test_iterator_finds_all_models_within_size_limit()`

### 8.2 Fixtures and Test Utilities

Use pytest fixtures for reusable test setup:

```python
import pytest

@pytest.fixture
def sample_theory():
    """Provide a sample theory instance for testing."""
    return LogosSemantic()

@pytest.fixture
def temp_package_dir(tmp_path):
    """Create a temporary package directory for testing."""
    package_dir = tmp_path / "test_package"
    package_dir.mkdir()
    (package_dir / ".modelchecker").write_text("package=true\n")
    return package_dir

def test_uses_fixtures(sample_theory, temp_package_dir):
    """Test using fixtures for setup."""
    # Test implementation uses sample_theory and temp_package_dir
    pass
```

### 8.3 Testing Error Conditions

Always test that errors are raised appropriately:

```python
def test_semantic_raises_error_on_undefined_operator():
    """Test that using undefined operator raises clear error."""
    semantic = LogosSemantic()

    with pytest.raises(ValueError) as exc_info:
        semantic.evaluate("undefined_operator(p, q)")

    assert "undefined_operator" in str(exc_info.value).lower()
    assert "not supported" in str(exc_info.value).lower()
```

### 8.4 Parametrized Tests

Use parametrization to test multiple cases efficiently:

```python
@pytest.mark.parametrize("formula,expected_valid", [
    ("p > p", True),           # Reflexivity
    ("p > q", False),          # Not tautology
    ("(p & q) > p", True),     # Simplification
    ("p > (p | q)", True),     # Addition
])
def test_logos_validates_propositional_principles(formula, expected_valid):
    """Test various propositional logic principles."""
    result = check_validity([], formula, theory="logos")
    assert result.is_valid == expected_valid, \
        f"Formula '{formula}' validity should be {expected_valid}"
```

### 8.5 Performance Testing

For performance-critical code, include timing assertions:

```python
import time

def test_iteration_completes_within_time_limit():
    """Test that model iteration completes within reasonable time."""
    start = time.time()

    result = iterate_models(formula, max_size=10)

    duration = time.time() - start
    assert duration < 5.0, f"Iteration took {duration}s, should complete in <5s"
```

### 8.6 Regression Testing

For bug fixes, always add regression tests:

```python
def test_regression_issue_73_package_loading():
    """Test that package loading works after Issue #73 fix.

    Issue #73: Package loading failed when .modelchecker missing 'package=true'
    Fix: Added validation and clear error message

    This test ensures the fix remains effective.
    """
    # Test implementation that would have failed before fix
    package_dir = create_package_without_marker()

    with pytest.raises(ImportError) as exc_info:
        load_package(package_dir)

    assert "package=true" in str(exc_info.value).lower()
```

---

## Quick Reference

### Common Testing Tasks

| Task | Command |
|------|---------|
| Run all tests | `PYTHONPATH=Code/src pytest Code/tests/ -v` |
| Run specific theory | `PYTHONPATH=Code/src pytest Code/src/model_checker/theory_lib/logos/tests/ -v` |
| Check coverage | `PYTHONPATH=Code/src pytest --cov=model_checker --cov-report=term-missing` |
| Run one test | `PYTHONPATH=Code/src pytest path/to/test.py::test_function_name -v` |
| Stop on first failure | `PYTHONPATH=Code/src pytest -x` |
| Show local vars | `PYTHONPATH=Code/src pytest -l` |

### TDD Workflow Quick Reference

1. **RED**: Write failing test
2. **GREEN**: Minimal implementation
3. **REFACTOR**: Improve code quality
4. **REPEAT**: Next requirement

### Coverage Targets

- Overall: ≥85%
- Critical paths: ≥90%
- Utilities: ≥80%
- Error handling: ≥75%

---

## See Also

- [Code Standards](CODE_STANDARDS.md) - Python coding conventions
- [Development Workflow](../implementation/DEVELOPMENT_WORKFLOW.md) - Feature development process
- [Architecture](ARCHITECTURE.md) - System design patterns
- [Manual Testing](../quality/MANUAL_TESTING.md) - Integration and acceptance testing
- [Quality Metrics](../quality/METRICS.md) - Quality measurement and targets

[← Code Standards](CODE_STANDARDS.md) | [Back to Core](README.md) | [Architecture →](ARCHITECTURE.md)
