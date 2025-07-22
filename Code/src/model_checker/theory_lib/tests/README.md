# Theory Library Test Suite

This directory contains tests for the core theory library infrastructure that supports all semantic theories in the ModelChecker framework. These tests focus on cross-theory functionality rather than theory-specific implementations.

## Overview

The theory library tests verify:

- **Metadata Management**: Version tracking, citation files, license generation
- **Theory Discovery**: Automatic loading and registration of theories
- **Cross-Theory Integration**: Compatibility between different semantic theories
- **Infrastructure**: Common functionality that all theories depend on

## Test Structure

### Core Infrastructure Tests

| Test Module | Purpose | Coverage |
|-------------|---------|----------|
| `test_meta_data.py` | Metadata system functionality | Version tracking, citations, licenses |

### Running Tests

#### Via Main Test Runner (Recommended)

```bash
# Run all theory_lib tests
python test_package.py --components theory_lib

# Run with verbose output
python test_package.py --components theory_lib -v

# Run with failfast (stop on first failure)
python test_package.py --components theory_lib -x
```

#### Direct pytest Execution

```bash
# Run all theory_lib tests
pytest src/model_checker/theory_lib/tests/

# Run specific test module
pytest src/model_checker/theory_lib/tests/test_meta_data.py

# Run with detailed output
pytest src/model_checker/theory_lib/tests/ -v -s

# Run specific test class or method
pytest src/model_checker/theory_lib/tests/test_meta_data.py::TestMetadataSystem::test_version_update -v
```

## Theory-Specific Testing

For tests that focus on individual semantic theories and their logical properties, see:

### Logos Theory Tests

**Main Theory:**
- [logos/tests/README.md](../logos/tests/README.md) - Central logos theory testing

**Subtheory Tests:**
- [logos/subtheories/extensional/tests/README.md](../logos/subtheories/extensional/tests/README.md) - Truth-functional operators
- [logos/subtheories/modal/tests/README.md](../logos/subtheories/modal/tests/README.md) - Necessity and possibility operators  
- [logos/subtheories/constitutive/tests/README.md](../logos/subtheories/constitutive/tests/README.md) - Content relations (ground, essence, identity)
- [logos/subtheories/counterfactual/tests/README.md](../logos/subtheories/counterfactual/tests/README.md) - Counterfactual conditionals
- [logos/subtheories/relevance/tests/README.md](../logos/subtheories/relevance/tests/README.md) - Relevance logic

### Other Theory Tests

- [default/tests/README.md](../default/tests/README.md) - Default semantic theory
- [exclusion/tests/README.md](../exclusion/tests/README.md) - Exclusion semantics
- [imposition/tests/README.md](../imposition/tests/README.md) - Imposition semantics  
- [bimodal/tests/README.md](../bimodal/tests/README.md) - Bimodal temporal logic

---

# Theory Testing Framework Guide

This section provides comprehensive testing guidance for implementing tests for semantic theories using the two architectural patterns supported by ModelChecker.

## Testing Framework Overview

The ModelChecker testing framework follows a **dual-testing approach** with **inclusive-by-default** CLI control:

- **Example Tests**: Test the model checker on real logical arguments
- **Unit Tests**: Test individual software components in isolation
- **Inclusive CLI**: Maximum test coverage by default, with restriction flags for targeting

## Architecture-Specific Testing Patterns

Testing structure varies by theory architecture (see [THEORY_ARCHITECTURE.md](../THEORY_ARCHITECTURE.md)):

### Simple Pattern Testing Structure

For theories with unified operator collections (e.g., Exclusion Theory):

```
simple_theory/
├── tests/                           # Single test directory
│   ├── __init__.py
│   ├── conftest.py                  # Pytest fixtures
│   ├── test_examples.py             # All examples in one file
│   ├── test_operators.py            # All operators in one file
│   ├── test_semantic.py             # Semantic methods
│   └── test_integration.py          # Integration tests
├── examples.py                      # Main examples with 'unit_tests' variable
└── ...
```

### Modular Pattern Testing Structure

For theories with subtheory organization (e.g., Logos Theory):

```
modular_theory/
├── tests/                           # Core theory tests
│   ├── __init__.py
│   ├── conftest.py                  # Shared fixtures
│   ├── test_examples/               # Example test organization
│   │   ├── __init__.py
│   │   ├── test_theory_examples.py  # Main entry point
│   │   └── test_integration.py      # Cross-subtheory tests
│   └── test_unit/                   # Core unit tests
│       ├── __init__.py
│       ├── test_semantic_methods.py # Core semantic classes
│       ├── test_registry.py         # Operator registry
│       └── test_integration.py      # Integration tests
├── subtheories/                     # Subtheory-specific tests
│   ├── extensional/
│   │   ├── examples.py              # 'unit_tests' variable
│   │   └── tests/
│   │       ├── test_operators.py    # Subtheory operators
│   │       └── test_examples.py     # Subtheory examples
│   └── modal/
│       ├── examples.py              # 'unit_tests' variable
│       └── tests/
│           ├── test_operators.py    # Subtheory operators
│           └── test_examples.py     # Subtheory examples
├── examples.py                      # Cross-subtheory examples
└── ...
```

## Implementation Guide

### Step 1: Standardize Example Variables

All `examples.py` files must use the standardized variable name regardless of architecture:

```python
# REQUIRED: Use 'unit_tests' as the main variable name in ALL examples.py files

# For Simple Pattern (single examples.py):
unit_tests = {
    "THEORY_CM_1": [premises, conclusions, settings],
    "THEORY_TH_1": [premises, conclusions, settings],
    # ...
}

# For Modular Pattern (main examples.py):
unit_tests = {
    **cross_subtheory_examples,
    **integration_examples,
}

# For Modular Pattern (subtheory examples.py):
unit_tests = {
    "SUBTHEORY_CM_1": [premises, conclusions, settings],
    "SUBTHEORY_TH_1": [premises, conclusions, settings],
    # ...
}
```

**Key Requirements**:
- Use `unit_tests` as the main dictionary name in ALL example files
- Use consistent naming pattern: `{SCOPE}_{TYPE}_{NUMBER}`
- Include `expectation` in settings: `True` for countermodel expected, `False` for valid

### Step 2: Create Pytest Configuration

For both patterns, create `tests/conftest.py`:

```python
"""
Pytest configuration and fixtures for {your_theory} theory testing.
"""

import pytest


@pytest.fixture
def {theory}_theory():
    """Full {theory} theory with all components loaded."""
    from model_checker.theory_lib import {theory}
    
    # Simple Pattern: Direct access
    if hasattr({theory}, 'semantic_theories'):
        return list({theory}.semantic_theories.values())[0]
    
    # Modular Pattern: Use get_theory() function
    return {theory}.get_theory()


@pytest.fixture
def basic_settings():
    """Standard settings for most tests."""
    return {
        'N': 3,
        'max_time': 1,
        'contingent': True,
        'non_null': True,
        'non_empty': True,
        'disjoint': False,
    }


@pytest.fixture
def minimal_settings():
    """Minimal settings for fast tests."""
    return {
        'N': 2,
        'max_time': 1,
    }

# Add theory-specific fixtures as needed
```

### Step 3: Implement Example Tests

#### Simple Pattern Example Testing

Create `tests/test_examples.py` (single file for all examples):

```python
"""
Test runner for all {theory} theory examples.
"""

import pytest
from model_checker import run_test, ModelConstraints, Syntax
from model_checker.theory_lib.{theory}.examples import unit_tests


@pytest.mark.parametrize("example_name, example_case", unit_tests.items())
def test_{theory}_examples(example_name, example_case):
    """Test each {theory} example case."""
    
    # Access theory components (Simple Pattern)
    from model_checker.theory_lib import {theory}
    theory_dict = list({theory}.semantic_theories.values())[0]
    
    semantics = theory_dict['semantics']
    proposition = theory_dict['proposition']
    model_structure = theory_dict['model']
    operators = theory_dict['operators']
    
    # Run the test
    result = run_test(
        example_case, semantics, proposition, operators,
        Syntax, ModelConstraints, model_structure
    )
    
    expected = example_case[2].get('expectation', False)
    assert result == expected, f"Test failed for example: {example_name}. Expected {expected}, got {result}"
```

#### Modular Pattern Example Testing

Create `tests/test_examples/test_{theory}_examples.py` (main entry point):

```python
"""
Test runner for all {theory} theory examples.

This test file runs all examples from the {theory} theory using parametrized testing.
It serves as the main entry point for test_theories.py when running tests for the {theory} theory.
"""

import pytest
from model_checker import run_test, ModelConstraints, Syntax
from model_checker.theory_lib.{theory}.examples import unit_tests


@pytest.mark.parametrize("example_name, example_case", unit_tests.items())
def test_{theory}_examples(example_name, example_case):
    """Test each {theory} example case."""
    
    # Access theory components (Modular Pattern)
    from model_checker.theory_lib import {theory}
    theory_dict = {theory}.get_theory()
    
    semantics = theory_dict['semantics']
    proposition = theory_dict['proposition']
    model_structure = theory_dict['model']
    operators = theory_dict['operators']
    
    # Run the test
    result = run_test(
        example_case, semantics, proposition, operators,
        Syntax, ModelConstraints, model_structure
    )
    
    expected = example_case[2].get('expectation', False)
    assert result == expected, f"Test failed for example: {example_name}. Expected {expected}, got {result}"
```

### Step 4: Implement Unit Tests

#### Simple Pattern Unit Testing

Create unit tests directly in `tests/` for simple theories:

**test_semantic.py**:
```python
"""
Unit tests for {Theory}Semantics functionality.
"""

import pytest
from model_checker.theory_lib.{theory}.semantic import (
    {Theory}Semantics,
    {Theory}Proposition,
    {Theory}ModelStructure,
)


class Test{Theory}Semantics:
    """Test the {Theory}Semantics class."""
    
    def test_semantics_creation(self, {theory}_theory, basic_settings):
        """Test basic semantics creation."""
        semantics = {theory}_theory['semantics'](basic_settings)
        assert semantics is not None
        assert hasattr(semantics, 'N')
        assert semantics.N == basic_settings['N']
    
    # Add semantic method tests specific to your theory


class Test{Theory}Proposition:
    """Test the {Theory}Proposition class."""
    
    def test_proposition_creation(self, {theory}_theory, basic_settings):
        """Test basic proposition creation."""
        semantics = {theory}_theory['semantics'](basic_settings)
        prop = {Theory}Proposition(semantics, "p")
        assert prop is not None
        assert hasattr(prop, 'semantics')
        assert hasattr(prop, 'atom')
    
    # Add proposition tests specific to your theory


class Test{Theory}ModelStructure:
    """Test the {Theory}ModelStructure class."""
    
    def test_model_structure_creation(self, {theory}_theory, basic_settings):
        """Test basic model structure creation."""
        semantics = {theory}_theory['semantics'](basic_settings)
        model = {Theory}ModelStructure(semantics)
        assert model is not None
        assert hasattr(model, 'semantics')
    
    # Add model structure tests specific to your theory
```

#### Modular Pattern Unit Testing

Create comprehensive unit tests in `tests/test_unit/` for modular theories:

**test_semantic_methods.py** (same as above but in `test_unit/` subdirectory)

**test_registry.py** (specific to modular theories):
```python
"""
Unit tests for {Theory}OperatorRegistry functionality.
"""

import pytest
from model_checker.theory_lib.{theory}.operators import {Theory}OperatorRegistry


class Test{Theory}OperatorRegistry:
    """Test the {Theory}OperatorRegistry class."""
    
    def test_registry_creation(self):
        """Test basic registry creation."""
        registry = {Theory}OperatorRegistry()
        assert registry is not None
        assert hasattr(registry, 'load_subtheories')
    
    def test_subtheory_loading(self):
        """Test loading subtheories."""
        registry = {Theory}OperatorRegistry()
        operators = registry.load_subtheories(['extensional'])
        assert operators is not None
        assert len(operators.operator_dictionary) > 0
    
    # Add registry-specific tests
```

**test_operators.py** (for both patterns):
```python
"""
Unit tests for operator implementations.
"""

import pytest


class TestOperatorImplementations:
    """Test operator implementations."""
    
    def test_operators_available(self, {theory}_theory):
        """Test that all expected operators are available."""
        operators = {theory}_theory['operators']
        
        # Define expected operators for your theory
        expected_ops = ["\\neg", "\\wedge", "\\vee"]  # Add your operators
        
        for op_name in expected_ops:
            assert op_name in operators.operator_dictionary
            assert operators.operator_dictionary[op_name] is not None
    
    def test_operator_arities(self, {theory}_theory):
        """Test that operators have correct arities."""
        operators = {theory}_theory['operators']
        
        # Test operator arities
        assert operators.operator_dictionary["\\neg"].arity == 1
        assert operators.operator_dictionary["\\wedge"].arity == 2
        # Add your operator arity tests...
    
    def test_operator_semantic_clauses(self, {theory}_theory, basic_settings):
        """Test that operators have working semantic clauses."""
        operators = {theory}_theory['operators']
        semantics = {theory}_theory['semantics'](basic_settings)
        
        for op_name, operator_class in operators.operator_dictionary.items():
            operator = operator_class()
            assert hasattr(operator, 'semantic_clause')
            assert callable(operator.semantic_clause)
    
    # Add more operator tests specific to your theory...
```

## CLI Integration Patterns

### Simple Pattern Usage
```bash
# All theory tests (examples + unit tests)
python test_theories.py --theories {simple_theory}

# Examples only
python test_theories.py --theories {simple_theory} --examples

# Unit tests only  
python test_theories.py --theories {simple_theory} --package

# Specific unit test types
python test_theories.py --theories {simple_theory} --package --operators
python test_theories.py --theories {simple_theory} --package --semantics
```

### Modular Pattern Usage
```bash
# All theory tests (examples + unit tests across all subtheories)
python test_theories.py --theories {modular_theory}

# Examples only
python test_theories.py --theories {modular_theory} --examples

# Specific subtheories
python test_theories.py --theories {modular_theory} --subtheories extensional modal

# Unit tests only  
python test_theories.py --theories {modular_theory} --package

# Specific unit test types
python test_theories.py --theories {modular_theory} --package --operators
python test_theories.py --theories {modular_theory} --package --registry
```

### Example-Specific Testing (Both Patterns)
```bash
# Single example
python test_theories.py --theories {theory} --examples THEORY_CM_1

# Multiple examples
python test_theories.py --theories {theory} --examples THEORY_CM_1 THEORY_TH_1

# Pattern matching
python test_theories.py --theories {theory} --examples "THEORY_CM_*"
```

## Test Categories

### Infrastructure Tests (This Directory)

Focus on the theory library framework itself:

```python
# Example: Testing metadata management
def test_version_consistency():
    """Verify all theories have consistent version information."""
    # Tests cross-theory version tracking
    
def test_citation_generation():
    """Verify citation files are generated correctly."""
    # Tests bibliography management across theories
```

### Theory Tests (Individual Directories)

Focus on logical properties and semantic correctness:

```python
# Example: Testing logical validity (in theory-specific directories)
def test_modal_k_axiom():
    """Verify K axiom: Box(A implies B) and Box A entail Box B."""
    # Tests theory-specific logical principles
```

## Integration with Main Test Suite

The theory library tests integrate with the broader ModelChecker test infrastructure:

### Test Runners

1. **test_package.py** (includes theory_lib tests):
   - Focuses on framework and infrastructure
   - Includes cross-theory compatibility tests
   - Tests metadata and discovery systems

2. **test_theories.py** (theory-specific):
   - Focuses on logical properties and semantic correctness
   - Tests individual theory implementations
   - Verifies example suites and logical principles

### Discovery and Execution

Tests in this directory are automatically discovered by:

- `test_package.py --components theory_lib` (primary method)
- Direct pytest execution (alternative method)
- IDE test runners (for development)

## Design Principles

### Core Principles
- **Fail Fast**: Let errors occur naturally with clear tracebacks
- **No Duplication**: Single source of truth for each test
- **Clear Data Flow**: Explicit parameter passing
- **Inclusive-by-Default**: Maximum test coverage without explicit flags
- **Architecture Agnostic**: Testing patterns work for both Simple and Modular theories

### Testing Standards
- **Consistent Naming**: Use standardized variable names (`unit_tests`)
- **Systematic Coverage**: Both example and unit tests for comprehensive validation
- **Granular Control**: Support precise targeting with restriction flags
- **Clean Structure**: Organized directory layout appropriate to architecture
- **Pattern Flexibility**: Adapt test organization to theory complexity

### Quality Assurance
- **No Backward Compatibility**: Prioritize clean code over compatibility
- **Root Cause Analysis**: Address underlying issues, not symptoms
- **Test-Driven Resolution**: Create tests that reproduce bugs before fixing
- **Scalable Testing**: Support growth from Simple to Modular patterns

## Development Guidelines

### Adding New Infrastructure Tests

When adding tests for new theory library functionality:

1. **Create test module** in this directory following naming pattern `test_*.py`
2. **Follow existing patterns** from `test_meta_data.py`
3. **Update `__init__.py`** to export new test classes
4. **Document in this README** under appropriate section

### Test Naming Convention

- Test modules: `test_[component].py`
- Test classes: `Test[ComponentName]`
- Test methods: `test_[specific_functionality]`

### Example Structure

```python
"""
Tests for [component] functionality.
"""

import pytest
from model_checker.theory_lib.[component] import [functions]

class Test[ComponentName]:
    """Test suite for [component]."""
    
    def test_[specific_functionality](self):
        """Test description."""
        # Test implementation
        assert [condition]
```

## Expected Outcomes

Following this guidance provides:

### Pattern-Specific Benefits

**Simple Pattern**:
- **Minimal Overhead**: Direct testing structure for focused theories
- **Fast Setup**: Quick test implementation and execution
- **Clear Organization**: Single test directory with logical file separation

**Modular Pattern**:
- **Scalable Testing**: Support for complex theories with many operators
- **Subtheory Isolation**: Independent testing of operator groups
- **Selective Testing**: Target specific subtheories or components

### Universal Benefits
- **Consistent Standards**: Project-wide testing methodology regardless of pattern
- **Easy Maintenance**: Clear structure for updates and extensions
- **Better Error Detection**: Unit tests catch implementation issues early
- **Improved Development Workflow**: Faster feedback through targeted testing
- **Future-Proof Design**: Easy migration between patterns as theories evolve

## Common Issues and Debugging

### Import Path Issues

If tests fail with import errors:

```bash
# Ensure PYTHONPATH is set correctly when running directly
PYTHONPATH=src pytest src/model_checker/theory_lib/tests/

# Or use the main test runner which handles paths automatically
python test_package.py --components theory_lib
```

### Cross-Theory Dependencies

Some infrastructure tests may require multiple theories to be available:

- Tests verify theory discovery across all installed theories
- Metadata tests check consistency across theory versions
- Integration tests validate cross-theory compatibility

### Performance Considerations

Infrastructure tests should be lightweight and fast:

- Focus on API and integration testing rather than heavy computations
- Use mocking for external dependencies when appropriate
- Avoid running full logical model checking in infrastructure tests

## Related Documentation

- [../../TESTS.md](../../../TESTS.md) - Overall testing strategy and guide
- [../README.md](../README.md) - Theory library overview and architecture  
- [../THEORY_ARCHITECTURE.md](../THEORY_ARCHITECTURE.md) - Standard theory structure
- Individual theory README files for theory-specific testing information

## References

- **Simple Pattern Example**: [Exclusion Theory Testing](../exclusion/tests/)
- **Modular Pattern Example**: [Logos Theory Testing](../logos/tests/)
- **Architecture Guidance**: [THEORY_ARCHITECTURE.md](../THEORY_ARCHITECTURE.md)
- **CLI Integration**: `test_theories.py` theory-specific functions
- **Design Philosophy**: [../README.md](../README.md) and [CLAUDE.md](../../CLAUDE.md)

---

This testing infrastructure ensures the reliability and maintainability of the theory library framework while supporting the development of new semantic theories and the integration of existing ones.