# Theory Testing Template

This template provides a standardized approach for implementing comprehensive testing in ModelChecker theories, based on the successful logos theory refactor.

## Overview

The ModelChecker testing framework follows a **dual-testing approach** with **inclusive-by-default** CLI control:

- **Example Tests**: Test the model checker on real logical arguments
- **Unit Tests**: Test individual software components in isolation
- **Inclusive CLI**: Maximum test coverage by default, with restriction flags for targeting

## Directory Structure

Create this exact structure in your theory directory:

```
your_theory/
├── tests/
│   ├── __init__.py
│   ├── conftest.py                  # Pytest fixtures and configuration
│   ├── test_examples/
│   │   ├── __init__.py
│   │   ├── test_{theory}_examples.py     # Unified example testing (main entry)
│   │   ├── test_{subtype1}_examples.py  # Subtype-specific examples
│   │   ├── test_{subtype2}_examples.py  # Subtype-specific examples
│   │   └── ...
│   └── test_unit/
│       ├── __init__.py
│       ├── test_semantic_methods.py     # Semantic classes testing
│       ├── test_operators.py            # Operator implementations
│       ├── test_registry.py             # Operator registry (if applicable)
│       ├── test_proposition.py          # Proposition class testing
│       ├── test_model_structure.py      # Model structure testing
│       └── test_error_conditions.py     # Error handling and edge cases
├── examples.py                      # Main examples with 'unit_tests' variable
├── subtheories/                     # If modular theory
│   ├── subtype1/
│   │   └── examples.py              # Use 'unit_tests' variable
│   └── subtype2/
│       └── examples.py              # Use 'unit_tests' variable
└── ...
```

## Implementation Steps

### Step 1: Standardize Example Variables

All `examples.py` files must use the standardized variable name:

```python
# In your_theory/examples.py and all subtheory examples.py files

# Individual example collections
subtype1_cm_examples = {
    "SUBTYPE1_CM_1": [premises, conclusions, settings],
    "SUBTYPE1_CM_2": [premises, conclusions, settings],
    # ...
}

subtype1_th_examples = {
    "SUBTYPE1_TH_1": [premises, conclusions, settings],
    "SUBTYPE1_TH_2": [premises, conclusions, settings], 
    # ...
}

# REQUIRED: Use 'unit_tests' as the main variable name
unit_tests = {
    **subtype1_cm_examples,
    **subtype1_th_examples,
}
```

**Key Requirements**:
- Use `unit_tests` as the main dictionary name in ALL example files
- Use consistent naming pattern: `{SUBTYPE}_{TYPE}_{NUMBER}`
- Include `expectation` in settings: `True` for countermodel expected, `False` for valid

### Step 2: Create Pytest Configuration

Create `tests/conftest.py`:

```python
"""
Pytest configuration and fixtures for {your_theory} theory testing.
"""

import pytest


@pytest.fixture
def {theory}_theory():
    """Full {theory} theory with all components loaded."""
    from model_checker.theory_lib import {theory}
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

Create `tests/test_examples/test_{theory}_examples.py`:

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
    
    # Create theory with all components
    from model_checker.theory_lib import {theory}
    theory_dict = {theory}.get_theory()
    
    semantics = theory_dict['semantics']
    proposition = theory_dict['proposition']
    model_structure = theory_dict['model']
    operators = theory_dict['operators']
    
    # Run the test
    result = run_test(
        example_case,
        semantics,
        proposition,
        operators,
        Syntax,
        ModelConstraints,
        model_structure,
    )
    
    # Get expected result
    expected = example_case[2].get('expectation', False)
    
    assert result == expected, f"Test failed for example: {example_name}. Expected {expected}, got {result}"
```

### Step 4: Implement Unit Tests

Create comprehensive unit tests in `tests/test_unit/`:

**test_semantic_methods.py**:
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
    
    # Add more semantic tests...


class Test{Theory}Proposition:
    """Test the {Theory}Proposition class."""
    
    def test_proposition_creation(self, {theory}_theory, basic_settings):
        """Test basic proposition creation."""
        semantics = {theory}_theory['semantics'](basic_settings)
        prop = {Theory}Proposition(semantics, "p")
        assert prop is not None
        assert hasattr(prop, 'semantics')
        assert hasattr(prop, 'atom')
    
    # Add more proposition tests...


class Test{Theory}ModelStructure:
    """Test the {Theory}ModelStructure class."""
    
    def test_model_structure_creation(self, {theory}_theory, basic_settings):
        """Test basic model structure creation."""
        semantics = {theory}_theory['semantics'](basic_settings)
        model = {Theory}ModelStructure(semantics)
        assert model is not None
        assert hasattr(model, 'semantics')
    
    # Add more model structure tests...
```

**test_operators.py**:
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
        expected_ops = ["\\neg", "\\wedge", "\\vee", ...]  # Your operators
        
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
    
    # Add more operator tests...
```

### Step 5: Extend test_theories.py

Add theory-specific CLI support to `test_theories.py` by extending the existing pattern:

```python
def add_{theory}_args(parser):
    """Add {theory}-specific argument parsing."""
    {theory}_group = parser.add_argument_group('{theory} testing options')
    
    # Test type restrictions
    {theory}_group.add_argument('--examples', nargs='*', 
                           help='RESTRICT to example tests only. Optionally specify example names')
    {theory}_group.add_argument('--package', action='store_true', 
                           help='RESTRICT to unit/implementation tests only')
    
    # Add theory-specific restrictions based on your subtypes/categories
    # e.g., for different logical domains, operator types, etc.
    
    # Unit test category restrictions
    {theory}_group.add_argument('--semantics', action='store_true',
                           help='RESTRICT to semantic method tests only')
    {theory}_group.add_argument('--operators', action='store_true',
                           help='RESTRICT to operator implementation tests only')
    # Add more as needed...


def build_{theory}_test_command(args, code_dir):
    """Build pytest command for {theory} testing."""
    base_dir = "src/model_checker/theory_lib/{theory}/tests"
    command = ["pytest"]
    
    # Implement filtering logic similar to logos
    # See logos implementation in test_theories.py for reference
    
    return command
```

## CLI Integration

Your theory will automatically support the inclusive-by-default testing approach:

### Basic Usage
```bash
# All theory tests (examples + unit tests)
python test_theories.py --theories {theory}

# Examples only
python test_theories.py --theories {theory} --examples

# Unit tests only  
python test_theories.py --theories {theory} --package
```

### Example-Specific Testing
```bash
# Single example
python test_theories.py --theories {theory} --examples SUBTYPE1_CM_1

# Multiple examples
python test_theories.py --theories {theory} --examples SUBTYPE1_CM_1 SUBTYPE2_TH_1

# Wildcard patterns
python test_theories.py --theories {theory} --examples "SUBTYPE1_*"
```

### Unit Test Categories
```bash
# Specific unit test types
python test_theories.py --theories {theory} --package --operators
python test_theories.py --theories {theory} --package --semantics
```

## Design Principles

Follow these key principles from the project's design philosophy:

### Core Principles
- **Fail Fast**: Let errors occur naturally with clear tracebacks
- **No Duplication**: Single source of truth for each test
- **Clear Data Flow**: Explicit parameter passing
- **Inclusive-by-Default**: Maximum test coverage without explicit flags

### Testing Standards
- **Consistent Naming**: Use standardized variable names (`unit_tests`)
- **Systematic Coverage**: Both example and unit tests for comprehensive validation
- **Granular Control**: Support precise targeting with restriction flags
- **Clean Structure**: Organized directory layout with clear separation

### Quality Assurance
- **No Backward Compatibility**: Prioritize clean code over compatibility
- **Root Cause Analysis**: Address underlying issues, not symptoms
- **Test-Driven Resolution**: Create tests that reproduce bugs before fixing

## Expected Outcomes

Following this template provides:

### Immediate Benefits
- **Clear Test Separation**: Distinct example vs. unit tests
- **No Duplication**: Single location for each type of test
- **Inclusive-by-Default**: Maximum test coverage without explicit flags
- **Flexible Targeting**: Precise testing through restriction flags
- **Fast Debugging**: Run specific examples or components quickly

### Long-term Benefits
- **Consistent Standards**: Project-wide testing methodology
- **Easy Maintenance**: Clear structure for updates and extensions
- **Better Error Detection**: Unit tests catch implementation issues early
- **Improved Development Workflow**: Faster feedback through targeted testing

## References

- **Logos Implementation**: `src/model_checker/theory_lib/logos/tests/`
- **CLI Integration**: `test_theories.py` logos-specific functions
- **Design Philosophy**: `STYLE_GUIDE.md` and `CLAUDE.md`
- **Testing Policy**: `src/model_checker/theory_lib/logos/UNIT_TESTS.md`

This template ensures your theory follows the same high-quality testing standards established by the logos theory refactor.