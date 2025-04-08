# Model-Checker Unit Testing

## Current Testing Architecture

The ModelChecker project implements a multi-layered testing approach with tests at both the theory level and project level. This section provides an overview of the current testing architecture.

### Theory-Level Tests

Each theory in the `theory_lib` directory follows a consistent testing pattern:

#### Test Directory Structure

```
theory_lib/
├── default/
│   ├── test/
│   │   └── test_default.py
├── exclusion/
│   ├── test/
│   │   └── test_exclusion.py
└── imposition/
    ├── test/
    │   └── test_imposition.py
```

#### Test Implementation Pattern

Each theory's test file follows a similar pattern, using pytest's parametrization to test all examples defined in that theory:

```python
@pytest.mark.parametrize("example_name, example_case", test_example_range.items())
def test_example_cases(example_name, example_case):
    """Test each example case from example_range."""
    result = run_test(
        example_case,
        TheorySemantics,
        TheoryProposition,
        theory_operators,
        Syntax,
        ModelConstraints,
        TheoryModelStructure,
    )
    assert result, f"Test failed for example: {example_name}"
```

#### Example Data

Test cases are defined in each theory's `examples.py` file, specifically in the `test_example_range` dictionary. Each test case consists of:

1. Premises: List of formulas serving as assumptions
2. Conclusions: List of formulas to test
3. Settings: Dictionary with parameters (N, contingent, disjoint, etc.)
4. Expectation: Expected result (True/False)

### Project-Level Tests

The project also has higher-level tests in the main `test/` directory:

```
test/
├── __init__.py
├── README.md
├── t_champollion.py
├── t_constitutive.py
├── t_defined.py
├── t_extensional.py
├── t_imposition.py
├── t_modals.py
├── t_relevance.py
└── utils.py
```

These tests appear to:

1. Test specific logical features (modals, constitutive operators, etc.)
2. Use a shared utility module for common testing functionality
3. Create custom operator collections for specialized testing

The `utils.py` file provides helper functions like:
- `find_model_structure`: Creates a model structure for testing
- `check_model_status`: Verifies that a model has the expected status
- `failure_message`: Generates descriptive error messages

### Test Configuration

The project uses a `pytest.ini` file for configuration:

```ini
[pytest]
# Add the src directory to the Python path
pythonpath = src

# Specify directories to search for tests
testpaths = src/model_checker/theory_lib
python_files = test_*.py
python_classes = Test*

# runs the test no matter how long it takes
addopts = --durations=0 -v --import-mode=importlib
```

This configuration:
- Sets up the Python path to include the `src` directory
- Specifies that tests should be searched for in the `theory_lib` directory
- Sets naming conventions for test files and classes
- Configures pytest to run without time limits and in verbose mode

### Current Testing Workflow

Tests can be run using:

```bash
# Run all tests
pytest

# Run tests for a specific theory
pytest src/model_checker/theory_lib/default/test/

# Run a specific test case
pytest src/model_checker/theory_lib/default/test/test_default.py -k "example_name"

# Run tests with detailed output
pytest -v src/model_checker/theory_lib/default/test/test_default.py

# Run tests with real-time progress
pytest -v src/model_checker/theory_lib/default/test/test_default.py --capture=no
```

### Testing Strengths

1. **Consistent Pattern**: Each theory follows the same testing approach
2. **Parameterized Tests**: Uses pytest's parametrization for efficient test definition
3. **Detailed Output**: Provides informative error messages for failed tests
4. **Flexible Configuration**: pytest.ini allows for customized test behavior
5. **Theory-Specific Tests**: Each theory has its own dedicated test file

### Testing Limitations

1. **Limited Integration Testing**: Tests focus on individual theories without extensive cross-theory testing
2. **Manual Example Definition**: Test cases need to be manually defined in the examples files
3. **Minimal Fixture Usage**: Limited use of pytest fixtures for setup/teardown
4. **Limited Coverage Reporting**: No explicit test coverage tracking
5. **Minimal Documentation**: Limited documentation on testing approach and methodology

## Testing Improvement Recommendations

Based on the analysis of the current testing architecture, here are recommendations for improving the ModelChecker testing approach:

### Short-Term Improvements

1. **Centralized Test Utilities**

   Create a shared test utility module in `theory_lib/test_utils.py` that all theory tests can use:

   ```python
   # theory_lib/test_utils.py
   import pytest
   from model_checker import ModelConstraints, Syntax, run_test

   def run_theory_test(example_case, theory_semantics, theory_proposition, 
                      theory_operators, theory_model_structure):
       """Run a test for a specific theory with appropriate error reporting."""
       result = run_test(
           example_case,
           theory_semantics,
           theory_proposition,
           theory_operators,
           Syntax,
           ModelConstraints,
           theory_model_structure,
       )
       return result
   
   def parametrize_theory_tests(theory_name):
       """Create a pytest parametrize decorator for a theory's examples."""
       def decorator(func):
           module_path = f"model_checker.theory_lib.{theory_name}.examples"
           module = __import__(module_path, fromlist=["test_example_range"])
           test_examples = module.test_example_range
           return pytest.mark.parametrize("example_name,example_case", 
                                         test_examples.items())(func)
       return decorator
   ```

2. **Test Categorization**

   Use pytest markers to categorize tests:

   ```python
   # In pytest.ini
   [pytest]
   markers =
       countermodel: Tests that verify a countermodel exists
       theorem: Tests that verify a formula is a theorem
       performance: Tests that verify performance characteristics
   ```

   ```python
   # In test files
   @pytest.mark.countermodel
   @parametrize_theory_tests("default")
   def test_countermodel_examples(example_name, example_case):
       if "CM" in example_name:  # It's a countermodel test
           result = run_theory_test(...)
           assert result, f"Failed to find countermodel for: {example_name}"
   ```

3. **Verbose Test Output**

   Enhance test output with more detailed information:

   ```python
   def test_example_cases(example_name, example_case):
       """Test each example case from example_range."""
       premises, conclusions, settings = example_case
       
       # Print details before test runs
       print(f"\nTesting {example_name}:")
       print(f"  Premises: {premises}")
       print(f"  Conclusions: {conclusions}")
       print(f"  Settings: {settings}")
       
       result = run_theory_test(...)
       
       # Print detailed result
       print(f"  Result: {'PASS' if result else 'FAIL'}")
       
       assert result, f"Test failed for example: {example_name}"
   ```

### Medium-Term Improvements

1. **Fixtures for Common Setup**

   Use pytest fixtures to set up common test components:

   ```python
   @pytest.fixture
   def default_theory():
       """Fixture providing all components of the default theory."""
       from model_checker.theory_lib.default import (
           Semantics, Proposition, ModelStructure, default_operators
       )
       return {
           "semantics": Semantics,
           "proposition": Proposition,
           "model_structure": ModelStructure,
           "operators": default_operators,
       }
   
   def test_with_fixture(default_theory, example_name, example_case):
       result = run_theory_test(
           example_case,
           default_theory["semantics"],
           default_theory["proposition"],
           default_theory["operators"],
           default_theory["model_structure"],
       )
       assert result
   ```

2. **Property-Based Testing**

   Implement property-based testing with hypothesis to test theory properties:

   ```python
   from hypothesis import given, strategies as st
   
   # Define strategies for generating formulas
   atomic_formulas = st.sampled_from(["p", "q", "r", "s", "t"])
   
   @st.composite
   def simple_formulas(draw):
       """Generate simple logical formulas."""
       formula_type = draw(st.integers(min_value=0, max_value=3))
       if formula_type == 0:
           # Atomic formula
           return draw(atomic_formulas)
       elif formula_type == 1:
           # Negation
           subformula = draw(simple_formulas())
           return f"\\neg {subformula}"
       elif formula_type == 2:
           # Conjunction
           left = draw(simple_formulas())
           right = draw(simple_formulas())
           return f"({left} \\wedge {right})"
       else:
           # Disjunction
           left = draw(simple_formulas())
           right = draw(simple_formulas())
           return f"({left} \\vee {right})"
   
   @given(formula=simple_formulas())
   def test_excluded_middle(formula, default_theory):
       """Test the law of excluded middle for any formula."""
       example_case = [
           [],  # premises
           [f"({formula} \\vee \\neg {formula})"],  # conclusions
           {"N": 3, "max_time": 5, "expectation": False}
       ]
       result = run_theory_test(...)
       assert result, f"Law of excluded middle failed for {formula}"
   ```

3. **Cross-Theory Testing**

   Create tests that verify consistent behavior across theories:

   ```python
   @pytest.mark.parametrize("theory_name", ["default", "exclusion", "imposition"])
   def test_common_principles(theory_name):
       """Test that certain logical principles hold across all theories."""
       # Import theory components
       if theory_name == "default":
           from model_checker.theory_lib.default import ...
       elif theory_name == "exclusion":
           from model_checker.theory_lib.exclusion import ...
       # ...
       
       # Test cases all theories should satisfy
       principles = [
           ([], ["(p \\vee \\neg p)"], "Law of excluded middle"),
           ([], ["(p -> p)"], "Identity principle"),
           # ...
       ]
       
       for premises, conclusions, principle_name in principles:
           example_case = [premises, conclusions, {"N": 3, "max_time": 5}]
           result = run_theory_test(...)
           assert result, f"{principle_name} failed in {theory_name} theory"
   ```

### Long-Term Improvements

1. **Automated Test Generation**

   Create a framework for automatically generating tests based on theory properties:

   ```python
   class TheoryTestGenerator:
       """Generates tests for theories based on their properties."""
       
       def __init__(self, theory_name, operator_properties=None):
           self.theory_name = theory_name
           self.properties = operator_properties or {}
           
       def generate_test_cases(self):
           """Generate test cases based on operator properties."""
           test_cases = {}
           
           # Generate tests for each operator property
           for operator, properties in self.properties.items():
               if "associative" in properties:
                   test_cases[f"{operator}_associativity"] = self._generate_associativity_test(operator)
               if "commutative" in properties:
                   test_cases[f"{operator}_commutativity"] = self._generate_commutativity_test(operator)
               # ...
               
           return test_cases
           
       def _generate_associativity_test(self, operator):
           """Generate test for associativity property."""
           # ...
   ```

2. **Comprehensive Test Suite**

   Develop a comprehensive test suite covering all aspects of logical theories:

   - **Syntax Tests**: Verify parsing and normalization
   - **Semantics Tests**: Verify semantic evaluations
   - **Operator Tests**: Verify specific operator behaviors
   - **Performance Tests**: Verify time and space complexity
   - **Integration Tests**: Verify cross-theory consistency
   - **Edge Case Tests**: Verify behavior with extreme examples

3. **Test Coverage Reporting**

   Implement test coverage tracking with pytest-cov:

   ```ini
   # In pytest.ini
   [pytest]
   addopts = --cov=model_checker --cov-report=html --cov-report=term
   ```

   Ensure coverage reports for:
   - Line coverage: Basic code execution
   - Branch coverage: Decision points
   - Path coverage: All possible execution paths

4. **Continuous Integration**

   Set up a CI/CD pipeline for automated testing:

   ```yaml
   # .github/workflows/test.yml
   name: Tests
   
   on:
     push:
       branches: [ main ]
     pull_request:
       branches: [ main ]
   
   jobs:
     test:
       runs-on: ubuntu-latest
       steps:
       - uses: actions/checkout@v2
       - name: Set up Python
         uses: actions/setup-python@v2
         with:
           python-version: '3.x'
       - name: Install dependencies
         run: |
           python -m pip install --upgrade pip
           pip install -e ".[test]"
       - name: Test with pytest
         run: |
           pytest --cov=model_checker
       - name: Upload coverage reports
         uses: codecov/codecov-action@v1
   ```

5. **Testing Documentation**

   Create comprehensive testing documentation:

   - Test plan: Strategies and approaches
   - Test cases: Detailed descriptions of each test case
   - Test coverage: Maps between requirements and tests
   - Test results: Detailed reports of test outcomes

### Implementation Strategy

To implement these improvements, follow this phased approach:

1. **Phase 1**: Implement short-term improvements to make testing more consistent and informative
2. **Phase 2**: Introduce medium-term improvements to enhance test quality and coverage
3. **Phase 3**: Implement long-term improvements for comprehensive and automated testing

By following this strategy, you can gradually enhance the testing architecture while maintaining backward compatibility with the existing tests.

## Implementation Plan for Short-Term Improvements and Fixtures

### 1. Create Centralized Test Utilities Module

**File**: `src/model_checker/theory_lib/test_utils.py`

```python
"""Centralized test utilities for ModelChecker theories."""

import importlib
import pytest
from model_checker import ModelConstraints, Syntax, run_test
from model_checker.theory_lib import AVAILABLE_THEORIES

def run_theory_test(example_case, theory_semantics, theory_proposition, 
                   theory_operators, theory_model_structure,
                   verbose=False):
    """
    Run a test for a specific theory with appropriate error reporting.
    
    Args:
        example_case: List containing [premises, conclusions, settings]
        theory_semantics: The semantics class for the theory
        theory_proposition: The proposition class for the theory
        theory_operators: The operators dictionary for the theory
        theory_model_structure: The model structure class for the theory
        verbose: Whether to print detailed test information
        
    Returns:
        bool: Test result (True for success, False for failure)
    """
    premises, conclusions, settings = example_case
    
    if verbose:
        print("\nRunning test:")
        print(f"  Premises: {premises}")
        print(f"  Conclusions: {conclusions}")
        print(f"  Settings: {settings}")
    
    # Run the test
    result = run_test(
        example_case,
        theory_semantics,
        theory_proposition,
        theory_operators,
        Syntax,
        ModelConstraints,
        theory_model_structure,
    )
    
    if verbose:
        print(f"  Result: {'PASS' if result else 'FAIL'}")
    
    return result

def parametrize_theory_tests(theory_name, example_filter=None):
    """
    Create a pytest parametrize decorator for a theory's examples.
    
    Args:
        theory_name: Name of the theory (e.g., 'default', 'exclusion')
        example_filter: Optional function to filter examples by name
        
    Returns:
        Decorator function for parametrizing tests
    """
    def decorator(func):
        # Import the relevant test examples
        module_path = f"model_checker.theory_lib.{theory_name}.examples"
        module = __import__(module_path, fromlist=["test_example_range"])
        test_examples = module.test_example_range
        
        # Filter examples if a filter is provided
        if example_filter:
            test_examples = {name: test_examples[name] for name in test_examples 
                           if example_filter(name)}
        
        # Apply parametrization to the test function
        return pytest.mark.parametrize("example_name,example_case", 
                                     test_examples.items())(func)
    
    return decorator

def extract_test_info(example_name, example_case):
    """
    Extract relevant information from a test example for better reporting.
    
    Args:
        example_name: Name of the example
        example_case: The example case data [premises, conclusions, settings]
        
    Returns:
        dict: Dictionary with test metadata
    """
    premises, conclusions, settings = example_case
    
    # Determine test type from example name and settings
    test_type = "unknown"
    if "CM" in example_name:
        test_type = "countermodel"
    elif "TH" in example_name:
        test_type = "theorem"
    elif "expectation" in settings:
        test_type = "countermodel" if not settings["expectation"] else "theorem"
    
    # Extract theorem type if available
    theorem_type = None
    for prefix in ["neg", "and", "or", "imp", "box", "diamond", "cf"]:
        if example_name.startswith(prefix):
            theorem_type = prefix
    
    return {
        "name": example_name,
        "type": test_type,
        "theorem_type": theorem_type,
        "premises_count": len(premises),
        "conclusions_count": len(conclusions),
        "settings": settings
    }

def get_theory_components(theory_name):
    """
    Load and return the components of a theory by name.
    
    Args:
        theory_name: Name of the theory (e.g., 'default', 'exclusion')
        
    Returns:
        dict: Dictionary containing semantics, proposition, operators, and model_structure
    """
    if theory_name not in AVAILABLE_THEORIES:
        raise ValueError(f"Unknown theory: {theory_name}")
    
    try:
        # Use dynamic imports to get theory components
        module = importlib.import_module(f"model_checker.theory_lib.{theory_name}")
        
        # Get theory component names (different theories may use different naming conventions)
        component_map = {
            "default": {
                "semantics": "Semantics",
                "proposition": "Proposition",
                "model_structure": "ModelStructure",
                "operators": "default_operators"
            },
            "exclusion": {
                "semantics": "ExclusionSemantics",
                "proposition": "UnilateralProposition",
                "model_structure": "ExclusionStructure",
                "operators": "exclusion_operators"
            },
            "imposition": {
                "semantics": "ImpositionSemantics",
                "proposition": "ImpositionProposition",
                "model_structure": "ImpositionStructure",
                "operators": "imposition_operators"
            },
            "bimodal": {
                "semantics": "Semantics",
                "proposition": "Proposition",
                "model_structure": "ModelStructure",
                "operators_func": "get_bimodal_operators"
            }
        }
        
        # Get default component names if not explicitly mapped
        component_names = component_map.get(theory_name, {
            "semantics": "Semantics",
            "proposition": "Proposition",
            "model_structure": "ModelStructure",
            "operators": f"{theory_name}_operators"
        })
        
        # Import components
        result = {}
        for component, attr_name in component_names.items():
            if component == "operators_func":
                # Special case for functions that return operators
                func = getattr(module, attr_name)
                result["operators"] = func()
            else:
                result[component] = getattr(module, attr_name)
        
        return result
    except (ImportError, AttributeError) as e:
        raise ValueError(f"Failed to load components for theory '{theory_name}': {str(e)}")
```

### 2. Update pytest.ini with Test Markers

**File**: `/home/benjamin/Documents/Philosophy/Projects/ModelChecker/Code/pytest.ini`

```ini
[pytest]
# Add the src directory to the Python path
pythonpath = src

# Specify directories to search for tests
testpaths = src/model_checker/theory_lib
python_files = test_*.py
python_classes = Test*

# runs the test no matter how long it takes
addopts = --durations=0 -v --import-mode=importlib

# Test markers
markers =
    countermodel: Tests that verify a countermodel exists
    theorem: Tests that verify a formula is a theorem
    performance: Tests that verify performance characteristics
    basic: Basic logical principles
    modal: Modal logical principles
    counterfactual: Counterfactual logical principles
    imposition: Imposition logical principles
```

### 3. Create Test Fixtures Module

**File**: `src/model_checker/theory_lib/test_fixtures.py`

```python
"""Test fixtures for ModelChecker testing."""

import pytest
from model_checker import ModelConstraints, Syntax
from model_checker.theory_lib import AVAILABLE_THEORIES
from model_checker.theory_lib.test_utils import get_theory_components

# Define a fixture for each available theory
def _create_theory_fixture(theory_name):
    """Create a pytest fixture for a theory."""
    @pytest.fixture
    def theory_fixture():
        """Fixture providing components for the {theory_name} theory."""
        components = get_theory_components(theory_name)
        components["name"] = theory_name
        return components
    
    # Set proper name and docstring for the fixture
    theory_fixture.__name__ = f"{theory_name}_theory"
    theory_fixture.__doc__ = f"Fixture providing all components of the {theory_name} theory."
    
    return theory_fixture

# Dynamically create fixtures for all available theories
THEORY_FIXTURES = {}
for theory_name in AVAILABLE_THEORIES:
    fixture = _create_theory_fixture(theory_name)
    globals()[f"{theory_name}_theory"] = fixture
    THEORY_FIXTURES[theory_name] = fixture

@pytest.fixture
def model_components():
    """Fixture providing core model components."""
    return {
        "syntax": Syntax,
        "constraints": ModelConstraints
    }

@pytest.fixture
def test_settings():
    """Fixture providing standard test settings."""
    return {
        "default": {"N": 3, "max_time": 5},
        "performance": {"N": 5, "max_time": 10},
        "complex": {"N": 4, "max_time": 30, "maximize": True}
    }

@pytest.fixture
def standard_formulas():
    """Fixture providing standard logical formulas for testing."""
    return {
        "tautology": "p | ~p",
        "contradiction": "p & ~p",
        "modus_ponens": ["p", "p -> q", "q"],
        "modus_tollens": ["~q", "p -> q", "~p"],
        "excluded_middle": ["(p | ~p)"],
        "non_contradiction": ["~(p & ~p)"],
        # Modal formulas
        "K_axiom": ["([]p -> []q)", "[]p", "[]q"],
        "T_axiom": ["[]p -> p"],
        "modal_modus_ponens": ["[]p", "[](p -> q)", "[]q"],
        # Counterfactual formulas
        "cf_identity": ["p > p"],
        "cf_modus_ponens": ["p", "p > q", "q"],
        "cf_contraposition": ["~q > ~p", "p > q"],
    }

# Add a fixture that provides all available theories
@pytest.fixture
def all_theories():
    """Fixture providing all available theories."""
    result = {}
    for theory_name in AVAILABLE_THEORIES:
        fixture_func = globals()[f"{theory_name}_theory"]
        result[theory_name] = fixture_func()
    return result
```

### 4. Example Test File Implementation (Default Theory)

**File**: `src/model_checker/theory_lib/default/test/test_default.py`

```python
"""
Test cases for the default theory.
Uses the centralized test utilities and fixtures.
"""

import pytest
from model_checker.theory_lib.test_utils import (
    run_theory_test, parametrize_theory_tests, extract_test_info, get_theory_components
)
from model_checker.theory_lib import AVAILABLE_THEORIES

# Basic test with centralized utilities
@parametrize_theory_tests("default")
def test_all_examples(example_name, example_case):
    """Test all examples from default theory."""
    # Get test type and apply appropriate marker dynamically
    test_info = extract_test_info(example_name, example_case)
    
    # Get theory components dynamically
    components = get_theory_components("default")
    
    # Set up verbose output
    premises, conclusions, settings = example_case
    print(f"\nTesting {example_name} ({test_info['type']}):")
    print(f"  Premises: {premises}")
    print(f"  Conclusions: {conclusions}")
    print(f"  Settings: {settings}")
    
    # Run the test with the utility function
    result = run_theory_test(
        example_case,
        components["semantics"],
        components["proposition"],
        components["operators"],
        components["model_structure"],
        verbose=True
    )
    
    # Assertion with detailed message
    expected = settings.get("expectation", True)
    assert result == expected, (
        f"Test failed for {example_name}. "
        f"Expected {'success' if expected else 'failure'}, "
        f"got {'success' if result else 'failure'}"
    )

# Using the fixture-based approach
@pytest.mark.theorem
@parametrize_theory_tests("default", lambda name: "TH" in name)
def test_theorems(default_theory, model_components, example_name, example_case):
    """Test theorem examples from default theory using fixtures."""
    result = run_theory_test(
        example_case,
        default_theory["semantics"],
        default_theory["proposition"],
        default_theory["operators"],
        default_theory["model_structure"],
        verbose=True
    )
    assert result, f"Theorem test failed for {example_name}"

@pytest.mark.countermodel
@parametrize_theory_tests("default", lambda name: "CM" in name)
def test_countermodels(default_theory, model_components, example_name, example_case):
    """Test countermodel examples from default theory using fixtures."""
    result = run_theory_test(
        example_case,
        default_theory["semantics"],
        default_theory["proposition"],
        default_theory["operators"],
        default_theory["model_structure"],
        verbose=True
    )
    assert result, f"Countermodel test failed for {example_name}"

# Test specific logical principle categories
@pytest.mark.basic
def test_basic_principles(default_theory, standard_formulas, test_settings):
    """Test basic logical principles in default theory."""
    principles = [
        ([], [standard_formulas["tautology"]], "Tautology"),
        ([], [standard_formulas["excluded_middle"]], "Excluded Middle"),
        ([], [standard_formulas["non_contradiction"]], "Non-Contradiction"),
        (standard_formulas["modus_ponens"][:2], [standard_formulas["modus_ponens"][2]], "Modus Ponens"),
    ]
    
    for premises, conclusions, principle_name in principles:
        example_case = [premises, conclusions, test_settings["default"]]
        result = run_theory_test(
            example_case,
            default_theory["semantics"],
            default_theory["proposition"],
            default_theory["operators"],
            default_theory["model_structure"],
            verbose=True
        )
        assert result, f"{principle_name} principle failed in {default_theory['name']} theory"

# Cross-theory test that works with all available theories
@pytest.mark.parametrize("theory_name", AVAILABLE_THEORIES)
def test_theory_excluded_middle(theory_name, all_theories, standard_formulas, test_settings):
    """Test law of excluded middle across all theories."""
    if theory_name not in all_theories:
        pytest.skip(f"Theory {theory_name} not available")
    
    theory = all_theories[theory_name]
    example_case = [[], [standard_formulas["excluded_middle"]], test_settings["default"]]
    
    result = run_theory_test(
        example_case,
        theory["semantics"],
        theory["proposition"],
        theory["operators"],
        theory["model_structure"],
        verbose=True
    )
    
    assert result, f"Excluded middle principle failed in {theory_name} theory"
```

### 5. Implementation Steps

1. **Update Theory Registry in theory_lib/__init__.py**
   - Implement the centralized `AVAILABLE_THEORIES` registry
   - Refactor utility functions to use this registry
   - Implement dynamic theory loading with `__getattr__`
   - Add the `discover_theories()` function for development

2. **Create the Test Utilities Module**
   - Add `test_utils.py` to `src/model_checker/theory_lib/`
   - Implement the core testing utilities using the theory registry
   - Create a flexible `get_theory_components()` function that works with any theory

3. **Update pytest.ini**
   - Add the new test markers for categorizing tests
   - Verify that the configuration options are correct for the project

4. **Create Test Fixtures Module**
   - Add `test_fixtures.py` to `src/model_checker/theory_lib/`
   - Implement dynamic fixture generation for all registered theories
   - Add fixtures for common test components and standard formulas

5. **Update Default Theory Tests**
   - Refactor `default/test/test_default.py` to use the new utilities and fixtures
   - Categorize tests with appropriate markers
   - Add detailed reporting to the test output
   - Implement cross-theory tests that work with all registered theories

6. **Update Remaining Theory Tests**
   - Apply the same pattern to update tests for other theories:
     - `exclusion/test/test_exclusion.py`
     - `imposition/test/test_imposition.py`
     - `bimodal/test/test_bimodal.py` (if applicable)

7. **Documentation**
   - Add comments to document the usage of the new testing utilities
   - Document the theory registry and how to add new theories
   - Update any test-related documentation in README files

8. **Testing the Registry**
   - Verify that dynamic discovery of theories works correctly
   - Test that all utility functions work with the registry
   - Ensure that lazy loading still functions as expected

### 6. Expected Benefits

1. **Consistent Testing Approach**
   - All theories will use the same testing patterns and utilities
   - Tests will have consistent output and behavior

2. **Reduced Code Duplication**
   - Common testing logic extracted to shared utilities
   - Each theory's test file becomes simpler and more focused

3. **Better Test Organization**
   - Tests categorized with markers for easier filtering
   - Logical organization of test cases by type

4. **More Informative Output**
   - Enhanced reporting of test details and results
   - Better debugging information when tests fail

5. **Easier Test Creation**
   - Simplified pattern for creating new tests
   - Fixtures for common test setup

6. **Improved Maintainability**
   - Centralized logic for changes to testing approach
   - Easier to extend with new features

With this implementation plan, we establish a solid foundation for improving the testing architecture while maintaining backward compatibility with the existing test cases.

## Running Tests from the ModelChecker/ Directory

### Options for Running Centralized Tests for All Registered Theories

There are several approaches to configure pytest to discover and run all tests for registered theories from the root ModelChecker/ directory.

### Option 1: Dedicated Test Runner Script

**File**: `ModelChecker/run_tests.py`

```python
#!/usr/bin/env python3
"""Test runner script for ModelChecker.

This script discovers and runs tests for all registered theories.
"""

import sys
import os
import pytest
import importlib.util

# Ensure src is in the Python path
src_path = os.path.join(os.path.dirname(__file__), 'Code', 'src')
sys.path.insert(0, src_path)

# Import the theory registry
try:
    from model_checker.theory_lib import AVAILABLE_THEORIES
except ImportError:
    print("Error: Could not import theory registry. Make sure the path is correct.")
    sys.exit(1)

def main():
    """Run tests for all registered theories."""
    # Print available theories
    print(f"Available theories: {', '.join(AVAILABLE_THEORIES)}")
    
    # Build the list of test directories
    test_paths = []
    for theory in AVAILABLE_THEORIES:
        theory_test_path = os.path.join(src_path, 'model_checker', 'theory_lib', theory, 'test')
        if os.path.exists(theory_test_path):
            test_paths.append(theory_test_path)
    
    # Add any additional test directories
    test_paths.append(os.path.join(src_path, 'model_checker', 'theory_lib', 'test'))
    
    print(f"Discovering tests in: {', '.join(test_paths)}")
    
    # Run pytest with the specified paths
    sys.exit(pytest.main(['-v'] + test_paths))

if __name__ == "__main__":
    main()
```

Make the script executable:
```bash
chmod +x run_tests.py
```

Usage:
```bash
# Run from ModelChecker directory
./run_tests.py
```

### Option 2: Custom pytest.ini at Project Root

**File**: `ModelChecker/pytest.ini`

```ini
[pytest]
# Add the src directory to the Python path
pythonpath = Code/src

# Specify directories to search for tests
testpaths = 
    Code/src/model_checker/theory_lib/default/test
    Code/src/model_checker/theory_lib/exclusion/test
    Code/src/model_checker/theory_lib/imposition/test
    Code/src/model_checker/theory_lib/bimodal/test
    Code/src/model_checker/theory_lib/test

# Test file pattern
python_files = test_*.py
python_classes = Test*

# Test options
addopts = --durations=0 -v --import-mode=importlib

# Test markers
markers =
    countermodel: Tests that verify a countermodel exists
    theorem: Tests that verify a formula is a theorem
    performance: Tests that verify performance characteristics
    basic: Basic logical principles
    modal: Modal logical principles
    counterfactual: Counterfactual logical principles
    imposition: Imposition logical principles
```

Usage:
```bash
# Run from ModelChecker directory
pytest
```

### Option 3: Dynamic Test Configuration Script

**File**: `ModelChecker/configure_tests.py`

```python
#!/usr/bin/env python3
"""
Configure pytest for ModelChecker.

This script dynamically generates a pytest.ini file based on the registered theories.
"""

import os
import sys
import importlib.util
import configparser

# Ensure src is in the Python path
src_path = os.path.join(os.path.dirname(__file__), 'Code', 'src')
sys.path.insert(0, src_path)

# Import the theory registry
try:
    from model_checker.theory_lib import AVAILABLE_THEORIES, discover_theories
except ImportError:
    print("Error: Could not import theory registry. Make sure the path is correct.")
    sys.exit(1)

def main():
    """Generate pytest.ini based on available theories."""
    # Get registered theories
    registered_theories = AVAILABLE_THEORIES
    
    # Discover additional theories if available
    try:
        discovered_theories = discover_theories()
        unregistered = [t for t in discovered_theories if t not in registered_theories]
        if unregistered:
            print(f"Note: Found {len(unregistered)} unregistered theories: {', '.join(unregistered)}")
    except Exception as e:
        print(f"Warning: Could not discover additional theories: {e}")
    
    # Create test paths
    test_paths = []
    for theory in registered_theories:
        theory_test_path = os.path.join('Code', 'src', 'model_checker', 'theory_lib', theory, 'test')
        if os.path.exists(os.path.join(os.path.dirname(__file__), theory_test_path)):
            test_paths.append(theory_test_path)
    
    # Add the common test directory
    test_paths.append(os.path.join('Code', 'src', 'model_checker', 'theory_lib', 'test'))
    
    # Create pytest configuration
    config = configparser.ConfigParser()
    config['pytest'] = {
        'pythonpath': 'Code/src',
        'testpaths': '\n    ' + '\n    '.join(test_paths),
        'python_files': 'test_*.py',
        'python_classes': 'Test*',
        'addopts': '--durations=0 -v --import-mode=importlib',
        'markers': '\n    countermodel: Tests that verify a countermodel exists\n'
                  '    theorem: Tests that verify a formula is a theorem\n'
                  '    performance: Tests that verify performance characteristics\n'
                  '    basic: Basic logical principles\n'
                  '    modal: Modal logical principles\n'
                  '    counterfactual: Counterfactual logical principles\n'
                  '    imposition: Imposition logical principles'
    }
    
    # Write the configuration to pytest.ini
    with open('pytest.ini', 'w') as f:
        config.write(f)
    
    print(f"Generated pytest.ini with {len(test_paths)} test paths")
    print(f"Run 'pytest' to execute tests for all registered theories")

if __name__ == "__main__":
    main()
```

Usage:
```bash
# Generate pytest.ini
./configure_tests.py

# Run tests
pytest
```

### Option 4: Python Module-Based Approach

This approach relies on pytest's ability to run tests from a Python module.

**File**: `ModelChecker/Code/src/model_checker/theory_lib/test/__init__.py`

```python
"""Test package for ModelChecker theories."""
```

**File**: `ModelChecker/Code/src/model_checker/theory_lib/test/test_all_theories.py`

```python
"""Run tests for all registered theories."""

import pytest
from model_checker.theory_lib import AVAILABLE_THEORIES
from model_checker.theory_lib.test_utils import get_theory_components
from model_checker.theory_lib.test_fixtures import all_theories

@pytest.mark.parametrize("theory_name", AVAILABLE_THEORIES)
def test_theory_basic_principles(theory_name, all_theories, standard_formulas, test_settings):
    """Test basic logical principles across all theories."""
    if theory_name not in all_theories:
        pytest.skip(f"Theory {theory_name} not available")
    
    theory = all_theories[theory_name]
    
    # Define basic principles to test
    principles = [
        ([], ["p | ~p"], "Law of excluded middle"),
        ([], ["~(p & ~p)"], "Law of non-contradiction"),
        ([], ["p -> p"], "Identity principle"),
    ]
    
    for premises, conclusions, principle_name in principles:
        from model_checker.theory_lib.test_utils import run_theory_test
        
        example_case = [premises, conclusions, test_settings["default"]]
        result = run_theory_test(
            example_case,
            theory["semantics"],
            theory["proposition"],
            theory["operators"],
            theory["model_structure"],
            verbose=True
        )
        
        assert result, f"{principle_name} failed in {theory_name} theory"
```

Usage:
```bash
# Run from ModelChecker directory
python -m pytest Code/src/model_checker/theory_lib/test/test_all_theories.py -v
```

### Option 5: Make-Based Approach

**File**: `ModelChecker/Makefile`

```makefile
.PHONY: test test-all test-default test-exclusion test-imposition test-bimodal test-cross-theory

# Set Python path
PYTHONPATH := $(CURDIR)/Code/src

# Paths to test directories
DEFAULT_TESTS := Code/src/model_checker/theory_lib/default/test
EXCLUSION_TESTS := Code/src/model_checker/theory_lib/exclusion/test
IMPOSITION_TESTS := Code/src/model_checker/theory_lib/imposition/test
BIMODAL_TESTS := Code/src/model_checker/theory_lib/bimodal/test
COMMON_TESTS := Code/src/model_checker/theory_lib/test

# Run all tests
test-all: test-default test-exclusion test-imposition test-bimodal test-cross-theory

# Default target
test: test-all

# Run tests for specific theories
test-default:
	PYTHONPATH=$(PYTHONPATH) pytest $(DEFAULT_TESTS) -v

test-exclusion:
	PYTHONPATH=$(PYTHONPATH) pytest $(EXCLUSION_TESTS) -v

test-imposition:
	PYTHONPATH=$(PYTHONPATH) pytest $(IMPOSITION_TESTS) -v

test-bimodal:
	PYTHONPATH=$(PYTHONPATH) pytest $(BIMODAL_TESTS) -v

# Run cross-theory tests
test-cross-theory:
	PYTHONPATH=$(PYTHONPATH) pytest $(COMMON_TESTS) -v
```

Usage:
```bash
# Run all tests
make test

# Run tests for a specific theory
make test-default
```

### Recommendation

For the best combination of flexibility and ease of use, **Option 3: Dynamic Test Configuration Script** is recommended. This approach:

1. Automatically adapts to the registered theories
2. Provides a single command to execute all tests
3. Simplifies test discovery and configuration
4. Allows easy extension when new theories are added
5. Can detect unregistered theories

To implement this option:
1. Create the `configure_tests.py` script in the ModelChecker/ directory
2. Make the script executable
3. Run the script to generate the pytest.ini file
4. Run pytest to execute all tests

With any of these options, you'll be able to run tests for all registered theories from the ModelChecker/ directory, ensuring that all theories in the registry are properly tested.


