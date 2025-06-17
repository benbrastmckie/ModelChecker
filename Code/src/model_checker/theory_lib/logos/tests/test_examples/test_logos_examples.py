"""
Test runner for all logos theory examples.

This test file runs all examples from all logos subtheories using the same pattern 
as the default theory tests. It serves as the main entry point for test_theories.py
when running tests for the logos theory.

The logos theory is modular with examples from:
- Extensional: Truth-functional operators 
- Modal: Necessity and possibility operators
- Constitutive: Ground, essence, and identity operators
- Counterfactual: Counterfactual conditional operators  
- Relevance: Content-sensitive relevance operators

To run these tests:
1. All tests: pytest src/model_checker/theory_lib/logos/tests/test_logos_examples.py
2. Specific test: pytest src/model_checker/theory_lib/logos/tests/test_logos_examples.py -k "EXT_TH_1"
3. Verbose output: pytest -v src/model_checker/theory_lib/logos/tests/test_logos_examples.py
4. Via test runner: ./test_theories.py --theories logos -v
"""

import pytest

from model_checker import (
    ModelConstraints,
    Syntax,
    run_test,
)
from model_checker.theory_lib.logos.semantic import (
    LogosSemantics,
    LogosProposition,
    LogosModelStructure,
)
from model_checker.theory_lib.logos.operators import LogosOperatorRegistry

# Import unified examples from the main logos examples module
from model_checker.theory_lib.logos.examples import unit_tests

@pytest.mark.parametrize("example_name, example_case", unit_tests.items())
def test_logos_examples(example_name, example_case):
    """Test each logos example case from all subtheories."""
    
    # Create the appropriate operator registry based on the example type
    # This matches how each subtheory runs its own examples
    registry = LogosOperatorRegistry()
    
    if example_name.startswith('EXT_'):
        registry.load_subtheories(['extensional'])
    elif example_name.startswith('MOD_'):
        registry.load_subtheories(['extensional', 'modal', 'counterfactual'])
    elif example_name.startswith('CON_'):
        registry.load_subtheories(['extensional', 'constitutive', 'modal'])
    elif example_name.startswith('CF_'):
        registry.load_subtheories(['extensional', 'modal', 'counterfactual'])
    elif example_name.startswith('REL_'):
        registry.load_subtheories(['extensional', 'constitutive', 'modal', 'relevance'])
    elif example_name.startswith('LOGOS_BASIC_'):
        # Basic examples need full operator set
        registry.load_subtheories(['extensional', 'modal', 'constitutive', 'counterfactual', 'relevance'])
    else:
        # Default to all subtheories for unknown examples
        registry.load_subtheories(['extensional', 'modal', 'constitutive', 'counterfactual', 'relevance'])
    
    result = run_test(
        example_case,
        LogosSemantics,
        LogosProposition,
        registry.get_operators(),
        Syntax,
        ModelConstraints,
        LogosModelStructure,
    )
    
    # For logos subtheories, we follow the default theory pattern:
    # - True result means a countermodel was found (invalid argument)
    # - False result means no countermodel found (valid argument)
    # Most examples are countermodels (CM) showing invalidity, so we expect True
    # Theorem examples (TH) show validity, so we expect False
    settings = example_case[2] if len(example_case) > 2 else {}
    expected_result = settings.get('expectation', True)  # Use expectation from settings
    
    assert result == expected_result, f"Test failed for example: {example_name}. Expected {expected_result}, got {result}"


if __name__ == "__main__":
    pytest.main([__file__])