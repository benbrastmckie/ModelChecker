"""
Tests for constitutive subtheory examples.

This test file runs all examples from the constitutive subtheory examples.py file
using the same pattern as the default theory tests.

NOTE: For comprehensive logos theory testing, use the main logos test file:
./test_theories.py --theories logos -v

This file provides constitutive-specific testing for development and debugging.

To run these tests:
1. All tests: pytest src/model_checker/theory_lib/logos/subtheories/constitutive/tests/test_constitutive_examples.py
2. Specific test: pytest src/model_checker/theory_lib/logos/subtheories/constitutive/tests/test_constitutive_examples.py -k "CL_CM_1"
3. Verbose output: pytest -v src/model_checker/theory_lib/logos/subtheories/constitutive/tests/test_constitutive_examples.py
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
from model_checker.theory_lib.logos.subtheories.constitutive.examples import constitutive_examples

# Create operator registry for constitutive theory
constitutive_registry = LogosOperatorRegistry()
constitutive_registry.load_subtheories(['extensional', 'constitutive', 'modal'])

@pytest.mark.parametrize("example_name, example_case", constitutive_examples.items())
def test_constitutive_examples(example_name, example_case):
    """Test each constitutive example case."""
    result = run_test(
        example_case,
        LogosSemantics,
        LogosProposition,
        constitutive_registry.get_operators(),
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