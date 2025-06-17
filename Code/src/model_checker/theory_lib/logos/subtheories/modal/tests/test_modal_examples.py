"""
Tests for modal subtheory examples.

This test file runs all examples from the modal subtheory examples.py file
using the same pattern as the default theory tests.

To run these tests:
1. All tests: pytest src/model_checker/theory_lib/logos/subtheories/modal/tests/test_modal_examples.py
2. Specific test: pytest src/model_checker/theory_lib/logos/subtheories/modal/tests/test_modal_examples.py -k "MOD_CM_1"
3. Verbose output: pytest -v src/model_checker/theory_lib/logos/subtheories/modal/tests/test_modal_examples.py
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
from model_checker.theory_lib.logos.subtheories.modal.examples import modal_examples

# Create operator registry for modal theory
modal_registry = LogosOperatorRegistry()
modal_registry.load_subtheories(['extensional', 'modal', 'counterfactual'])

@pytest.mark.parametrize("example_name, example_case", modal_examples.items())
def test_modal_examples(example_name, example_case):
    """Test each modal example case."""
    result = run_test(
        example_case,
        LogosSemantics,
        LogosProposition,
        modal_registry.get_operators(),
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