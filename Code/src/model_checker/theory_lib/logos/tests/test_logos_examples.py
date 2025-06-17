"""
Tests for all logos subtheory examples.

This test file runs all examples from all logos subtheories following the same
pattern as the default theory tests.

1. To run all tests in the file run from your PROJECT_DIRECTORY:
   pytest src/model_checker/theory_lib/logos/tests/test_logos_examples.py

2. To run a specific example test by name:
   pytest src/model_checker/theory_lib/logos/tests/test_logos_examples.py -k "EXT_CM_1"

3. To see more detailed output including print statements:
   pytest -v src/model_checker/theory_lib/logos/tests/test_logos_examples.py

4. To see the most detailed output with full traceback:
   pytest -vv src/model_checker/theory_lib/logos/tests/test_logos_examples.py

5. To see test progress in real-time:
   pytest -v src/model_checker/theory_lib/logos/tests/test_logos_examples.py --capture=no
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

# Import all subtheory examples
from model_checker.theory_lib.logos.subtheories.extensional.examples import extensional_examples
from model_checker.theory_lib.logos.subtheories.modal.examples import modal_examples
from model_checker.theory_lib.logos.subtheories.constitutive.examples import constitutive_examples
from model_checker.theory_lib.logos.subtheories.counterfactual.examples import counterfactual_examples
from model_checker.theory_lib.logos.subtheories.relevance.examples import relevance_examples

# Create unified test example range (following default theory pattern)
test_example_range = {
    **extensional_examples,
    **modal_examples,
    **constitutive_examples,
    **counterfactual_examples,
    **relevance_examples,
}

@pytest.mark.parametrize("example_name, example_case", test_example_range.items())
def test_example_cases(example_name, example_case):
    """Test each example case from all subtheories."""
    
    # Create the appropriate operator registry based on the example type
    # This matches how each subtheory runs its own examples
    registry = LogosOperatorRegistry()
    
    if example_name.startswith('EXT_'):
        registry.load_subtheories(['extensional'])
    elif example_name.startswith('MOD_'):
        registry.load_subtheories(['extensional', 'modal', 'counterfactual'])
    elif example_name.startswith('CL_'):
        registry.load_subtheories(['extensional', 'constitutive', 'modal'])
    elif example_name.startswith('CF_'):
        registry.load_subtheories(['extensional', 'counterfactual'])
    elif example_name.startswith('REL_'):
        registry.load_subtheories(['extensional', 'modal', 'constitutive', 'relevance'])
    else:
        # Default to all subtheories
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
    # Check expectation setting: True = countermodel expected, False = theorem expected
    settings = example_case[2] if len(example_case) > 2 else {}
    expected_result = settings.get('expectation', True)  # Default to True (countermodel expected)
    
    assert result == expected_result, f"Test failed for example: {example_name}. Expected {expected_result}, got {result}"