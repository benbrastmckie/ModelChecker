"""
Tests for counterfactual subtheory examples.

This test file runs all examples from the counterfactual subtheory examples.py file
using the logos testing framework.

To run these tests:
1. All tests: pytest src/model_checker/theory_lib/logos/tests/test_examples/test_counterfactual_examples.py
2. Specific test: pytest src/model_checker/theory_lib/logos/tests/test_examples/test_counterfactual_examples.py -k "CF_CM_1"
3. Verbose output: pytest -v src/model_checker/theory_lib/logos/tests/test_examples/test_counterfactual_examples.py
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
from model_checker.theory_lib.logos.subtheories.counterfactual.examples import unit_tests


@pytest.mark.parametrize("example_name, example_case", unit_tests.items())
def test_counterfactual_examples(example_name, example_case):
    """Test each counterfactual example case."""
    
    # Create operator registry for counterfactual theory
    registry = LogosOperatorRegistry()
    registry.load_subtheories(['extensional', 'modal', 'counterfactual'])
    
    result = run_test(
        example_case,
        LogosSemantics,
        LogosProposition,
        registry.get_operators(),
        Syntax,
        ModelConstraints,
        LogosModelStructure,
    )
    
    # Extract expected result from settings
    settings = example_case[2] if len(example_case) > 2 else {}
    expected_result = settings.get('expectation', True)
    
    assert result == expected_result, f"Test failed for example: {example_name}. Expected {expected_result}, got {result}"


if __name__ == "__main__":
    pytest.main([__file__])