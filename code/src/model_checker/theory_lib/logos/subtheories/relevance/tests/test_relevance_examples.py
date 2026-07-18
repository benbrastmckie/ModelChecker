"""
Tests for relevance subtheory examples.

This test file runs all examples from the relevance subtheory examples.py file
using the logos testing framework.

To run these tests:
1. All tests: pytest src/model_checker/theory_lib/logos/subtheories/relevance/tests/test_relevance_examples.py
2. Specific test: pytest src/model_checker/theory_lib/logos/subtheories/relevance/tests/test_relevance_examples.py -k "REL_CM_1"
3. Verbose output: pytest -v src/model_checker/theory_lib/logos/subtheories/relevance/tests/test_relevance_examples.py
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
from model_checker.theory_lib.logos.subtheories.relevance.examples import unit_tests


@pytest.mark.parametrize("example_name, example_case", unit_tests.items())
def test_relevance_examples(example_name, example_case):
    """Test each relevance example case."""
    
    # Create operator registry for relevance theory
    registry = LogosOperatorRegistry()
    registry.load_subtheories(['extensional', 'modal', 'constitutive', 'relevance'])
    
    result = run_test(
        example_case,
        LogosSemantics,
        LogosProposition,
        registry.get_operators(),
        Syntax,
        ModelConstraints,
        LogosModelStructure,
    )
    
    # The run_test function returns True if the model matches expectations, False otherwise
    assert result, f"Test failed for example: {example_name}. Model result did not match expectation value in settings."


if __name__ == "__main__":
    pytest.main([__file__])