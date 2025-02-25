"""
1. To run all tests in the file run from your PROJECT_DIRECTORY:
pytest PROJECT_DIRECTORY/test/test_exclusion.py

2. To run a specific example test by name:
pytest PROJECT_DIRECTORY/test/test_exclusion.py -k "example_name"

3. To see more detailed output including print statements:
pytest -v PROJECT_DIRECTORY/test/test_exclusion.py

4. To see the most detailed output with full traceback:
pytest -vv PROJECT_DIRECTORY/test/test_exclusion.py

5. To see test progress in real-time:
pytest -v PROJECT_DIRECTORY/test/test_exclusion.py --capture=no
"""

import pytest

from model_checker import (
    ModelConstraints,
    Syntax,
)
from model_checker.theory_lib.exclusion import (
    ExclusionStructure,
    UnilateralProposition,
    ExclusionSemantics,
    exclusion_operators,
)
from model_checker.theory_lib.exclusion.examples import example_range
from model_checker.utils import run_test

@pytest.mark.parametrize("example_name,example_case", example_range.items())
def test_example_cases(example_name, example_case):
    """Test each example case from example_range."""
    result = run_test(
        example_case,
        ExclusionSemantics,
        UnilateralProposition,
        exclusion_operators,
        Syntax,
        ModelConstraints,
        ExclusionStructure,
    )
    assert result, f"Test failed for example: {example_name}"

