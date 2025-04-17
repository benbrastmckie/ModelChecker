"""
1. To run all tests in the file run from your PROJECT_DIRECTORY:
pytest PROJECT_DIRECTORY/test/test_default.py

2. To run a specific example test by name:
pytest PROJECT_DIRECTORY/test/test_default.py -k "example_name"

3. To see more detailed output including print statements:
pytest -v PROJECT_DIRECTORY/test/test_default.py

4. To see the most detailed output with full traceback:
pytest -vv PROJECT_DIRECTORY/test/test_default.py

5. To see test progress in real-time:
pytest -v PROJECT_DIRECTORY/test/test_default.py --capture=no
"""

import pytest

from model_checker import (
    ModelConstraints,
    Syntax,
    run_test,
)
from model_checker.theory_lib.default import (
    ModelStructure,
    Proposition,
    Semantics,
    default_operators,
)
from model_checker.theory_lib.default.examples import test_example_range

@pytest.mark.parametrize("example_name, example_case", test_example_range.items())
def test_example_cases(example_name, example_case):
    """Test each example case from example_range."""
    result = run_test(
        example_case,
        Semantics,
        Proposition,
        default_operators,
        Syntax,
        ModelConstraints,
        ModelStructure,
    )
    assert result, f"Test failed for example: {example_name}"



