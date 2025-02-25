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
)
from model_checker.theory_lib.default import (
    ModelStructure,
    Proposition,
    Semantics,
    default_operators,
)
from model_checker.theory_lib.default.examples import example_range



def run_test(example_case):

    premises, conclusions, settings = example_case

    example_syntax = Syntax(premises, conclusions, default_operators)

    semantics = Semantics(settings)

    # Create model constraints
    model_constraints = ModelConstraints(
        settings,
        example_syntax,
        semantics,
        Proposition,
    )

    # Create model structure
    model_structure = ModelStructure(
        model_constraints, 
        settings,
    )

    return model_structure.check_result

@pytest.mark.parametrize("example_name,example_case", example_range.items())
def test_example_cases(example_name, example_case):
    """Test each example case from example_range."""
    result = run_test(example_case)
    assert result, f"Test failed for example: {example_name}"



