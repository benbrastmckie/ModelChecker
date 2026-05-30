"""
1. To run all tests in the file run from your PROJECT_DIRECTORY:
pytest PROJECT_DIRECTORY/code/src/model_checker/theory_lib/bimodal/test/test_bimodal.py

2. To run a specific example test by name:
pytest PROJECT_DIRECTORY/code/src/model_checker/theory_lib/bimodal/test/test_bimodal.py -k "example_name"

3. To see more detailed output including print statements:
pytest -v PROJECT_DIRECTORY/code/src/model_checker/theory_lib/bimodal/test/test_bimodal.py

4. To see the most detailed output with full traceback:
pytest -vv PROJECT_DIRECTORY/code/src/model_checker/theory_lib/bimodal/test/test_bimodal.py

5. To see test progress in real-time:
pytest -v PROJECT_DIRECTORY/code/src/model_checker/theory_lib/bimodal/test/test_bimodal.py --capture=no
"""

import pytest

from model_checker import (
    ModelConstraints,
    Syntax,
    run_test,
)
from model_checker.theory_lib.bimodal import (
    BimodalStructure,
    BimodalProposition,
    BimodalSemantics,
    bimodal_operators,
)
from model_checker.theory_lib.bimodal.examples import countermodel_examples, theorem_examples

# Combine both example sets for testing, excluding known solver timeout cases
KNOWN_TIMEOUT_EXAMPLES = {"TN_CM_1", "TN_CM_2", "BM_CM_1", "BM_CM_2", "BM_CM_3", "BM_CM_4", "MD_TH_2"}
test_examples = {k: v for k, v in {**countermodel_examples, **theorem_examples}.items()
                 if k not in KNOWN_TIMEOUT_EXAMPLES}

@pytest.mark.parametrize("example_name, example_case", test_examples.items())
def test_example_cases(example_name, example_case):
    """Test each example case from test_example_range."""
    result = run_test(
        example_case,
        BimodalSemantics,
        BimodalProposition,
        bimodal_operators,
        Syntax,
        ModelConstraints,
        BimodalStructure,
    )
    assert result, f"Test failed for example: {example_name}"


if __name__ == '__main__':
    import pytest
    pytest.main([__file__, '-v'])
