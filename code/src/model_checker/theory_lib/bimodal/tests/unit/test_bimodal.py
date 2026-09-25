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
from model_checker.utils.context import isolated_z3_context

# No excluded examples. The certificate encoding is quantifier-free (no ForAll/MBQI/
# E-matching anywhere in the search), so every example in `countermodel_examples`/
# `theorem_examples` is collected and expected to decide `match`. This constant is kept
# (empty) rather than deleted, matching this file's own historical convention and giving a
# single, greppable place to record a genuine future exclusion should one ever be needed.
#
# HISTORY (Phase 19): this set previously held 8 entries (`TN_CM_1`, `TN_CM_2`, `BM_CM_3`,
# `MD_TH_2`, `BM_TH_1`, `BM_TH_2`, `BX7_LINEAR_U_TH`, `BX7P_LINEAR_S_TH`) that were all
# specific to the retired window-and-abundance encoding's solver cost or a boundary-vacuity
# artifact (`MF_MODAL_FUTURE_TH`, removed from this set in Phase 16). Phase 17 measured
# every one of those 8 deciding correctly in well under 6ms under the certificate encoding;
# this phase confirms the same by simply running the full suite with nothing excluded.
KNOWN_TIMEOUT_EXAMPLES: set = set()

# No unstable-marked examples. `BM_CM_1`/`BM_CM_4` were previously marked `unstable` for a
# heavy-tailed Z3 solve distribution specifically attributed to the retired encoding's
# `ForAllTime`/`ExistsTime` quantifiers (`BM_CM_1`) and its Skolemized Seriality +
# Interpolation frame axioms added by commit f9cc081e (`BM_CM_4`) -- see
# `code/pyproject.toml`'s `unstable` marker registration and TESTING_GUIDE.md section 8.9
# for the general policy this marking followed. **Both mechanisms are gone, not merely
# fixed**: `build_seriality_constraint`, `build_interpolation_constraint`, `ForAllTime`, and
# `ExistsTime` no longer exist anywhere in `semantic/core.py` (the certificate encoding has
# no world/frame-axiom machinery to quantify over at all -- D3/D4), so the entry criteria's
# own root cause (a Z3 heuristic heavy tail on a `ForAll`-quantified constraint) cannot recur
# by construction, not merely by observation. Confirmed empirically as well: 20/20
# consecutive runs of both examples passed in this phase, each decided in well under 1s
# (`isolated_z3_context()` per run, matching the suite's own isolation discipline) --
# satisfying entry criterion (4)'s exit bar (a >= 20-run sweep with zero undecided/failing
# draws) even though the structural argument above is the stronger of the two grounds.
UNSTABLE_EXAMPLES: set = set()

test_examples = {k: v for k, v in {**countermodel_examples, **theorem_examples}.items()
                 if k not in KNOWN_TIMEOUT_EXAMPLES}

# pytest.param with the same (name, case) positional values reproduces the
# auto-generated ids a bare `.items()` view would have produced -- no explicit
# `ids=` is passed, so node IDs are unchanged from before this restructuring
# (verified by a --collect-only diff; see the implementation summary).
test_example_params = [
    pytest.param(
        name, case,
        marks=[pytest.mark.unstable] if name in UNSTABLE_EXAMPLES else [],
    )
    for name, case in test_examples.items()
]

@pytest.mark.parametrize("example_name, example_case", test_example_params)
def test_example_cases(example_name, example_case):
    """Test each example case from test_example_range."""
    with isolated_z3_context():
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
