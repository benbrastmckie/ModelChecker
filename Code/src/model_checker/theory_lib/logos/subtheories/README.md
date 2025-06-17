# LOGOS: A Unified Formal Language of Thought

## Theory Testing

This file contains a number of demonstrations for the subtheories that belong to the Logos.

### Individual Subtheory Testing

To test a specific subtheory, use these commands from the project root:

**Developer mode (using dev_cli.py):**
- `./dev_cli.py src/model_checker/theory_lib/logos/subtheories/counterfactual/examples.py`
- `./dev_cli.py src/model_checker/theory_lib/logos/subtheories/constitutive/examples.py`
- `./dev_cli.py src/model_checker/theory_lib/logos/subtheories/modal/examples.py`
- `./dev_cli.py src/model_checker/theory_lib/logos/subtheories/extensional/examples.py`
- `./dev_cli.py src/model_checker/theory_lib/logos/subtheories/relevance/examples.py`

**Using model-checker command:**
- `model-checker src/model_checker/theory_lib/logos/subtheories/counterfactual/examples.py`
- `model-checker src/model_checker/theory_lib/logos/subtheories/constitutive/examples.py`
- `model-checker src/model_checker/theory_lib/logos/subtheories/modal/examples.py`
- `model-checker src/model_checker/theory_lib/logos/subtheories/extensional/examples.py`
- `model-checker src/model_checker/theory_lib/logos/subtheories/relevance/examples.py`

### Complete Logos Theory Testing

To test the entire Logos theory including all subtheories:

**Developer mode:**
- `./dev_cli.py src/model_checker/theory_lib/logos/examples.py`

**Using model-checker command:**
- `model-checker src/model_checker/theory_lib/logos/examples.py`

## Unit Testing

**Unit test suite (includes all examples from all subtheories):**
- `python test_theories.py --theories logos`

**Run only the unified subtheory examples:**
- `python -m pytest src/model_checker/theory_lib/logos/tests/test_logos_examples.py -v`

**Run specific examples by name:**
- `python -m pytest src/model_checker/theory_lib/logos/tests/test_logos_examples.py -k "EXT_CM_1" -v`

### Debugging Test Failures

To see detailed information about test failures, use verbose mode:

**Verbose output:**
- `python test_theories.py --theories logos -v`

**Stop on first failure:**
- `python test_theories.py --theories logos -x`

**Direct pytest for more control:**
- `python -m pytest src/model_checker/theory_lib/logos/tests/ -v`
- `python -m pytest src/model_checker/theory_lib/logos/tests/test_logos.py::TestLogosSemantics::test_semantics_instantiation -v -s`

**With timeout for hanging tests:**
- `python -m pytest src/model_checker/theory_lib/logos/tests/ -v --timeout=30`

The `-v` flag shows verbose output including which specific test failed and why. The `-s` flag shows print statements and other output from tests. The `--timeout=30` flag kills tests that run longer than 30 seconds, useful for identifying hanging tests.
