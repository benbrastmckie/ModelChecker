# TODO

Tasks that remain before the next release.

## Tests

- clean up the various tests in `/home/benjamin/Documents/Philosophy/Projects/ModelChecker/Code/`, removing any that are unnecessary and moving the remaining tests to a Code/tests/ directory
- get all tests to pass when running `./Code/test_theories.py -v` making sure that the old `default/` theory tests are no longer included

## Jupyter Notebooks

- Look at the default/ theory to see how to implement Jupyter Notebooks for the logos/ theory
- Implement Jupyter Notebooks for each subtheory of the Logos/

## Clean Up

- review all documentation in the `logos/` theory to see if it can be improved to avoid redundancy, improve clarity, or better organize information

## Buffer Diagnostics

Code/tests/test_package.py|1 col 1| Parser failed. Error message:...al/share/nvim/lazy/nvim-lint/lua/lint/linters/pylint.lua:28: Expected value but found invalid token at character 1Output from linter:No files to lint: exiting.
Code/tests/test_package.py|13 col 8| "importlib.util" is not accessed
Code/tests/test_package.py|141 col 9| "full_test_dir" is not accessed
Code/tests/test_package.py|208 col 13| "verify_metadata_consistency" is not accessed
