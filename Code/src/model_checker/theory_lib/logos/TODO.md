# TODO

Tasks that remain before the next release.

## Jupyter Notebooks

- Look at the default/ theory to see how to implement Jupyter Notebooks for the logos/ theory
- Implement Jupyter Notebooks for each subtheory of the Logos/

## Clean Up

- review all documentation in the `logos/` theory to see if it can be improved to avoid redundancy, improve clarity, or better organize information

## Buffer Diagnostics

Code/run_update.py|1 col 1| Parser failed. Error message:...al/share/nvim/lazy/nvim-lint/lua/lint/linters/pylint.lua:28: Expected value but found invalid token at character 1Output from linter:No files to lint: exiting.
Code/run_update.py|27 col 46| Argument of type "ModuleSpec | None" cannot be assigned to parameter "spec" of type "ModuleSpec" in function "module_from_spec"  Type "ModuleSpec | None" is not assignable to type "ModuleSpec"    "None" is not assignable to "ModuleSpec"
Code/run_update.py|28 col 17| "exec_module" is not a known attribute of "None"
Code/run_update.py|28 col 10| "loader" is not a known attribute of "None"
Code/run_update.py|16 col 8| "os" is not accessed

Code/tests/test_package.py|1 col 1| Parser failed. Error message:...al/share/nvim/lazy/nvim-lint/lua/lint/linters/pylint.lua:28: Expected value but found invalid token at character 1Output from linter:No files to lint: exiting.
Code/tests/test_package.py|13 col 8| "importlib.util" is not accessed
Code/tests/test_package.py|141 col 9| "full_test_dir" is not accessed
Code/tests/test_package.py|208 col 13| "verify_metadata_consistency" is not accessed
