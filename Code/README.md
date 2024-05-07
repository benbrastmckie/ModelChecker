# Model Checker

This project draws on the [Z3](https://github.com/Z3Prover/z3) theorem prover to provide tools for proving theorems and finding countermodels for counterfactual conditional and modal claims.

## Semantics

The semantics included is hyperintensional insofar as sentences are evaluated at states which may be partial rather than total as in intensional semantic theories.
States are modeled by bitvectors (e.g., `#b00101`) of a specified length, where state fusion is modeled by the bitwise OR operator `|`.

More information can be found in the GitHub [repository](https://github.com/benbrastmckie/ModelChecker). For the background hyperintensional theory, see this [paper](https://link.springer.com/article/10.1007/s10992-021-09612-w).

## Syntax

The language currently includes operators for the counterfactual conditional `boxright`, modal operators for necessity `Box` and possibility `Diamond`, and the extensional operators for conjunction `wedge`, disjunction `vee`, material conditional `rightarrow`, material biconditional `leftrightarrow`, and negation `neg`.

## Instructions

To generate a test file run `model-checker` without arguments.

Alternatively, run `model-checker path/to/test_file.py` if the `test_file.py` already exists.

A number of [examples](https://github.com/benbrastmckie/ModelChecker/blob/master/Examples/examples.py) are provided in the GitHub repository.

Each file must specify a set of `premises` which are treated conjunctively, `conclusions` which are treated disjunctively, and the number `N` of atomic states to include in each model.

Optionally, the user can specify whether to print the Z3 constraints when a model is found, or the unsatisfiable core when no model exists, as well as an option to save the output.
