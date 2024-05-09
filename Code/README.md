# Model Checker

This project draws on the [Z3](https://github.com/Z3Prover/z3) theorem prover to provide tools for proving theorems and finding countermodels for counterfactual conditional and modal claims.

## Installation

Install [Python 3](https://www.python.org/downloads/) and run the following commands in the terminal:

```
pip install model-checker
```

The project has the `z3-solver` as a dependency.

Detailed [installation instructions](https://github.com/benbrastmckie/ModelChecker?tab=readme-ov-file#instructions) are provided in the GitHub repository.

## Instructions

To generate a test file run `model-checker` without arguments.

Alternatively, run `model-checker path/to/test_file.py` if the `test_file.py` already exists.

A number of [examples](https://github.com/benbrastmckie/ModelChecker/blob/master/Examples/examples.py) are provided in the GitHub repository.

Each file must specify a set of `premises` and `conclusions` which are treated conjunctively, and the number `N` of atomic states to include in each model.

Optionally, the user can specify whether to print the Z3 constraints when a model is found, or the unsatisfiable core when no model exists, as well as an option to save the output.

## Semantics

The semantics included is hyperintensional insofar as sentences are evaluated at states which may be partial rather than total as in intensional semantic theories.
States are modeled by bitvectors (e.g., `#b00101`) of a specified length, where state fusion is modeled by the bitwise OR operator `|`.
States are named by lowercase letters for the sake of printing readable countermodels.

More information can be found in the GitHub [repository](https://github.com/benbrastmckie/ModelChecker). 
The hyperintensional semantic theory for counterfactual conditionals is motivated and elaborated in this [draft](https://github.com/benbrastmckie/ModelChecker/blob/master/Counterfactuals.pdf).
For the background hyperintensional theory of propositions, see this [paper](https://link.springer.com/article/10.1007/s10992-021-09612-w).

## Syntax

The language currently includes operators for the counterfactual conditional `boxright`, modal operators for necessity `Box` and possibility `Diamond`, and the extensional operators for conjunction `wedge`, disjunction `vee`, material conditional `rightarrow`, material biconditional `leftrightarrow`, and negation `neg`.

