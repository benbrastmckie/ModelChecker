# Model Checker

This project aims to develop tools for finding countermodels for counterfactual claims as well as establishing entailments over finite models up to a specified degree of complexity.

## Dependencies

The model checker is built on [Z3](https://github.com/Z3Prover/z3) which can be installed with `pip install z3-solver` or as specified in the `flake.nix` for NixOS.
[Python 3](https://www.python.org/downloads/) must also be installed, but there are no other dependencies.

## Examples

The script `Code/test_complete.py` contains a number of examples that can be commented on and off.
Running this file with `python3` produces countermodels or else provides the resulting core Z3 constraints that cannot be satisfied.
Further examples can easily be added to this file.

## Modules

Here is a brief overview of the included modules.

### Main Script: `test_complete.py`

This script includes specifies the complexity of models `N`, `premises`, `conclusions`, and the print settings `print_cons_bool` and `print_unsat_core_bool` for debugging examples.
This scrip imports from `model_structure.py`.

### Model Module: `model_structure.py`

This module... To be continued. 

## Resources

The `Resources/` directory contains a number of files with various resources.
This is a place to not only store what has been learned along the way for later reference, but to share knowledge.
Ultimately, it would be nice to make these resources useful to those who are new to the project.

## Axiom Search

Building tools for finding axiom systems.

- [ ] design method for searching for entailments
  - [ ] design syntactic filters to reduce the number of sentences up to a given complexity
  - [ ] design methods for avoiding searching for valid sentences by brute force
- [ ] given a set of valid sentences, devise method for identifying derivability relations
  - [ ] can lean be used to help?

