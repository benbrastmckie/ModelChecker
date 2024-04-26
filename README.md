# Model Checker

This project aims to develop tools for finding countermodels for counterfactual claims as well as establishing entailments over finite models up to a specified degree of complexity.

## Dependencies

The model checker is built on [Z3](https://github.com/Z3Prover/z3) which can be installed with `pip install z3-solver` or as specified in the `flake.nix` for NixOS.
[Python 3](https://www.python.org/downloads/) must also be installed, but there are no other dependencies.

## Examples

To run the model checker, run `python3 path/to/test_complete.py` to generate a test file, or else run `python3 path/to/test_complete.py path/to/test_file.py`.
The `examples.py` file contains a number of valid and invalid arguments that can be tested in this way.

## Modules

Here is a brief overview of the included modules.

To be continued...

## Resources

The `Resources/` directory contains a number of files with various resources including the paper which motivates and develops the hyperintensional semantics implemented here.

To be continued...

## Future Ambitions

Here are a number of additions that remain to be included.

### Axiom Search

 [ ] design method for searching for entailments
  - [ ] design syntactic filters to reduce the number of sentences up to a given complexity
  - [ ] design methods for avoiding searching for valid sentences by brute force
 [ ] given a set of valid sentences, devise method for identifying derivability relations
  - [ ] can lean be used to help?

