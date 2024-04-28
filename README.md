# Model Checker

This project aims to develop tools for finding countermodels for counterfactual claims as well as establishing entailments over finite models up to a specified degree of complexity.

## Installation

Install [Python 3](https://www.python.org/downloads/) and run the following commands in the terminal:

```
pip install z3-solver
pip install model-checker
```

## Examples

To generate a test file, `python3 path/to/test_complete.py`, or else run `python3 path/to/test_complete.py path/to/test_file.py` if a test file already exists.
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

- [ ] design method for searching for entailments
  - [ ] design syntactic filters to reduce the number of sentences up to a given complexity
  - [ ] design methods for avoiding searching for valid sentences by brute force
- [ ] given a set of valid sentences, devise method for identifying derivability relations
  - [ ] can lean be used to help?

