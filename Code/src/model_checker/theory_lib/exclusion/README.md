# Model-Checker Instructions

This document provides an overview of the package contents for the _exclusion semantics_ defended by [Bernard and Champollion](https://ling.auf.net/lingbuzz/007730/current.html).
Further documentation can be found in the `docstrings` and comments.

## Contents

This package includes the following templates:
  - `README.md` to document usage and changes.
  - `__init__.py` to expose definitions to be imported elsewhere.
  - `semantic.py` defines the default semantics for the operators included.
  - `operators.py` defines the primitive and derived operators.
  - `examples.py` defines a number of examples to test.

## Usage

Run `model-checker examples.py` from within the project directory to test the examples included in `examples.py`.
For instance, these might include:


## Basic Architecture

The `semantics.py` module consists of two classes which define the models of the language and the theory of propositions over which the language is interpreted.

