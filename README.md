# Model Checker

This project aims to develop tools for finding countermodels for counterfactual claims as well as establishing entailments over a restricted range of models up to a specified degree of complexity.

## Phases

### Planning

- review and revise plan for the project
- create scaffolding for documentation, TODOS, and project updates
- identify tooling (noting this in the docs)
  - what else in addition to python3 and Z3 is needed?
  - is latex ok for the overview?

### Z3

Putting Z3 to work in simple and specific applications.

- [ ] compile a range of resources for learning Z3
  - [ ] glossary of commands, basic types/sorts, etc.
  - [ ] introductory examples and practice problems
  - [ ] relevant information about how Z3 works
- [ ] define the predicates 'x is a model', 'y is a sentence', and 'x satisfies y' in Z3
  - [ ] begin with propositional sentences
  - [ ] design definitions and run tests
  - [ ] extend approach to counterfactual sentences

### Python

Using python as a meta-language for interfacing with Z3.

- [ ] design conventions for a `semantics file` containing the definitions:
  - [ ] definition of the primitives and sentences of the language
  - [ ] definition of a model of the language
  - [ ] semantic clauses for the operators of the language
  - [ ] optional axioms and rules to constrain the space of models
  - [ ] needs to be relatively easy to read/tweak
- [ ] design conventions for a `project file` for a specific inquiry
  - [ ] may include a set of sentences to check for satisfiability
  - [ ] may include an entailment between a set of premises and a conclusion
  - [ ] may specify options such as:
    - [ ] halt after first model is found
    - [ ] find all models up to some limit in time or complexity
- [ ] Z3 translator
  - [ ] devise translation algorithms from the readable conventions into Z3 sentences
  - [ ] use algorithms to create a `job file` from a `semantics file` and `project file`
  - [ ] the `job file` should include the Z3 sentences and the outputs from Z3

### Search (Bonus)

Building tools for finding axiom systems.

- [ ] design method for searching for all valid sentences
  - [ ] design syntactic filters to reduce the number of sentences up to a given complexity
  - [ ] design methods for avoiding searching for valid sentences by brute force
- [ ] given a set of valid sentences, devise method for identifying derivability relations
  - [ ] can lean be used to help?

### Print (Bonus)

Presenting models in a visually compelling manner.

- [ ] devise algorithm for visually representing models
  - [ ] design the desired visual output
  - [ ] review the tools that already exist for representing models visually
  - [ ] see what it would take to translate from a `job file` to a visual model using a given tool

## Resources

Z3 Python API - https://microsoft.github.io/z3guide/programming/Z3%20Python%20-%20Readonly/Introduction
