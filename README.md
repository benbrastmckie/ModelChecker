# Model Checker

This project aims to develop tools for finding countermodels for counterfactual claims as well as establishing entailments over a restricted range of models up to a specified degree of complexity.

## Resources

The `Resources/` directory contains a number of files where we can compile resources throughout.
This is a place to not only store what has been learned along the way for later reference, but to share knowledge.
Ultimately, it would be nice to make these resources useful to those who are new to the project.

## Phases

The phases are intended to roughly divide the project chronologically.

### Planning

- [x] review and revise plan for the project
- [x] create scaffolding for documentation, TODOS, and project updates
- [x] identify tooling (noting this in the docs)
  - [x] what else in addition to python3 and Z3 is needed?
  - [x] is latex ok for the overview?

### Z3

Putting Z3 to work in simple and specific applications.

- [ ] research Z3
- [ ] define models in Z3
- [ ] get a basic model checker working in Z3

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
