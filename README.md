# Model Checker

This project aims to develop tools for finding countermodels for counterfactual claims as well as establishing entailments over a restricted range of models up to a specified degree of complexity.

## Phases

### Z3

- [ ] introduction to Z3
  - [ ] identify a range of resources for learning Z3
  - [ ] compile notes with basic facts about Z3 and links to resources
  - [ ] complete relevant practice problems to gain familiarity with Z3
- [ ] define the predicates 'is a model' and 'satisfies' in a way that Z3 understands
  - [ ] begin with propositional sentences
  - [ ] design definitions and run tests to find models
  - [ ] extend to counterfactual sentences

### Python

- [ ] using python as a meta-language for interfacing with Z3
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

- [ ] design method for searching for valid sentences
  - [ ] design syntactic filters to reduce the number of sentences below a given complexity
  - [ ] design methods for avoiding searching for valid sentences by brute force
- [ ] given a set of valid sentences, devise method for identifying derivability relations
  - [ ] can lean be used to help?

### Print (Bonus)

- [ ] devise algorithm for visually representing models

## Resources

Z3 Python API - https://microsoft.github.io/z3guide/programming/Z3%20Python%20-%20Readonly/Introduction
