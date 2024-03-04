# Plan

This document outlines the next steps going forward.

## Concrete Model

- [.] build concrete models for simple examples
  - [.] show A, B, \neg(A \boxright B) is sat
    - [x] identify groups of constraints
      - [x] frame constraints
      - [.] model constraints
        - [ ] debug why adding constraints for B fails
      - [x] evaluation constraints
- [ ] represent Z3 models in a readable way
  - [ ] name atomic states, representing all states as fusions
  - [ ] represent which states verify/falsify which sentence letters
  - [ ] represent which states are world states
- [ ] build constraint generators
  - [ ] abstract from groups of constraints above
  - [ ] the frame constraints only depend on how many atomic states there are
  - [ ] the model constraints depend on which sentence letters are involved
  - [ ] the evaluation constraints depend on both:
    - [ ] the sentences being evaluated
    - [ ] the semantic clauses (held fixed for now purposes)
  - testing and refinement
    - use constraint generators to explore models
- model representations
  - represent a concrete models in a readable way
  - identify functions to abstract
  - build general representation function
- design input process
  - definition file
  - semantics file
  - model template file
  - output file conventions
