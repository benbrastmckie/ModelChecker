# Plan

This document outlines the next steps going forward.

## Concrete Model

- build concrete model for simple example
  - show A, B, \neg(A \boxright B) is sat
  - identify groups of constraints
    - frame constraints
    - model constraints
    - evaluation constraints
- build constraint generators
  - abstract from groups of constraints above
  - the frame constraints only depend on how bit states are
  - the model constraints depend on which sentence letters are involved
  - the evaluation constraints depend on both:
    - the sentences being evaluated
    - the semantic clauses (held fixed for now purposes)
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
