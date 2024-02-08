# TODO

Individual specific tasks can be marked with _M_ or _B_ when relevant.

## Planning

- [x] review and revise plan for the project
- [x] create scaffolding for documentation, TODOS, and project updates
- [x] identify tooling (noting this in the docs)
  - [x] what else in addition to python3 and Z3 is needed?
  - [x] is latex ok for the overview?

## Overview

- [ ] _B_ move from set-fusion to binary fusion throughout

## Z3

- [.] compile a range of resources for learning Z3
  - [.] glossary of commands, basic types/sorts, etc.
  - [ ] introductory examples and practice problems
    - [ ] _M_ add Z3 test examples with bitvectors to the `Z3Test/` directory
    - [ ] _M_ add any questions to `Questions.md` that arise
  - [ ] _B_ collect relevant information about how Z3 works
- [ ] basic definitions in Z3
  - [ ] fusion
  - [ ] parthood
  - [ ] state space
  - [ ] modal frame
  - [ ] compatible
  - [ ] world state
  - [ ] exhaustive
  - [ ] exclusive
  - [ ] closed
  - [ ] propositions
- [ ] semantic definitions in Z3
  - [ ] model
  - [ ] propositional operators
  - [ ] compatible parts
  - [ ] minimal changes
  - [ ] true at w in M
  - [ ] satisfaction
- [ ] define the predicates 'x is a model', 'y is a sentence', and 'x satisfies y' in Z3
  - [ ] begin with propositional sentences
  - [ ] design definitions and run tests
  - [ ] extend approach to counterfactual sentences
