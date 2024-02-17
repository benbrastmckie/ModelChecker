# TODO

Individual specific tasks can be marked with _M_ or _B_ when relevant.

## Planning

- [x] review and revise plan for the project
- [x] create scaffolding for documentation, TODOS, and project updates
- [x] identify tooling (noting this in the docs)
  - [x] what else in addition to python3 and Z3 is needed?
  - [x] is latex ok for the overview?
- [x] get git working

## Overview

- [ ] _B_ move from set-fusion to binary fusion throughout

## Design

- [:] _B_ outline model checker design strategies

## Python

- [ ] _M_ infix/prefix functions
  - [ ] _M_ review `/Design/Strategies.md`, raising any questions in the corresponding GitHub issue.
  - [ ] _M_ confirm whether LaTeX commands will serve as suitable notation in python
  - [ ] _M_ build algorithm for going in either direction
    - [ ] _M_ prefix function translating into prefix notation
    - [ ] _M_ infix function translating back into infix notation
  - [:] _B_ research what Z3 wants for sentences to be interpreted

## Z3

- [x] clean up project directory
- [.] compile a range of resources for learning Z3
  - [.] glossary of commands, basic types/sorts, etc.
  - [ ] research Z3
    - [ ] _M_ add Z3 test examples with bitvectors to the `Z3Test/` directory
    - [ ] _M_ add questions/answers to `Questions.md`
    - [ ] _M_ read about how to use Z3 adding resources to `Resources.md`
    - [ ] _B_ add information about how Z3 works to `Resources.md`
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
- [ ] semantics in Z3
  - [ ] model
  - [ ] propositional operators
  - [ ] compatible parts
  - [ ] minimal changes
  - [ ] true at w in M
    - [ ] begin with propositional sentences
    - [ ] design definitions and run tests
    - [ ] extend approach to counterfactual sentences
  - [ ] entailment
