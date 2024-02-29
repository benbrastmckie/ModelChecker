# TODO

Individual specific tasks can be marked with _M_ or _B_ when relevant.

## Frame Definitions

- [ ] frame definitions
  - [ ] _M_ maximal
  - [ ] _M_ compatible
  - [ ] _M_ new/world
  - [ ] _M_ create test file
  - [ ] _M_ fix print numbers

## Concrete Model

- [ ] _B_ build countermodel

## Semantics

- [ ] semantic clauses
  - [ ] _M_ truth-functions

## Overview

- [ ] _B_ move from set-fusion to binary fusion throughout

## Strategies

- [x] _B_ model checker design strategies
  - [x] _B_ outline
  - [x] _B_ email Graham
  - [x] _B_ revise constraints
- [:] _B_ run strategies by Graham

## Z3

- [.] set up test solvers in Z3 with constraints
  - [ ] troubleshoot `is_part_of` in `parts.py`
  - [ ] define `verify` and `falsify` predicates in `prop.py`
- [x] clean up project directory
- [.] compile a range of resources for learning Z3
  - [.] glossary of commands, basic types/sorts, etc.
  - [:] research Z3
    - [x] _M_ add Z3 test examples with bitvectors to the `Z3Test/` directory
    - [x] _M_ add questions/answers to `Questions.md`
    - [x] _M_ read about how to use Z3 adding resources to `Resources.md`
    - [.] _B_ add information about how Z3 works to `Resources.md`
- [.] basic definitions in Z3
  - [x] atomic
  - [x] fusion
  - [x] parthood
  - [ ] exhaustive
  - [ ] exclusive
  - [ ] closed
  - [ ] propositions
  - [ ] semantics

## Python

- [:] sentence letter extractor
- model builder
  - function for extracting, renaming, and saving the elements of a Z3 model
  - function for printing the extracted model in a readable way
- constraint generators
  - model constraints
  - semantic constraints
  - evaluation constraints

# OLD

## Planning

- [x] review and revise plan for the project
- [x] create scaffolding for documentation, TODOS, and project updates
- [x] identify tooling (noting this in the docs)
  - [x] what else in addition to python3 and Z3 is needed?
  - [x] is latex ok for the overview?
- [x] get git working

## Python

- [x] _M_ prefix function
  - [x] _M_ review `/Design/Strategies.md`, raising any questions in the corresponding GitHub issue.
  - [x] _M_ confirm whether LaTeX commands will serve as suitable notation in python
  - [x] _M_ function translating into prefix notation
    - [x] _M_ clean up function names/stray parts
    - [x] _M_ check that `(A \\wedge B)` goes to `[Wedge, A, B]`
      - _M_: it doesn't, but I think the way it is now is better. To get rid of the backslashes would involve another function that may take a lot of computation, but we could leave it like this (right now it accepts double backslash, forwardslash, and no slashes) so that there is maximum flexibility on the user end. Internally of course the issue will have to be resolved, but I think it's easier to map 3 versions of the same command to one function or semantic requirement (ie, \\wedge /wedge and wedge all to Wedge) than to fix them all to a string of that semantic requirement.
      - _B_: sounds good.
    - [x] _B_ move notes elsewhere

## Strategies    

- [x] _B_ fix docs for prefix
  - [x] _B_ document purpose
  - [x] _B_ replace `Or` with `fusion`
- [x] _B_ representation function
  - [x] document purpose
  - [x] create issue
- [x] research what Z3 wants for predicates to be interpreted
