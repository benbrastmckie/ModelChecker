# TODO

Individual specific tasks can be marked with _M_ or _B_ when relevant.

## Print Function

NOTE: See post-processing in `Strategies.md`.
It will be important to start on model representation to better understand the models it is building.
Once Z3 is finding good models for explicit example inputs we can start on the constraint generator functions.

- [x] _M_ name all atomic states in the model with lowercase letters `a, b, c, ...`
- [x] _M_ represent all states in the model as fusions, e.g., `a.b.c, d.e, a, ...`
- [ ] _M_ print which states verify/falsify which sentence letters
  - [ ] this could take the form `|A| = < {a, b, a.b}, {c.d} >`
- [ ] _M_ print which states are world states

## Concrete Model

- [ ] countermodel for `A, B \vdash A \boxright B`
  - [x] _B_ build concrete model
  - [.] debug Z3 crashing issues in `test_model.py`
    - [x] _B_ Locate the constraint that seems to be the problem
    - [ ] figure out why this constraint is causing trouble
  - [ ] _M_ try to use quantifiers over sentence letters in model constraints

## Semantic Definitions

- [ ] _M_ `proposition` see strategies
- [ ] _M_ `extended_verify` see strategies
- [ ] _M_ `extended_falsify` see strategies
- [ ] _M_ recursive definition of `true`

## Constraint Generators

- model constraints from `sentence_letters`
- evaluation constraints from `input_sentences`

## Overview

- [ ] _B_ move from set-fusion to binary fusion throughout
- [x] _B_ check that world-hood constraint is not needed for finite spaces

## Strategies

- [x] _B_ model checker design strategies
  - [:] model constraints
    - [x] _B_ outline
    - [x] _B_ email Graham
    - [x] _B_ revise constraints
    - [:] _B_ run strategies by Graham
  - [x] _B_ model builder
    - [x] _B_ outline
    - [x] _B_ revise

<!-- BONEYARD -->

# Completed

## Planning

- [x] review and revise plan for the project
- [x] create scaffolding for documentation, TODOS, and project updates
- [x] identify tooling (noting this in the docs)
  - [x] what else in addition to python3 and Z3 is needed?
  - [x] is latex ok for the overview?
- [x] get git working

## Definitions

- [x] _B_ maximal
- [x] _B_ compatible
- [x] _B_ world
- [x] _B_ create test file

## Python

- [x] sentence letter extractor
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

## Z3

- [x] set up test solvers in Z3 with constraints
  - [x] troubleshoot `is_part_of` in `parts.py`
  - [x] define `verify` and `falsify` predicates in `prop.py`
- [x] clean up project directory
- [.] compile a range of resources for learning Z3
  - [:] glossary of commands, basic types/sorts, etc.
  - [:] research Z3
    - [x] _M_ add Z3 test examples with bitvectors to the `Z3Test/` directory
    - [x] _M_ add questions/answers to `Questions.md`
    - [x] _M_ read about how to use Z3 adding resources to `Resources.md`
    - [.] _B_ add information about how Z3 works to `Resources.md`
- [:] basic definitions in Z3
  - [x] atomic
  - [x] fusion
  - [x] parthood
  - [x] exhaustive
  - [x] exclusive
  - [x] closed
  - [x] propositions
