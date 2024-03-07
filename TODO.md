# TODO

Individual specific tasks can be marked with _M_ or _B_ when relevant.

## Print Function

- [ ] _M_ print all states in the model (some seem to be hidden)
  - NOTE: this is high priority since I can't really tell what it is doing until I can see the full state space
- [:] _B_ assign either `world`, `possible`, or `impossible` to each printed state
  - [x] _M_ revise state labeling strategy I hacked together
  - [ ] _M_ unlock `Var(0) == 1`; maybe there is a better way to find the extensions of predicates?
  - [ ] NOTE: I had to declare `world` making it equivalent to the defined `is_world` but this seems bad (maybe I'm wrong)
- [:] _B_ for each sentence letter `X`, print set of verifiers and set of falsify
  - [x] _M_ revise code I hacked together
- [ ] _M_ for each counterfactual sentence `X \boxright Y`, print the set of `X` alternatives to `w`
  - if `X \boxright Y` is true at `w`, then `Y` will be true in every `X` alternative to `w`
  - if `X \boxright Y` is false at `w`, then `Y` will be false at some `X` alternative to `w`
  - either way, it would be great to know what the `X` alternatives to `w` are
  - but we don't need to know what the `Z` alternatives to `w` are for `Z` that is not the antecedent to a counterfactual
  - NOTE: I can see how to do all of this by also declaring `alt_world` making this equivalent to `alternative`
  - it would be great to avoid this, but maybe there is no good way?

## Concrete Model

- [ ] countermodel for `A, B \vdash A \boxright B`
  - [x] _B_ build concrete model
  - [.] debug Z3 crashing issues in `test_model.py`
    - [x] _B_ Locate the constraint that seems to be the problem
    - [.] figure out why this constraint is causing trouble
      - [x] _B_ email Graham

## Definitions

- [x] _B_ `proposition` see strategies
- [x] _B_ add docstrings to `definitions.py`
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

## Print

- [x] _M_ name all atomic states in the model with lowercase letters `a, b, c, ...`
- [x] _M_ represent all states in the model as fusions, e.g., `a.b.c, d.e, a, ...`

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
