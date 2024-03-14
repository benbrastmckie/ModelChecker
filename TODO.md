# TODO

Individual specific tasks can be marked with _M_ or _B_ when relevant.

## Refine and Optimize

- [x] _M_ functions in `print.py` can probably be improved (see notes there)
  - B: looks much better!
  - B: replacing `string_part` in `print.py` with `bit_part` seems to work, but my linter doesn't like it. not sure if that is any concern.
  - M: Cleaned up what I hadn't been able to get to before and left comments—feel free to delete any comments that are resolved/solved (linter issue unsolved, but I wasn't getting it on my end, maybe your linter is stricter than mine lol)
- [x] _M_ `is_bitvector` in `print.py` for `N > 4` (see TODO in `print.py`)
- [x] _M_ allow for more than 26 atomic states in `bitvec_to_substates`
  - M: I have a soln, something that seemed intuitive to me (not subindices), however let me know if
  you want a different one. It'd be a simple change, so whatever you want it to be represented as let
  me know and I can change it to that
- [.] _M_ avoid having to make N not equal to a power of 2
  - M: I did some more digging around and it looks like there's no way around this, even within Z3 languages so to speak. There is a way to make all bitvecs in decimal format, but that's not something useful for us. My best source so far: https://microsoft.github.io/z3guide/docs/theories/Bitvectors/ (and other websites that say the same thing). This also makes sense given how .sexpr() works: it takes in the Z3 object in C and its location (https://z3prover.github.io/api/html/classz3py_1_1_ast_ref.html#ab41c56f8b1c61ace1b28a163103d86b4), making me think that the hexadecimal format for multiples of 4 (I thought it was powers of 2, but it's actually mults of 4) gets pretty down to low-level representation, meaning it's not like a more surface level thing we can flip. (copied and pasted this to relevant part in Questions.md)
- [x] _M_ remove quotes from output of `bitvec_to_substates` when printing
  - M: I think this is solved (with `make_set_pretty_for_print` function in `print.py`. Let me know if there's anything missing)
  - B: Looks perfect!
- [x] _M_ `Equivalent` function in Z3?
  - M: seems you can just use `==` (I'm pretty sure but not 100% sure). I left the `Equivalent` function we had and replaced its body to the new definition `==`; if you notice any changes or anything going wrong, we can always switch back to the old one. However, I am almost certain that if equivalence isn't represented by `==`, then there is no function for equivalence (cf: https://microsoft.github.io/z3guide/docs/logic/propositional-logic, and in the list of all funcs in Z3, could not find anything that looked like it'd reasonably be equivalence)
  - B: Awesome! It works great!

## Definitions

- [x] _M_ `extended_verify` see strategies
- [x] _M_ `extended_falsify` see strategies
    - M: at the end of `semantics.py` (both extended verify and falsify)
- [x] _M_ recursive definition of `true` see strategies
    - M: at the end of `semantics.py`

## Models

- [ ] show `{ A \boxright (B \vee C), \neg(A \boxright B), \neg(A \boxright C) }` is sat
- [ ] show `{ (A \vee B) \boxright C, \neg(A \boxright B) }` is unsat

## Constraint Generators

- model constraints from `sentence_letters`
- evaluation constraints from `input_sentences`

## Overview

- [ ] _B_ move from set-fusion to binary fusion throughout
- [x] _B_ check that world-hood constraint is not needed for finite spaces









<!-- BONEYARD -->

# Completed

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
## Models

- [x] countermodel for `A, B \vdash A \boxright B`
  - [x] _B_ build concrete model
  - [:] debug Z3 crashing issues in `test_model.py`
    - [x] _B_ Locate the constraint that seems to be the problem
    - [.] figure out why this constraint is causing trouble
      - [x] _B_ email Graham

## Print

- [x] _M_ print all states in the model (some seem to be hidden)
- [x] _B_ assign either `world`, `possible`, or `impossible` to each printed state
  - [x] _M_ revise state labeling strategy I hacked together
  - [x] _M_ unlock `Var(0) == 1`; maybe there is a better way to find the extensions of predicates?
- [x] _B_ for each sentence letter `X`, print set of verifiers and set of falsify
  - [x] _M_ revise code I hacked together
- [x] _B_ for each counterfactual sentence `X \boxright Y`, print the set of `X` alternatives to `w`
  - B: I declared `alt_world` making this equivalent to `alternative`
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

- [x] _B_ `proposition` see strategies
- [x] _B_ add docstrings to `definitions.py`
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
