# TODO

Individual specific tasks can be marked with _M_ or _B_ when relevant.

## Data Structure

- [ ] design data structure module in markdown
  - [ ] abstract model builder functions from `print` to build data structure functions in `model_builder`
  - [ ] abstract on `eval_world` to generalize `alt_bits` function
- [ ] develop in new branch
- [ ] debug and merge

## Print

- [ ] print the proposition for each sub-sentence
  - [ ] design recursive structure
  - [ ] define sub-sentences for input sentences
  - [ ] define extensional operators for propositions
  - [ ] redesign print proposition functions to be recursive
    - [ ] _B_ add section to strategies

## Architecture

- [ ] how should the algorithm be organized across files?
  - [ ] sketch design in markdown
    - `test_complete` contains all relevant user inputs
      - inputs include `infix_sentences`
      - inputs include bitvector length `N`
    - `definitions` includes all basic definitions
      - move `N` from `definitions` to `test_complete`
      - [import loops](https://m.youtube.com/watch?v=UnKa_t-M_kM&list=PLBYZ1xfnKeDRqQLvg_tIx-hScTrUOFQVC&index=23&t=463s&pp=gAQBiAQB)
    - `util` contains all helper functions
      - move from semantics
    - `semantics` contains all semantic functions
      - recursively generate variable declarations
    - `model_builder` functions for building a data structure
    - `print` functions that operate on a data structure
  - [ ] implement in new branch
  - [ ] debug and merge

## Semantics

- [ ] _M_ generate variables to be declared alongside Z3 constraints
  - HOLD
- [ ] _B_ alternative worlds
  - [ ] adapt semantics to admit of iterated counterfactuals
  - [ ] debug no alternatives (issue #17)
- [ ] pipe Z3 constraints into output file
- [ ] _B_ investigate why exhaustivity constraint crashes

## Examples

- [ ] `test_complete` cases
  - [ ] weakening
  - [ ] absorption
  - [ ] transitivity
- [ ] _B_ provide countermodels by hand
  - [ ] `ent_2`
  - [ ] `poss_strength`
    - [ ] `A => C` is true though there is an `A`-alternative where `C` is false
    - [ ] replacing `verify` with `non_null_verify` eliminates models
      - [ ] _B_ check validity by hand

## Refine and Optimize

- [ ] simplify `definitions`
  - [ ] move declarations out of `definitions`
  - [ ] clear out unused
- [ ] closure under fusion constraint in `semantics`?
  - see issue #16
- [:] _B_ speed
  - [x] add benchmarks tooling
  - [.] multiprocessing
    - B: couldn't get this to work
- [x] _B_ trace tools
  - [x] `Pyinstrument` visualizes the execution flow of the code
  - [x] `cProfile` for fine-grained times
- [ ] Z3 guru
  - [:] ask Graham
  - [.] email CS faculty
    - [ ] (https://people.csail.mit.edu/mcarbin/)[Michael Carbin]
    - [ ] (https://people.csail.mit.edu/henrycg/)[Henry Corrigan-Gibbs]
    - [ ] (http://adam.chlipala.net/)[Adam Chlipala]
    - [ ] (https://www.csail.mit.edu/person/frans-kaashoek)[Frans Kaashoek]
    - [ ] (https://people.csail.mit.edu/mengjia/)[Megjia Yan]

## Pre-Processing

- [ ] pre-processing module
  - NOTE: hold until necessary
  - [ ] design algorithm for simplifying prefix sentences
  - [ ] research `SymPy` for simplifying sentences

## Overview

- [ ] _B_ move from set-fusion to binary fusion throughout
- [:] _B_ check that world-hood constraint is not needed for finite spaces









<!-- BONEYARD -->

# Completed

Tasks that have been completed.

## Semantics

- [x] _M_ model constraints from `sentence_letters`
- [x] _M_ evaluation constraints from `input_sentences`
- [x] generate constraints from `infix_sentences`
  - [x] debug
- [x] _B_ organize semantics

## Refine and Optimize

  - [x] _B_ ssh to supercomputer
    - [x] https://engaging-ood.mit.edu/pun/sys/dashboard
      - [x] browser based only?
      - [x] is there Z3 access?
      - [x] add info to `general`
    - [ ] https://mybinder.org/
      - [ ] explore ssh options
      - [ ] setup a new public repo
      - [ ] setup `enviornment.yml`
- [x] _B_ ask Graham about
  - [x] existential quantifier claims
  - [x] hexadecimal for `N > 4`
- [x] do we still need simplify?
  - B: I think not; last instance was removed from `bit_fusion` in `definitions`
- [x] `world_bits` sometimes includes non-maximal worlds
  - M: do you have any examples (ie, file name and N value) for when this is true, to try to see what's going on?
  - B: yes, I found a bunch of examples and created an issue to document
  - M: if this is issue #13, I think this is now fixed!
- [x] _M_ avoid having to make `N` not equal to a multiple of 4
  - M: try manual route
  - B: I added an issue about this with some points from Graham
- [x] _B_ push conversion from bits to states late in print
- [x] _B_ integrate `alt_worlds`
- [x] _M_ functions in `print.py` can probably be improved (see notes there)
  - B: looks much better!
  - B: replacing `string_part` in `print.py` with `bit_part` seems to work, but my linter doesn't like it. not sure if that is any concern.
  - M: Cleaned up what I hadn't been able to get to before and left comments—feel free to delete any comments that are resolved/solved
  - M: linter issue unsolved, but I wasn't getting it on my end, maybe your linter is stricter than mine lol
- [x] _M_ allow for more than 26 atomic states in `bitvec_to_substates`
  - M: I have a soln, something that seemed intuitive to me (not subindices)
  - B: looks great!
- [x] _M_ remove quotes from output of `bitvec_to_substates` when printing
  - M: I think this is solved (with `make_set_pretty_for_print` function in `print.py`. Let me know if there's anything missing)
  - B: Looks perfect!
- [x] _M_ `Equivalent` function in Z3?
  - M: seems you can just use `==` (I'm pretty sure but not 100% sure). I left the `Equivalent` function we had and replaced its body to the new definition `==`; if you notice any changes or anything going wrong, we can always switch back to the old one. However, I am almost certain that if equivalence isn't represented by `==`, then there is no function for equivalence (cf: https://microsoft.github.io/z3guide/docs/logic/propositional-logic, and in the list of all funcs in Z3, could not find anything that looked like it'd reasonably be equivalence)
  - B: Awesome! It works great!

## Models

- [.] _M_ show that `A \boxright B` entails `A \rightarrow C` (in `ent_1.py`)
- [:] _M_ show that `A \boxright B, B \boxright C` do not entail `A \boxright C` (in `ent_2.py`)
- [:] _M_ show that `A \boxright B, A \wedge B \boxright C` entails `A \boxright C` (in `ent_3.py`)
- [.] _M_ show that `A \boxright B, \neg B` do not entail `\neg B \boxright \neg A` (in `ent_4.py`)
- [x] _B_ show `{ A \boxright (B \vee C), \neg(A \boxright B), \neg(A \boxright C) }` is sat
- [x] _B_ show `{ (A \vee B) \boxright C, \neg(A \boxright B) }` is unsat
- [x] countermodel for `A, B \vdash A \boxright B`
  - [x] _B_ build concrete model
  - [:] debug Z3 crashing issues in `test_model.py`
    - [x] _B_ Locate the constraint that seems to be the problem
    - [.] figure out why this constraint is causing trouble
      - [x] _B_ email Graham

## Print

- [x] _M_ extract helper function from `alt_bits` def in `print.py`
- [x] _B_ abstract on multiple occurrences of `all_bits`
- [x] _B_ separate model building, eval building, and printing elements (see NOTE in `print.py`)
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

- [x] _M_ `extended_verify` see strategies
- [x] _M_ `extended_falsify` see strategies
    - M: at the end of `semantics.py` (both extended verify and falsify)
- [x] _M_ recursive definition of `true` see strategies
    - M: at the end of `semantics.py`
- [x] _B_ `proposition` see strategies
- [x] _B_ add docstrings to `definitions.py`
- [x] _B_ maximal
- [x] _B_ compatible
- [x] _B_ world
- [x] _B_ create test file

## Python

- [x] _M_ sentence letter extractor
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

- [x] _B_ model checker design strategies
  - [:] model constraints
    - [x] _B_ outline
    - [x] _B_ email Graham
    - [x] _B_ revise constraints
    - [:] _B_ run strategies by Graham
  - [x] _B_ model builder
    - [x] _B_ outline
    - [x] _B_ revise

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
