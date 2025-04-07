# TODO

Specific tasks can be marked with _M_ or _B_ when relevant.

## Plan

- debug readme issue
- bimodal semantics
  - semantics
    - [ ] add abundance constraint
  - proposition
    - [ ] extension
  - operators
    - [x] future
    - [x] past
    - [x] necessity
- [ ] tools
  - [.] iterate
  - [ ] minimize
- [:] applications
  - [:] _M_ Champollion
    - [ ] all_bits
    - [.] examples
    - [x] divide into modules
  - [x] Fine
    - [x] implement
    - [x] separate from default
- [x] benchmarks
- [x] unit tests
  - [x] example unit tests
  - [x] add unit tests to theories
- [.] documentation
  - [x] code base
  - [:] default
  - [.] exclusion
  - imposition
  - bimodal
  - wiki
- [ ] subject-matter operators

## Applications

### Exclusion Semantics

- [.] _M_ test exclusion semantics
  - [.] build range of examples
  - [x] test frame constraints
    - [ ] add constraint that exclusion is nonempty?
    - [ ] go from complete lattice to boolean lattice
  - [ ] test settings
  - [.] compare with bilateral semantics
  - [.] test theorems proven in the paper
    - [ ] do the proofs require all the axioms?
    - [x] are any of the other axioms derivable?
- [.] documentation and cleanup
- [.] unit tests
  - [x] _B_ setup tests
  - [ ] add examples
- [ ] run comparisons with bilateral semantics
  - [ ] max atomic complexity `N` before timeout
  - [ ] max sentence/atomic complexity before too many constraints to build

## Documentation

- [.] theories
  - [:] default
    - [x] docstrings
    - [x] readme
    - [ ] design
  - exclusion
    - docstrings
    - [.] readme
    - design
  - imposition
    - docstrings
    - readme
    - design
  - bimodal
    - docstrings
    - readme
    - design
- [:] code base
  - [x] readme
  - [x] docstrings
    - [x] `__init__.py`
    - [x] `builder.py`
    - [x] `syntactic.py`
    - [x] `model.py`
    - [x] `utils.py`
  - [ ] wiki
    - [ ] methodology
    - [ ] architecture
    - [ ] semantics
- [ ] _B_ rewrite architecture doc
- [ ] _B_ write semantics doc
- [x] clean up project directory
  - [x] delete old
  - [x] decapitalize directories

## Implementation

1. [:] An Operator class for each primitive operator:
  - [x] the Operator class itself
    - [x] attribute for arity
    - [x] attribute for name
    - [x] confirm changes
  - [x] for each operator
    - [x] attribute for semantics
    - [x] methods for truth and falsity at a world
    - [x] methods for verification and falsification at a world
    - [x] printing methods
  - [:] operators to implement:
    - [:] defined operators
      - [x] debug given `sentence_obj` integration
      - [x] _M_ move derived definition upstream
      - [x] check definitional loops etc
      - [.] _B_ add doc strings
    - [x] might counterfactual
      - [x] defined
      - [x] unit tests
    - [x] modal
      - [x] primitive
      - [x] defined in terms of counterfactual and top
        - [x] debug
      - [x] unit tests
      - [ ] verifiers and falsifiers
    - [x] constitutive
      - [x] define primitive identity operator
      - [x] define essence, ground, and relevance in terms of identity
      - [x] add print methods
      - [x] debug true conclusion and false premise models
      - [x] unit tests
      - [ ] verifiers and falsifiers
    - [:] defined operators
      - [x] definitions
      - [ ] unit tests
    - [x] relevance
      - [x] semantics
      - [x] unit tests
      - [ ] verifiers and falsifiers
    - [:] imposition counterfactual
      - [x] add z3 primitive semantics
      - [x] add frame constraints
      - [x] define operator
      - [x] unit tests
      - [:] benchmarking
      - [ ] verifiers and falsifiers
    - [x] extensional
      - [:] unit tests
        - [ ] wedge
        - [ ] vee
    - [x] extremal
      - [x] define extremal elements in `hidden_things.py`
      - [x] define two primitive extremal operators in `exposed_things.py`
      - [x] add print methods
      - [ ] verifiers and falsifiers
      - [ ] unit tests
    - [x] must counterfactual
      - [x] debug
      - [x] add print method
      - [x] fix indenting
      - [x] unit tests
      - [ ] verifiers and falsifiers

## Z3 Research

- [ ] document problems
  - [ ] no quantifiers
- [ ] create Z3 issue
- [.] email CS faculty
  - [x] https://people.csail.mit.edu/mcarbin/ -- Michael Carbin
  - [x] http://adam.chlipala.net/ -- Adam Chlipala
  - [.] https://people.csail.mit.edu/asolar/ -- Armando Solar-Lezama
  - [ ] https://people.csail.mit.edu/henrycg/ -- Henry Corrigan-Gibbs
  - [ ] https://www.csail.mit.edu/person/frans-kaashoek -- Frans Kaashoek
  - [ ] https://people.csail.mit.edu/mengjia/ -- Megjia Yan










<!-- BONEYARD -->

# Completed

## Diagnostic Tools

- [x] error reporting
  - [x] convert bvs to states in raise Errors
  - [x] few remaining todos in `__main__.py`
- [x] refactor
  - [x] `builder.py`
  - [x] `main.py`
  - [x] `utils.py`
- [x] printouts
  - [x] add total time
- [x] flags
- [x] function to compare semantics
- [x] create project template
- [x] add check/continues and test

## Release v0.8

- [x] _B_ add utilities
  - [x] comparison
    - [x] maximizer
    - [x] example tester
  - [x] api
  - [x] readme
- [x] class architecture
- [x] implementation
- [x] api
- [x] cli
- [x] release
- [x] Semantics class
  - [x] add frame constraints on `exclusion`
- [x] Proposition class
- [x] Operators
  - [x] Not
  - [x] And
  - [x] Or
- [x] _M_ add identity to semantics
- [x] _B_ get settings to work in unilateral semantics
  - [x] `contingent`
  - [x] `non_null`
  - [x] `disjoint`
  - [x] `non_empty`

## CLI

- [x] add save functions to `ModelStructure`
- [x] flags
  - [x] print constraints
  - [x] print unsat core
  - [x] comparison
  - [x] maximizer
- [x] update help flag
- [x] fix templates
- [x] add default operators
- [x] check `no_model` cases
- [x] refactor printing and saving
- [x] progress bar

## Release v0.7

- [x] project template
- [x] bypass semantics
  - [x] generate `semantics` module
- [x] primitive imposition
  - [x] implement
  - [x] test

### Imposition Semantics

- [x] add Z3 primitive for `imposition` from old `model-checker`
- [x] add frame constraints on `imposition`
- [x] add imposition semantics for counterfactuals
- [x] run unit tests
  - [x] debug `IMP_CM2`
- [x] separate Fine's semantics

## API

- [x] create `__init__.py` and add all imports
- [x] move any functions with general uses to `utils.py`
  - [x] add useful functions from `utils.py` to `__init__.py`
- [x] rebuild package
- [x] create `api_example.py` to import from `model-checker`
- [x] confirm `api_example.py` works

## Documentation

- [x] _B_ revise pypi readme
  - [x] semantics overview
  - [x] update paper link
- [x] _B_ revise github readme
  - [x] semantics overview
  - [x] update paper link

## Implementation (class semantics)

1. [x] ModelConstraints class for storing user inputs and their results:
  - [x] arguments: operator classes, semantics class
  - [x] attributes:
    - [x] settings and flags
    - [x] premises and conclusions
    - [x] prefix premises and conclusions
    - [x] all subsentences of the premises and conclusions
    - [x] sentence letters
    - [x] Z3 constraints including (drawing on methods from semantics and operator classes):
      - [x] frame constraints
      - [x] model constraints (currently called proposition constraints)
      - [x] premise constraints
      - [x] conclusion constraints
      - [x] all constraints
  - [x] methods:
    - [x] infix to prefix methods
    - [x] subsentences extraction methods
    - [x] sentence letters extraction methods
    - [x] prefix to infix methods
    - [x] solver
2. [x] Semantics classes:
  - [x] attributes for Z3 primitives:
    - [x] verify
    - [x] falsify
    - [x] possible
    - [x] main world
    - [x] frame constraints
    - [x] premise and conclusion behavior
  - [x] semantic methods:
    - [x] fusion
    - [x] parthood
    - [x] compatible
    - [x] maximal
    - [x] world
    - [x] max-compatible
    - [x] alternative
    - [x] true-at
    - [x] false-at
    - [x] model constraints (assigning each sentence letter to a proposition)
  - [x] printing methods:
    - [x] divide `rec_print`
    - [x] verifiers for a sentence
    - [x] falsify for a sentence
    - [x] state fusion
  - [x] error reporting
    - [x] definitional loops
3. [x] Proposition class:
  - [x] syntactic attributes:
    - [x] prefix sentence
    - [x] infix sentence (called name)
    - [x] complexity
  - [x] semantic attributes:
    - [x] `verifiers`
    - [x] `falsifiers`
    - [x] `truth_at`
4. [x] ModelStructure class:
  - [x] arguments: ModelConstraints instance
  - [x] attributes:
    - [x] resulting Z3 model including:
      - [x] timeout value
      - [x] model status
      - [x] Z3 model
      - [x] model runtime
    - [x] dictionary for all propositions for all subsentences
  - [x] general methods for printing
  - [x] unsat core
  - [x] print benchmarks
- [x] pre-processing module
  - [x] add backslashes
  - [x] design algorithm for simplifying prefix sentences
    - NOTE: research `SymPy` for simplifying sentences
- [x] general
  - [x] _B_ move from set-fusion to binary fusion throughout
  - [x] fix imports
  - [x] _B_ check that world-hood constraint is not needed for finite spaces

## Documentation

- [x] _M_ doc strings for functions
- [x] _M_ revise architecture description
- [x] _B_ architecture description
- [x] _B_ expanded READMEs
- [x] examples
  - [x] move modal interaction to counterfactuals
- [x] screenshots
  - [x] add brief descriptions
  - [x] counterfactuals
  - [x] constitutive
  - [x] modal
  - [x] relevance

## Patch

- [x] disjoint subject-mater for all propositions
- [x] help flag
- [x] debug optimizer
  - [x] ask to increase time if timeout
  - [x] interrupt process if greater than `max_time`
  - [x] if timeout, should reduce N rather than halt
  - [x] seems to erroneously increase N

## v0.5 Release 

- [x] prompt user to increase time if timeout
- [x] add examples to test file
  - [:] reduce number
- [x] remove `non_null`
- [x] false-premise and true-conclusion models
  - [x] testing
  - [ ] debug
- [x] unit tests
  - [x] tests
    - [x] counterfactual
    - [x] extensional
    - [x] modal
      - [x] debug CM2
    - [x] constitutive
    - [x] relevance
  - [.] pytest
    - [x] get working
    - [ ] add documentation
- [x] complexity
  - [x] timeout on each run
  - [x] find minimal countermodel
  - [x] test validity up to timeout
- [x] remove assign skolem function
- [x] flags
  - [x] possible verifiers and falsifiers
  - [x] remove `print_unsat_core`
  - [x] timeout

## Examples

- [x] `\neg B, A \boxright B` does not entail `\neg B \boxright \neg A` 
  - works without `\neg B`.
  - [ ] _B_ step through `neg_unsat.md` building model
- [x] `\neg A, A \boxright C` does not entails `(A \wedge B) \boxright C`
  - works without `\neg A`.
- [ ] `A \boxright C, B \boxright C` entails `(A \wedge B) \boxright C`
- [x] `(A \wedge B) \boxright C` entails `A \boxright (B \boxright C)`
  - it is working by finding models where A and B incompatible
  - adding `\neg ((A \wedge B) \boxright D)` avoids this
  - will this come out in the wash once model checker can step through multiple models?
- [x] `A \boxright (B \boxright C)` does not entail `(A \wedge B) \boxright C`
  - this does not find models for N = 3
  - very slow for N = 5 (ran for minutes on the remote server)

## Package

- [x] added an update bash script
- [x] _B_ add version flag
- [x] release to MIT philosophy
- [x] final features
  - [x] permit modals and counterfactuals to occur in the antecedent
    - [x] implement
    - [x] debug
  - [x] evaluate conclusions disjunctively
    - [x] test
    - [x] debug
    - [x] update READMEs
  - [x] flags
    - [x] test
    - [x] update READMEs
    - [x] print impossible
- [x] cleanup
  - [x] `find_alt_bits` fix to make null state work
  - [x] _M_ move helper functions from `ModelStructure` to `model_definitions`
  - [x] _B_ review TODOs throughout
  - [x] _B_ replace dummy
  - [x] _B_ replace "comparison world" with "input world"
- [x] _B_ create package v0.1
- [x] _B_ submit to pip installer
- [:] _B_ release v0.2
  - [x] expose and test package commands
  - [x] include general print algorithm
  - [x] change execution instructions once the package is working
  - [x] include help in template output
  - [x] document package release protocols

## Print

- [x] printing
  - [x] _M_ `backslash` function, adding double backslashes if none
  - [x] _B_ separate premises and conclusions
  - [x] _M_ refactor `rec_print`
  - [x] _B_ refactor `print_to` and `save_to`
- [x] print the proposition for each sub-sentence
  - [x] _B_ print proposition for extensional sentences immediately
  - [x] _B_ design recursive structure in `strategies`
  - [x] _B_ tested new `print_props`
  - [x] _M_ define general print algorithm
    - [x] create new branch
    - [x] test and debug
    - [x] merge branch

- [x] _B_ add enumeration to `test_complete_datastructure`
- [x] move model builder definitions that concern bits from `print` into `model_definitions`
  - keep all definitions that concern states in `print`

## Data Structure

- [x] _M_ abstract model builder functions from `print` to build data structure functions in `model`
  - [x] sketch design in `strategies` for how modules relate
  - [x] _M_ divide classes into `ModelStructure` and `Propositions`
- [x] abstract on `eval_world` to generalize `alt_bits` function
Tasks that have been completed.

## Semantics

- [x] finite quantifiers
  - [x] debug
    - [x] forall
    - [x] exists
  - [x] test
- [x] say if premises, conclusions, or N are absent
- [:] semantics
  - [x] added exclude for `not` operator
    - [x] test
    - [ ] conform to lucas's definition
  - [x] essence and ground
    - [x] test
  - [x] relevance
    - [x] test
- [x] add modal operators
  - [x] semantics
  - [x] syntax
- [x] _B_ investigate why exhaustivity constraint crashes
- [x] add designated top elements
  - [x] _M_ fixed top constraints
  - B: tried in `add_top_nec` branch
- [x] _B_ alternative worlds
  - [x] adapt semantics to admit of iterated counterfactuals
  - [x] debug no alternatives (issue #17)
- [x] _M_ model constraints from `sentence_letters`
- [x] _M_ evaluation constraints from `input_sentences`
- [x] generate constraints from `infix_sentences`
  - [x] debug
- [x] _B_ organize semantics

## Refine and Optimize

- [x] `optional_generate_test` in `test_complete`
  - [x] abstract helper functions
  - [x] change to make output file a script
  - [x] add flags for saving and printing
- [x] _M_ `model_structure`
  - [x] invalid conditional operands
  - [x] clear out unused
- [x] if `Const(token, AtomSort)` happens for `token = A` multiple times
  - Z3 is able to eliminate the redundancy
  - see issue #28
- [x] _M_ `definitions`
  - [x] move declarations out of `definitions`
  - [x] divide between use cases: Z3 constraints vs print etc
  - [x] clear out unused
- [x] _M_ `print`
  - [x] clear out unused
- [x] _M_ `semantics`
  - [x] clear out unused
- [x] _M_ `syntax`
  - [x] clear out unused
- [x] _M_ `model_definitions`
  - [x] clear out unused
- [x] _M_ move `N` to `test_complete`
  - B: I have included `N` in `mod.solve()` and `mod.print_all()` in `test_complete` to help with this
  - [import loops](https://m.youtube.com/watch?v=UnKa_t-M_kM&list=PLBYZ1xfnKeDRqQLvg_tIx-hScTrUOFQVC&index=23&t=463s&pp=gAQBiAQB)
  - [x] _M_ implement in new branch
  - [x] _M_ debug and merge
- [x] closure under fusion constraint in `semantics`?
  - see issue #16
- [x] _B_ trace tools
  - [x] `Pyinstrument` visualizes the execution flow of the code
  - [x] `cProfile` for fine-grained times
  - [x] `unsat_core`
    - [x] _M_ debug
    - [.] _M_ adjust variable declarations
- [x] _B_ speed
  - [x] add benchmarks tooling
  - [.] multiprocessing
    - B: only useful for dividing tasks
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

- [x] _B_ `A \boxright C` and `\neg (A \boxright \neg B)` does not entail `\neg ((A \wedge B) \boxright C)`
- [x] weakening
- [x] absorption
- [x] transitivity
- [x] _M_ show that `A \boxright B` entails `A \rightarrow B` (in `ent_1.py`)
- [x] _M_ show that `A \boxright B, B \boxright C` do not entail `A \boxright C` (in `ent_2.py`)
- [x] _M_ show that `A \boxright B, A \wedge B \boxright C` entails `A \boxright C` (in `ent_3.py`)
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
