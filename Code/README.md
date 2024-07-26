# Model Checker

This project draws on the [Z3](https://github.com/Z3Prover/z3) SMT solver to provide tooling for finding hyperintensional countermodels and establishing validity over models up to a user specified level of complexity for inferences in a propositional language with the following operators:

  - `neg` for _negation_
  - `wedge` for _conjunction_
  - `vee` for _disjunction_
  - `rightarrow` for the _material conditional_
  - `leftrightarrow` for the _material biconditional_
  - `boxright` for the _must counterfactual conditional_
  - `circleright` for the _might counterfactual conditional_
  - `Box` for _necessity_
  - `Diamond` for _possibility_
  - `leq` for _ground_ read 'sufficient for'
  - `sqsubseteq` for _essence_ read 'necessary for'
  - `equiv` for _propositional identity_ read 'just is for'
  - `preceq` for _relevance_
  <!-- - `not` for _exclusion_ -->

Accessible [installation instructions](https://github.com/benbrastmckie/ModelChecker?tab=readme-ov-file#installation) are provided in the GitHub repository.

## Usage

To generate a test file run `model-checker` in the terminal without arguments.
Alternatively, run `model-checker path/to/test_file.py` if the `test_file.py` already exists.
A number of [examples](https://github.com/benbrastmckie/ModelChecker/blob/master/Examples/examples.py) are provided in the GitHub repository.

Each file may specify the following inputs where the defaults are specified below:

  - A list of zero or more premises that are treated conjunctively: `premises = []`.
  - A list of zero or more conclusions that are treated disjunctively: `conclusions = []`.
  - The number of atomic states to include in each model: `N = 3`.
  - The maximum time in seconds to spend looking for a model: `max_time = 1`.

Optionally, the user can specify a number of additional settings where defaults are provided below:

  - Require all sentence letters to express contingent propositions: `contingent_bool = False`.
  - Require all sentence letters to express propositions with disjoint subject-matters: `contingent_bool = False`.
  - Find a model with the smallest number of atomic elements: `optimize_bool = False`.
  - Print all Z3 constraints or unsatisfiable core constraints: `print_cons_bool = False`.
  - Show impossible states included in the model: `print_impossibe_states_bool = False`.
  - Prompt the user to append the output to the current file or to a new file: `save_bool = False`.

Users can override these settings from the command line by including the following flags:

  - Include `-c` to set `contingent_bool = True`.
  - Include `-d` to set `disjoint_bool = True`.
  - Include `-o` to set `optimize_bool = True`.
  - Include `-p` to set `print_cons_bool = True`.
  - Include `-i` to set `print_impossibe_states_bool = True`.
  - Include `-s` to set `save_bool = True`.

Additional flags have been included in order to manage the package version:

  - Include `-h` to print help information about the package and its usage.
  - Include `-v` to print the installed version number.
  - Include `-u` to upgrade to the latest version.

The following section will sketch the underlying semantics.
More information can be found in the GitHub [repository](https://github.com/benbrastmckie/ModelChecker) as well as in this recent [manuscript](https://github.com/benbrastmckie/ModelChecker/blob/master/Counterfactuals.pdf). 

## Hyperintensional Semantics

The semantics is hyperintensional insofar as sentences are evaluated at _states_ which may be partial rather than total as in intensional semantic theories.
States are modeled by bitvectors of a specified length (e.g., `#b00101` has length `5`), where _state fusion_ is modeled by the bitwise OR operator `|`.
For instance, `#b00101 | #b11001 = #b11101`.
The _atomic states_ have exactly one occurrence of `1` and the _null state_ has no occurrences of `1`.
The space of states is finite and closed under fusion.

States are named by lowercase letters in order to print readable countermodels.
Fusions are printed using `.` where `a.b` is the fusion of the states `a` and `b`.
A state `a` is _part_ of a state `b` just in case `a.b = b`.
States may be either _possible_ or _impossible_ where the null state is required to be possible and every part of a possible state is possible.
The states `a` and `b` are _compatible_ just in case `a.b` is possible.
A _world state_ is any state that is both possible and includes every compatible state as a part.

Sentences are assigned _verifier states_ and _falsifier states_ where both the verifiers and falsifiers are required to be closed under fusion.
A sentence is _true at_ a world state `w` just in case `w` includes a verifier for that sentence as a part and _false at_ `w` just in case `w` includes a falsifier for that sentence as a part.
In order to ensure that sentence letters have at most one truth-value at each world state, a fusion `a.b` is required to be impossible whenever `a` is verifier for a sentence letter `A` and `b` is a falsifier for `A`.
Additionally, sentence letters are guaranteed to have at least one truth-value at each world state by requiring every possible state to be compatible with either a verifier or falsifier for any sentence letter.

A _negated sentence_ is verified by the falsifiers for the sentence negated and falsified by the verifiers for the sentence negated.
A _conjunctive sentence_ is verified by the pairwise fusions of verifiers for the conjuncts and falsified by falsifiers for either of the conjuncts or fusions thereof.
A _disjunctive sentence_ is verified by the verifiers for either disjunct or fusions thereof and falsified by pairwise fusions of falsifiers for the disjuncts.
Conjunction and disjunction are dual operators obeying the standard idempotence and De Morgan laws.
The absorption laws do not hold, nor does conjunction distribute over disjunction, nor _vice versa_.
For a defense of the background theory of hyperintensional propositions, see this [paper](https://link.springer.com/article/10.1007/s10992-021-09612-w).

<!-- By contrast with the _bilateral_ extensional operators which treat both verifiers and falsifiers, the semantics for `not` is _unilateral_. -->
<!-- In particular `not A` is verified by a state `s` just in case every non-null part of `s` is incompatible with a verifier for `A` and every verifier for `A` is incompatible with some non-null part of `s`. -->
<!-- This semantics is further motivated and elaborated in [Bernard and Champollion](https://ling.auf.net/lingbuzz/007730/current.html) and included here for comparison. -->

A _necessity sentence_ `Box A` is true at a world just in case every world state includes a part that verifies `A` and a _possibility sentence_ `Diamond A` is true at a world just in case some world state includes a part that verifies `A`.
Given a world state `w` and state `s`, an `s`_-alternative_ to `w` is any world state to include as parts both `s` and a maximal part of `w` that is compatible with `s`.
A _must counterfactual conditional sentences_ `A boxright B` is true at a world state `w` just in case its consequent is true at any `s`-alternative to `w` for any verifier `s` for the antecedent of the counterfactual.
A _might counterfactual conditional sentences_ `A boxright B` is true at a world state `w` just in case its consequent is true at some `s`-alternative to `w` for some verifier `s` for the antecedent of the counterfactual.
The semantic theory for counterfactual conditionals is motivated and further elaborated in this accompanying [paper](https://github.com/benbrastmckie/ModelChecker/blob/master/Counterfactuals.pdf).
This account builds on [Fine 2012](https://www.pdcnet.org/jphil/content/jphil_2012_0109_0003_0221_0246) and [Fine2012a](https://link.springer.com/article/10.1007/s11229-012-0094-y?error=cookies_not_supported&code=5166a4da-1834-438c-9f93-75b61f58b6db).

A _grounding sentence_ `A leq B` may be read '`A` is _sufficient for_ `B`' and an _essence sentence_ `A sqsubseteq B` may be read '`A` is _necessary for_ `B`'.
A _propositional identity sentence_ `A equiv B` may be read '`A` _just is for_ `B`'.
A _relevance sentence_ `A preceq B` may be read '`A` _is wholly relevant to_ `B`'.
The semantics for ground requires every verifier for the antecedent to be a verifier for the consequent, any fusion of a falsifier for the antecedent and consequent to be a falsifier for the consequent, and any falsifier for the consequent to have a part that falsifies the antecedent.
The semantics for essence requires every fusion of a verifier for the antecedent and consequent to be a verifier for the consequent, any verifier for the consequent must have a part that verifies the antecedent, and every falsifier for the antecedent to be a falsifier for the consequent.
The semantics for propositional identity requires the two arguments to have the same verifiers and falsifiers.
The semantics for relevance requires any fusion of verifiers for the antecedent and consequent to be a verifier for the consequent and, similarly, any fusion of falsifiers for the antecedent and consequent to be a falsifier for the consequent.
Whereas the first three constitutive operators are interdefinable, relevance is definable in terms of the other constitutive operators but not _vice versa_:

- `A leq B  :=  neg A sqsubseteq neg B  :=  (A vee B) equiv B`.
- `A sqsubseteq B  :=  neg A leq neg B  :=  (A wedge B) equiv B`.
- `A equiv B  :=  (A leq B) wedge (B leq A)  :=  (A sqsubseteq B) wedge (B sqsubseteq A)`.
- `A preceq B  :=  (A wedge B) leq B :=  (A vee B) sqsubseteq B`.

Instead of a Boolean lattice as in extensional and intensional semantics theories, the space of hyperintensional propositions forms a non-interlaced bilattice as described in this [paper](https://link.springer.com/article/10.1007/s10992-021-09612-w), building on [Fine 2017](https://link.springer.com/article/10.1007/s10992-016-9413-y).

More information can be found in the GitHub [repository](https://github.com/benbrastmckie/ModelChecker). 
