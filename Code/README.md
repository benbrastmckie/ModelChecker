# Model Checker

This project draws on the [Z3](https://github.com/Z3Prover/z3) theorem prover to provide tooling for proving theorems and finding countermodels for counterfactual conditional and modal claims.

Accessible [installation instructions](https://github.com/benbrastmckie/ModelChecker?tab=readme-ov-file#installation) are provided in the GitHub repository.

## Instructions

To generate a test file run `model-checker` without arguments.

Alternatively, run `model-checker path/to/test_file.py` if the `test_file.py` already exists.

A number of [examples](https://github.com/benbrastmckie/ModelChecker/blob/master/Examples/examples.py) are provided in the GitHub repository.

Each file must specify a set of `premises` which are treated conjunctively, `conclusions` which are treated disjunctively, and the number `N` of atomic states to include in each model.

Optionally, the user can specify the following settings in each file: 

- Print all Z3 constraints if a model is found: `print_cons_bool`
- Print the Z3 unsatisfiable core constraints if no model exists: `print_unsat_core_bool`
- Print all states including impossible states: `print_impossibe_states_bool`
- Prompt the user to append the output to the current file in a new file: `save_bool`

Users can override these settings by including the following flags:

- Include `-s` to prompt the user to save the output in a new file.
- Include `-c` to include Z3 constraints.
- Include `-i` to print impossible states.
- Include `-h` to print help information about the programs usage.

## Syntax

The language currently includes operators for the counterfactual conditional `boxright`, modal operators for necessity `Box` and possibility `Diamond`, and the extensional operators for conjunction `wedge`, disjunction `vee`, material conditional `rightarrow`, material biconditional `leftrightarrow`, and negation `neg`.

## Semantics

The semantics included is hyperintensional insofar as sentences are evaluated at _states_ which may be partial rather than total as in intensional semantic theories.
States are modeled by bitvectors of a specified length (e.g., `#b00101` has length `5`), where _state fusion_ is modeled by the bitwise OR operator `|`.
For instance, `#b00101 | #b11001 = #b11101`.
The _atomic states_ have exactly one occurrence of `1` and the _null state_ has no occurrences of `1`.
The space of states is finite and closed under fusion.

States are named by lowercase letters for the sake of printing readable countermodels.
Fusions are printed using `.` so that `a.b` is the fusion of the states `a` and `b`.
A state `a` is _part_ of a state `b` just in case `a.b = b`.
States may be either _possible_ or _impossible_ where the null state is required to be possible and every part of a possible state is possible.
The states `a` and `b` are _compatible_ just in case `a.b` is possible.
A _world state_ is any state that is both possible and includes every compatible state as a part.

Sentences are assigned _verifier states_ and _falsifier states_ where both the verifiers and falsifiers are required to be closed under fusion.
A sentence is _true at_ a world state `w` just in case `w` includes a verifier for that sentence as a part and _false at_ `w` just in case `w` includes a falsifier for that sentence as a part.
In order to ensure that sentence letters have at most one truth-value at each world state, a fusion `a.b` is required to be impossible whenever `a` is verifier for a sentence letter `A` and `b` is a falsifier for `A`.
Additionally, sentence letters have at least one truth-value at each world state by requiring every possible state to be compatible with either a verifier or falsifier for any sentence letter.

Negated sentences are verified by the falsifiers for the sentence negated and falsified by the verifiers for the sentence negated.
Conjunctions are verified by the pairwise fusions of verifiers for the conjuncts and falsified by falsifiers for either of the conjuncts or fusions thereof.
Conjunction and disjunction are dual operators obeying the standard idempotent and De Morgan laws.
The absorption laws do not hold, nor does conjunction distribute over disjunction, nor _vice versa_.
For a defense of the background theory of hyperintensional propositions, see this [paper](https://link.springer.com/article/10.1007/s10992-021-09612-w).

A modal sentence `Box A` is true at a world just in case every world state includes a part that verifies `A`, where `Diamond A` is true at a world just in case some world state includes a part that verifies `A`.
Given a world state `w` and state `s`, an `s`_-alternative_ to `w` is any world state to include `s` along with a maximal part of `w` that is compatible with `s` as parts.
A counterfactual conditional sentences `A boxright B` is true at a world state `w` just in case its consequent is true at any `s`-alternative to `w` for any verifier `s` for the antecedent of the counterfactual.

The semantic theory for counterfactual conditionals is motivated and further elaborated in this [draft](https://github.com/benbrastmckie/ModelChecker/blob/master/Counterfactuals.pdf).
This account builds on [Fine 2012](https://www.pdcnet.org/jphil/content/jphil_2012_0109_0003_0221_0246) and [Fine 2017](https://link.springer.com/article/10.1007/s10992-016-9413-y).
More information can be found in the GitHub [repository](https://github.com/benbrastmckie/ModelChecker). 

