# Model Checker

This project draws on the [Z3](https://github.com/Z3Prover/z3) theorem prover to provide tools for proving theorems and finding countermodels for counterfactual conditional and modal claims.

### Syntax

The language currently includes operators for the counterfactual conditional `boxright`, modal operators for necessity `Box` and possibility `Diamond`, and the extensional operators for conjunction `wedge`, disjunction `vee`, material conditional `rightarrow`, material biconditional `leftrightarrow`, and negation `neg`.

## Installation

Install [Python 3](https://www.python.org/downloads/) and run the following command in the terminal:

```
pip install model-checker
```

The project has the `z3-solver` as a dependency and should be installed automatically.
You can confirm that `z3-solver` is installed with:

```
pip show z3-solver
```

In case the dependency did not install automatically, you can run:

```
pip install z3-solver
```

## Updating

To update to the latest version of the `model-checker`, run:

```
pip install --upgrade model-checker
```

You can check the version with:

```
pip show model-checker
```

To receive updates about new releases, click the "Watch" button at the top right corner of the page.

## Instructions

NOTE: These instructions have been written so as not to presume any prior experience working in the terminal.
Experienced users can skip to the [following section](##Hyperintensional-Semantics).

### Navigation

Open the terminal (e.g., `Cmd + Space` on MacOS) and list the directories with `ls`. 
Navigate to your desired location with `cd directory/path/...`, replacing 'directory/path/...' accordingly.
If you do not know the full path, you can change directory one step at a time, running `ls` after each move.

Alternatively, if you are on MacOS, write `cd` followed by a space in the terminal but do not hit return.
Then you can open the desired project directory in Finder, dragging the Finder window onto the terminal.
This should paste the path into the terminal.
You can now hit return to change to the desired directory.

### Generate Test

To generate a test file run `model-checker` in the terminal without arguments.
Alternatively, run `model-checker path/to/test_file.py` if the `test_file.py` already exists.
If you are in the directory in which the `test_file.py` exists, you can run `model-checker test_file.py` without specifying the full (or relative) path.
A number of [examples](https://github.com/benbrastmckie/ModelChecker/blob/master/Examples/examples.py) are provided in the GitHub repository.

Each file must specify a set of `premises` which are treated conjunctively, `conclusions` which are treated disjunctively, and the number `N` of atomic states to include in each model.
Optionally, the user can specify whether to print the Z3 constraints when a model is found, or the unsatisfiable core when no model exists, as well as an option to save the output.

Files can be edited with your choice of text editor, e.g., run `vim test_file.py` to edit the file in the terminal.
It may be convenient to open a terminal for running the file in addition to a terminal/editor for making changes to the file.

## Hyperintensional Semantics

This section provides an outline of the underlying semantics along with links to further information. 

### States

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

Sentences are assigned _verifier states_ and _falsifier states_ where the both the verifiers and falsifiers are required to be closed under fusion.
In order to ensure that sentence letters have at most one truth-value at each world state, a fusion `a.b` is required to be impossible whenever `a` is verifier for a sentence letter `A` and `b` is a falsifier for `A`.
Additionally, sentence letters have at least one truth-value at each world state by requiring every possible state to be compatible with either a verifier or falsifier for any sentence letter.
These definitions were originally provided in [Fine 2017](https://link.springer.com/article/10.1007/s10992-016-9413-y).

Negated sentences are verified by the falsifiers for the sentence negated and falsified by the verifiers for the sentence negated.
Conjunctions are verified by the pairwise fusions of verifiers for the conjuncts and falsified by falsifiers for either of the conjuncts or fusions thereof.
Conjunction and disjunction are dual operators obeying the standard De Morgan laws.
The absorption laws do not hold, nor does conjunction distribute over disjunction, or _vice versa_.
True counterfactual and modal sentences are verified by the null state and falsified by no states.

The semantic theory for counterfactual conditionals is motivated and further elaborated in this [manuscript](https://github.com/benbrastmckie/ModelChecker/blob/master/Counterfactuals.pdf).
For the background theory of hyperintensional propositions, see this [paper](https://link.springer.com/article/10.1007/s10992-021-09612-w).

### Code Architecture

Conclusions are negated and added to a list which includes the premises.
The sentences in the list are then tokenized and converted to lists in prefix form so that the operator is the first entry.
Each prefix sentence is then passed to the semantics which evaluates that sentence at a designated world, returning a corresponding Z3 constraint.
These constraints are then combined with a number of frame constraints and added to a Z3 solver.
Z3 looks for a model, returning the unsatisfiable core constraints if none is found.
Otherwise, the elements of the model is stored in a class, drawing on these elements to print an appropriate output.
Settings are provided to include the Z3 constraints in the printed output, as well as prompting the user to save the output in a new file.


