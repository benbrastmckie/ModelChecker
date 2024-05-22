# Model Checker

This project draws on the [Z3](https://github.com/Z3Prover/z3) theorem prover to provide tooling for finding countermodels for counterfactual conditional and modal claims.

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

More information can be found [here](https://packaging.python.org/en/latest/tutorials/installing-packages/).

## Updating

You can check the current version with:

```
model-checker -v
```

For more information, you can run:

```
pip show model-checker
```

To update to the latest version of the `model-checker`, run:

```
model-checker -u
```

To receive updates about new releases, click the "Watch" button at the top right corner of this page.

## Instructions

NOTE: For users new to working in the terminal, see the [Terminal](##Terminal) instructions below.

### Usage

To generate a test file run `model-checker` in the terminal without arguments.
Alternatively, run `model-checker path/to/test_file.py` if the `test_file.py` already exists.
A number of [examples](https://github.com/benbrastmckie/ModelChecker/blob/master/Examples/examples.py) are provided in the GitHub repository.

Each file must specify a set of `premises` which are treated conjunctively, `conclusions` which are treated disjunctively, and the number `N` of atomic states to include in each model.
Optionally, the user can specify whether to print the Z3 constraints when a model is found, or the unsatisfiable core when no model exists, as well as an option to save the output.
These settings are specified with the Boolean values `True` and `False`:

- Print all Z3 constraints if a model is found: `print_cons_bool`
- Print the Z3 unsatisfiable core constraints if no model exists: `print_unsat_core_bool`
- Print all states including impossible states: `print_impossibe_states_bool`
- Prompt the user to append the output to the current file in a new file: `save_bool`

Users can override these settings by including the following flags:

- Include `-c` to include Z3 constraints.
- Include `-i` to print impossible states.
- Include `-s` to prompt the user to save the output in a new file.

Users can print help information, the current version, and upgrade to the latest version by including the following flags:

- Include `-h` to print help information about the programs usage.
- Include `-v` to print the installed version number.
- Include `-u` to upgrade to the latest version.

### Terminal

Open the terminal (e.g., `Cmd + Space` on MacOS) and list the directories with `ls`. 
Navigate to your desired location with `cd directory/path/...`, replacing 'directory/path/...' accordingly.
If you do not know the full path, you can change directory one step at a time, running `ls` after each move.

Alternatively, if you are on MacOS, write `cd` followed by a space in the terminal but do not hit return.
Then you can open the desired project directory in Finder, dragging the Finder window onto the terminal.
This should paste the path into the terminal.
You can now hit return to change to the desired directory.
If you are in the directory in which the `test_file.py` exists, you can run `model-checker test_file.py` without specifying the full (or relative) path to that file.

Files can be edited with your choice of text editor, e.g., run `vim test_file.py` to edit the named file in the terminal with Vim (for help, run `vimtutor`).
If you do not want to use Vim, you can use any other text editor, e.g., TextEdit on MacOS.
Alternatively, you might consider using [NeoVim](https://github.com/benbrastmckie/.config), [VSCode](https://code.visualstudio.com/), or [PyCharm](https://www.jetbrains.com/pycharm/).

## Hyperintensional Semantics

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
Given a world state `w` and state `s`, an `s`_-alternative_ to `w` is any world state to include as parts both `s` and a maximal part of `w` that is compatible with `s`.
A counterfactual conditional sentences `A boxright B` is true at a world state `w` just in case its consequent is true at any `s`-alternative to `w` for any verifier `s` for the antecedent of the counterfactual.

The semantic theory for counterfactual conditionals is motivated and further elaborated in this [draft](https://github.com/benbrastmckie/ModelChecker/blob/master/Counterfactuals.pdf).
This account builds on [Fine 2012](https://www.pdcnet.org/jphil/content/jphil_2012_0109_0003_0221_0246) and [Fine 2017](https://link.springer.com/article/10.1007/s10992-016-9413-y).
More information can be found in the GitHub [repository](https://github.com/benbrastmckie/ModelChecker). 


### Code Architecture

Conclusions are negated and added to a list which includes the premises.
The sentences in the list are then tokenized and converted to lists in prefix form so that the operator is the first entry.
Each prefix sentence is then passed to the semantics which evaluates that sentence at a designated world, returning a corresponding Z3 constraint.
These constraints are then combined with a number of frame constraints and added to a Z3 solver.
Z3 looks for a model, returning the unsatisfiable core constraints if none is found.
Otherwise, the elements of the model is stored in a class, drawing on these elements to print an appropriate output.
Settings are provided to include the Z3 constraints in the printed output, as well as prompting the user to save the output in a new file.


