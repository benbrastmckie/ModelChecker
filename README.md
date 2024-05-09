# Model Checker

This project draws on the [Z3](https://github.com/Z3Prover/z3) theorem prover to provide tools for proving theorems and finding countermodels for counterfactual conditional and modal claims.

## Installation

Install [Python 3](https://www.python.org/downloads/) and run the following commands in the terminal:

```
pip install model-checker
```

The project has the `z3-solver` as a dependency.
In case the dependency does not install automatically, you can run:

```
pip install z3-solver
```

## Instructions

NOTE: These instructions have been written so as not to presume any prior experience working in the terminal.
Experienced users can skip to the [following section](##Hyperintensional-Semantics).

### Navigation

Open the terminal (e.g., `Cmd + Space` on MacOS) and list the directories with `ls`. 
Navigate to your desired location with `cd directory/path/...`, replacing 'directory/path/...' accordingly.
If you do not know the full path, you can change directory one step at a time, running `ls` after each move.

Alternatively, if you are on MacOS, write `cd` followed by a space in the terminal but do not hit return.
Then you can open the desired project directory in Finder, dragging the Finder window onto the terminal.
This should paste the path into the terminal, and so you can now hit return.

### Generate Test

To generate a test file run `model-checker` in the terminal without arguments.
Alternatively, run `model-checker path/to/test_file.py` if the `test_file.py` already exists.
A number of [examples](https://github.com/benbrastmckie/ModelChecker/blob/master/Examples/examples.py) are provided in the GitHub repository.

Each file must specify a set of `premises` and `conclusions` which are treated conjunctively, and the number `N` of atomic states to include in each model.
Optionally, the user can specify whether to print the Z3 constraints when a model is found, or the unsatisfiable core when no model exists, as well as an option to save the output.

Files can be edited with your choice of text editor, e.g., run `vim test_file.py` to edit the file in the terminal.
It may be convenient to open a terminal for running the file in addition to a terminal/editor for making changes to the file.

## Hyperintensional Semantics

This section provides an outline of the underlying semantics along with links to further information. 

### Syntax

The language currently includes operators for the counterfactual conditional `boxright`, modal operators for necessity `Box` and possibility `Diamond`, and the extensional operators for conjunction `wedge`, disjunction `vee`, material conditional `rightarrow`, material biconditional `leftrightarrow`, and negation `neg`.

### State Semantics

The semantics included is hyperintensional insofar as sentences are evaluated at states which may be partial rather than total as in intensional semantic theories.
States are modeled by bitvectors (e.g., `#b00101`) of a specified length, where state fusion is modeled by the bitwise OR operator `|`.
For instance, `#b00101 | #b11001 = #b11101`.
Atomic states have exactly one occurrence of `1` and the null state includes only `0`s.
States are named by lowercase letters for the sake of printing readable countermodels.

### Code Architecture

Conclusions are negated and added to a list which includes the premises.
The sentences in the list are then tokenized and converted to lists in prefix form so that the operator is the first entry.
Each prefix sentence is then passed to the semantics which evaluates that sentence at a designated world, returning a corresponding Z3 constraint.
These constraints are then combined with a number of frame constraints and added to a Z3 solver.
Z3 looks for a model, returning the unsatisfiable core constraints if none is found.
Otherwise, the elements of the model is stored in a class, drawing on these elements to print an appropriate output.
Settings are provided to include the Z3 constraints in the printed output, as well as prompting the user to save the output in a new file.


