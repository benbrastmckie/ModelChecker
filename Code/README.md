Whereas logic has traditionally focused on small language fragments, this project develops a unified semantics for Logos, a language of thought for AI agents to plan and reason with in order to promote consistency, transparency, and moral accountability.
This package draws on the [Z3](https://github.com/Z3Prover/z3) SMT solver to provide a unified programmatic semantics and methodology for developing modular semantic theories and exploring their logics.
Rather than computing whether a given sentence is a logical consequence of some set of sentences by hand, these resources allow users to establish logical consequence over finite models, finding readable countermodels if there are any.

In addition to the unified semantics for the Logos, this package provides support for users to develop their own programmatic semantic theories.
The [`TheoryLib`](src/model_checker/theory_lib/) includes the semantic theories that are available for users to import or use as a template to develop novel theories that can be contributed to the `TheoryLib` by pull request.

You can find more information about development [here](docs/DEVELOPMENT.md) and the background semantic theory provided for the Logos [here](http://www.benbrastmckie.com/research#access).
The semantics and logic for counterfactual conditionals is developed in this [paper](https://link.springer.com/article/10.1007/s10992-025-09793-8).

## _LOGOS_: A Formal Language of Thought

Intensional action is predicated on forethought and planning, where this applies to AI agents as much as it does to human agents.
Since strategic planning requires agents to contemplate counterfactual possibilities, temporal eventualities, causal and constitutive explanatory relationships, as well as reason under uncertainty about what is permissible or ought to be the case, it is important to equip AI with the conceptual resources needed to think in these ways.

_Logos_ is a unified formal language of thought which provides these logical resources and currently includes semantic clauses for the following operators:

- `neg` for _negation_
- `wedge` for _conjunction_
- `vee` for _disjunction_
- `rightarrow` for the _material conditional_
- `leftrightarrow` for the _material biconditional_
- `boxright` for the _must counterfactual conditional_
- `diamondright` for the _might counterfactual conditional_
- `Box` for _necessity_
- `Diamond` for _possibility_
- `Future` read 'it will always be the case that'
- `future` read 'it will be the case that'
- `Past` read 'it always has been the case that'
- `past` read 'it has been the case that'
- `leq` for _ground_ read 'sufficient for'
- `sqsubseteq` for _essence_ read 'necessary for'
- `equiv` for _propositional identity_ read 'just is for'
- `preceq` for _relevance_

To complete _Phase I_, I am working to extend the _Logos_ to include causal operators and quantifiers.
_Phase II_ of this project aims to include indicative conditionals, epistemic modals, belief and revision operators, and probability operators for reasoning under uncertainty.
Following these additions, _Phase III_ will include deontic modal and normative explanatory operators for cooperating with other agents in optimizing preferences and values.

More specific details about the implementation of these semantic clauses can be found in the [logos/README.md](Code/src/model_checker/theory_lib/logos/README.md) as well as information about the package architecture [model_checker/README.md](Code/src/model_checker/README.md).

## TheoryLib

Whereas the _Logos_ provides a unified semantic theory, the `TheoryLib` includes a library of pure semantic theories for small language fragments that may be variously combined and modified, each of which:

- Introduces the semantic primitives that make up a frame
- Defines the propositions over a frame needed to interpret the language
- Defines the models of the language by assigning sentence letters to propositions
- Provides semantic clauses for the primitive operators included in the language fragment
- Draws on the primitive operators to define a number of additional operators
- Includes a range of examples of logical consequences and countermodels

Local instances of the semantic theories within the `TheoryLib` may be generated using `model-checker -l THEORY_NAME` and then modified.
Once the extension of a new or modified semantic theory has been explored with adequate range of results, that theory can be contributed to the `TheoryLib` with a pull request.
See the [theory_lib/README.md](Code/src/model_checker/theory_lib/README.md) for further details on the existing theories as well as contributing new theories.

### Licensing

ModelChecker is licensed under the GNU General Public License v3.0 (GPL-3.0). This license ensures that the software remains free and open-source. Key aspects of the licensing include:

- **Core Package**: The main ModelChecker framework is licensed under GPL-3.0
- **Theory Library**: All theories in the `theory_lib` directory are also individually licensed under GPL-3.0
- **Derivative Works**: According to GPL-3.0 terms, any derivative works, including new theories based on existing ones, must maintain the same license
- **Academic Attribution**: Each theory includes a CITATION.md file with proper academic attribution information

### Contributing New Theories

When contributing a new theory to the ModelChecker framework:

1. Your contribution must be compatible with the GPL-3.0 license
2. Your theory will be automatically licensed under GPL-3.0 when added to the theory library
3. You retain copyright for your specific implementation but grant license under GPL-3.0
4. Academic attribution for your theory will be maintained in CITATION.md

The licensing structure is designed to ensure that the ModelChecker ecosystem remains open and accessible while providing proper attribution to theory authors.
More information can be found in [Docs/DEVELOPMENT.md](../Docs/DEVELOPMENT.md).

## Installation

### Basic Installation

For core functionality (command line interface and model checking):

```bash
pip install model-checker
```

This installs the essential `z3-solver` dependency needed for constraint solving.

### Optional Features

For Jupyter notebook integration with interactive visualizations:

```bash
pip install model-checker[jupyter]
```

For development tools (running tests):

```bash
pip install model-checker[dev]
```

For a complete installation with all features:

```bash
pip install model-checker[all]
```

### Need Help with Installation?

**📋 For detailed installation instructions, including terminal usage for beginners:** see [INSTALLATION.md](../Docs/INSTALLATION.md)

The detailed guide covers:
- How to open and use the terminal on Mac/Windows/Linux
- Step-by-step Python installation for all operating systems  
- Troubleshooting common installation issues
- Platform-specific installation notes
- Virtual environment setup

## Updating

Once installed, you can check the current version of the `model-checker` with:

```
model-checker -v
```

To update to the latest version, run:

```
model-checker -u
```

## Usage

Run `model-checker` in the terminal without arguments to create a new project with the following modules:

- `semantic.py` specifies the Z3 primitives, frame constraints, models, theory of logical consequence, defined semantic terms, theory of propositions, and print instructions for displaying countermodels.
- `operators.py` specifies the semantic clauses for the primitive operators included in the _Logos_ along with a number of defined operators.
- `examples/` includes modules with collections of examples and settings.
- `notebooks/` includes Jupyter Notebooks for exploring theories and discussing findings.
- `tests/` includes unit tests which aid in rapidly prototyping theories.

Alternatively, run `model-checker -l THEORY_NAME` to create a copy of the semantic theory with the name 'THEORY_NAME'.
The library of available semantic theories can be found [theory_lib/README.md](Code/src/model_checker/theory_lib/README.md).
Additional theories can be added by submitting a pull request.

After changing to the project directory that you created, run `model-checker project_examples.py` to find a countermodel if there is any.
The example settings specify the following inputs where the defaults are indicated below:

- The number of atomic states to include in each model: `N = 3`.
- An option to require all sentence letters to be contingent: `contingent = False`.
- An option to require all sentence letters to have at least one verifier and at least one falsifier: `non_empty = False`.
- An option to prevent sentence letters from having the null state as a verifier or a falsifier: `non_null = False`.
- An option to prevent sentence letters from having overlapping verifiers or falsifiers: `disjoint = False`.
- The maximum time in seconds to spend looking for a model: `max_time = 1`.

A number of general settings may also be specified with the following:

- An option to print impossible states: `print_impssible = False`.
- An option to print all Z3 constraints or unsatisfiable core constraints: `print_constraints = False`.
- An option to print the Z3 model if there is any: `print_z3 = False`.
- An option to prompt the user to append the output to the current file or to create a new file: `save_output = False`.

Examples are specified by defining a list as follows:

```
# CF_CM_1: COUNTERFACTUAL ANTECEDENT STRENGTHENING

CF_CM_1_premises = ['(A \\boxright C)']
CF_CM_1_conclusions = ['((A \\wedge B) \\boxright C)']
CF_CM_1_settings = {
    'N' : 3,
    'contingent' : True,
    'non_null' : True,
    'non_empty' : True,
    'disjoint' : False,
    'max_time' : 1,
}

CF_CM_1_example = [
    CF_CM_1_premises,
    CF_CM_1_conclusions,
    CF_CM_1_settings,
]
```

The example `CF_CM_1_example` includes:

- A list of zero or more premises that are treated conjunctively: `premises = []`.
- A list of zero or more conclusions that are treated disjunctively: `conclusions = []`.
- A dictionary of settings where the defaults are indicated above.

Alternatively, users can define a general stock of `example_settings`, reusing these for an number of examples.
Users can override these settings from the command line by including the following flags:

- Include `-c` to set `contingent = True`.
- Include `-d` to set `disjoint = True`.
- Include `-e` to set `non_empty = True`.
- Include `-i` to set `print_impossibe = True`.
- Include `-n` to set `non_null = True`.
- Include `-p` to set `print_constraints = True`.
- Include `-s` to set `save_bool = True`.
- Include `-z` to set `print_z3 = True`.

Additional flags have been included in order to manage the package version:

- Include `-h` to print help information about the package and its usage.
- Include `-v` to print the installed version number.
- Include `-u` to upgrade to the latest version.

## Jupyter Notebook Integration

ModelChecker can be used interactively in Jupyter notebooks, allowing for dynamic exploration of logical models with an interactive interface.

### Installation

To use ModelChecker in Jupyter notebooks, install with optional dependencies:

```bash
pip install ipywidgets matplotlib networkx
```

### Basic Usage

```python
from model_checker.notebook import check_formula

# Check a counterfactual formula
check_formula("((A \\vee B \\boxright C) \\rightarrow (A \\boxright C))")

# Check a modal formula
check_formula("(\\Box (A \\rightarrow B) \\rightarrow (\\Box A \\rightarrow \\Box B))")

# Check with premises
check_formula("B", premises=["A", "(A \\diamondright B)"])
```

### Interactive Explorer

For interactive exploration with a UI:

```python
from model_checker.notebook import InteractiveModelExplorer

# Create and display the explorer
explorer = InteractiveModelExplorer()
explorer.display()
```

The interactive explorer provides:

- Formula input with syntax highlighting
- Theory selection and settings customization
- Multiple visualization options
- Ability to find alternative models

For a demonstration, see the `examples/jupyter_demo.ipynb` notebook and the `examples/README_jupyter.md` documentation.

## Hyperintensional Semantics

The semantics for the _Logos_ is hyperintensional insofar as sentences are evaluated at _states_ which may be partial rather than total as in intensional semantic theories, fixing the truth values of only some sentence letters.
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

A _necessity sentence_ `Box A` is true at a world just in case every world state includes a part that verifies `A` and a _possibility sentence_ `Diamond A` is true at a world just in case some world state includes a part that verifies `A`.
Given a world state `w` and state `s`, an `s`_-alternative_ to `w` is any world state to include as parts both `s` and a maximal part of `w` that is compatible with `s`.
A _must counterfactual conditional sentences_ `A boxright B` is true at a world state `w` just in case its consequent is true at any `s`-alternative to `w` for any verifier `s` for the antecedent of the counterfactual.
A _might counterfactual conditional sentences_ `A boxright B` is true at a world state `w` just in case its consequent is true at some `s`-alternative to `w` for some verifier `s` for the antecedent of the counterfactual.
The semantic theory for counterfactual conditionals is motivated and further elaborated in this accompanying [paper](https://link.springer.com/article/10.1007/s10992-025-09793-8).

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

Instead of a Boolean lattice as in extensional and intensional semantics theories, the space of hyperintensional propositions forms a non-interlaced bilattice as described in the paper ["Identity and Aboutness"](https://link.springer.com/article/10.1007/s10992-021-09612-w), building on [Fine 2017](https://link.springer.com/article/10.1007/s10992-016-9413-y).
This framework is further extended in the paper ["Counterfactual Worlds"](https://link.springer.com/article/10.1007/s10992-025-09793-8). 
