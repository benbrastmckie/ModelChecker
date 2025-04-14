# Model-Checker: Hyperintensional Semantics

The hyperintensional semantics implements the semantic theories defended in the following papers:

- Brast-McKie (2021) ["Identity and Aboutness"](https://link.springer.com/article/10.1007/s10992-021-09612-w), Journal of Philosophical Logic
- Brast-McKie (2025) ["Counterfactual Worlds"](https://github.com/benbrastmckie/ModelChecker/blob/master/Counterfactuals.pdf), Journal of Philosophical Logic

This work builds on the truthmaker semantics developed by Kit Fine in the following papers:

- Fine (2017) ["Counterfactuals without Possible Worlds"](https://link.springer.com/article/10.1007/BF00248737), Journal of Philosophy
- Fine (2017) ["A Theory of Truthmaker Content I: Conjunction, Disjunction and Negation"](https://link.springer.com/article/10.1007/s10992-016-9413-y), Journal of Philosophical Logic
- Fine (2017) ["A Theory of Truthmaker Content II: Subject-Matter, Common Content, Remainder and Ground"](https://doi.org/10.1007/s10992-016-9419-5) Journal of Philosophical Logic
- Fine (2017) ["Truthmaker Semantics"](https://doi.org/10.1002/9781118972090.ch22), Wiley-Blackwell

I have implemented Fine's semantics for the counterfactual conditional alongside the account that I defend for comparison.
Whereas Fine's semantics is provided for `\\imposition`, the semantics I defend will be used to interpret `\\boxright`.

In order to provide an overview of the hyperintensional semantics, this document will include the following sections below:

- Package Contents
- Basic Usage
- Unit Testing
- Programmatic Semantics

The hyperintensional semantics provides an example of the more general programmatic methodology developed alongside this project.
Further details about the more general project can also be found in the project [repository](https://github.com/benbrastmckie/ModelChecker).

## Package Contents

This package includes the following modules:

- `semantic.py` defines the default semantics for the operators included.
- `operators.py` defines the primitive and derived operators.
- `examples.py` defines a number of examples to test.
- `__init__.py` to expose definitions.

The contents of each will be provided in the following subsections.

### Default Theory Settings

The default theory defines the following settings:

```python
DEFAULT_EXAMPLE_SETTINGS = {
    # Number of atomic states
    'N': 3,
    # Whether sentence_letters are assigned to contingent propositions
    'contingent': False,
    # Whether sentence_letters are assigned to distinct states
    'disjoint': False,
    # Maximum time Z3 is permitted to look for a model
    'max_time': 1,
    # Whether a model is expected or not (used for unit testing)
    'expectation': True,
}

DEFAULT_GENERAL_SETTINGS = {
    "print_impossible": False,
    "print_constraints": False,
    "print_z3": False,
    "save_output": False,
    "maximize": False,
    # Note: align_vertically is not included since it's only relevant for bimodal theory
}
```

The default theory explicitly omits settings that aren't applicable to it, following the principle that each theory should only define settings relevant to its specific semantics. For example, the default theory doesn't define:

- `M`: Only relevant for theories with a temporal dimension (like bimodal)
- `align_vertically`: Only relevant for theories with time-based visualization (like bimodal)

If you provide command-line flags for settings that don't exist in a theory (like using `-e` for 'non_empty' with the default theory), you'll see a warning that the flag doesn't correspond to any known setting, but the system will continue running normally.

For more information about how the settings system handles theory-specific settings, please see the [Settings Documentation](../../settings/README.md).

### `Semantic.py`

This module is central to the model checker as it specifies the semantic primitives that everything else builds upon.
The `semantic.py` module consists of three main classes that work together:

1. **Semantics Class**

- This class provides the foundation for the hyperintensional semantic theory
  - The class inherits from the ModelDefaults class in `model.py`
  - Specifies the Z3 primitives that make up a frame along with frame constraints
- Defines Z3 semantic primitives:
  - `verify`: Maps states and atoms to truth values
  - `falsify`: Maps states and atoms to falsity values
  - `possible`: Determines if a state is possible
  - `main_world`: Designated world for evaluation
- Defines derived semantic relations in terms of primitives:
  - `compatible`: Tests if states' fusion is possible
  - `maximal`: Tests if state includes all compatible states
  - `is_world`: Tests if state is possible and maximal
  - `max_compatible_part`: Finds largest compatible substate
  - `is_alternative`: Tests for alternative worlds
  - `true_at`/`false_at`: Evaluates sentences at worlds
  - `extended_verify`/`extended_falsify`: Handles complex sentences

2. **Proposition Class**

- The class defines the hyperintensional propositions used to interpret sentences
  - Inherits from PropositionDefaults in `model.py`
  - Draws on the Semantics class for core semantic operations
- Before a Z3 model is found, the class generates model constraints on the verification/falsification of sentence letters by states, including:
  - Required constraints that yield classical behavior:
    - Preventing truth value gaps
    - Preventing truth value gluts
  - Optional constraints that can be enabled via settings:
    - Ensuring contingency
    - Requiring non-empty verifier/falsifier sets
    - Enforcing disjoint atomic propositions
    - Preventing null states from being verifiers/falsifiers
- Once a Z3 model is found, the class interprets sentences by assigning them to a hyperintensional proposition
  - Each hyperintensional proposition consist of a set of verifier states and a set of falsifier states
  - Hyperintensional propositions are then used to identify the world states in which the proposition is true
  - The class also specifies how hyperintensional propositions are to be printed

3. **ModelStructure Class**

- Constructs and manages the overall semantic model
  - Inherits from the ModelDefaults class from `model.py`
  - Draws on both Semantics and Proposition classes
- The class is responsible for constructing a semantic model from a Z3 model by handling:
  - Z3 solver integration and constraint satisfaction
  - State space construction and management
  - Model evaluation
  - Visualization and printing utilities

#### Class Integration

- The Semantics class provides the foundational semantic definitions for the Proposition and ModelStructure classes
- The Proposition class uses the Semantics class to determine truth values and verifier/falsifier sets
- The ModelStructure class uses both the Semantics and Proposition classes to build and evaluate semantic models

The module is designed to permit extensions of the semantics by:

- Increasing modularity by separating the definition of operators in `operators.py` from the semantics
- Subclassing the Semantics to add new semantic primitives or constraints
- Extending the ModelStructure to support different kinds of semantic models defined from a Z3 model

### `Operators.py`

The `operators.py` module implements the semantics for the logical operators deployed in `examples.py`.
Each operator is a class that inherits from either the base Operator class (for primitive operators) or DefinedOperator class (for operators defined in terms of primitives) from the syntactic module.
The operators are organized into the following categories:

1. **Extensional Operators**

   - Basic truth-functional operators from classical logic
   - Includes primitives like negation (¬), conjunction (∧), and disjunction (∨)
   - Defined operators include material implication (→) and biconditional (←→)
   - The semantics for these operators is developed in Fine (2017)

2. **Extremal Operators**

   - Represent logical constants: top (⊤) for tautology and bottom (⊥) for contradiction
   - These operators have fixed truth values regardless of context
   - As the semantics is bilateral, the extremal operators are not interdefinable with negation.
   - The semantics for these operators differs from that given in Fine (2017)

3. **Constitutive Operators**

   - Express relationships between propositional content
   - Identity (≡): exact content identity between propositions
   - Ground (≤): one proposition grounds or entails another
   - Essence (⊑): one proposition is essential to another
   - Relevance (≼): one proposition is relevant to another
   - The semantics for these operators is defended in Brast-McKie (2021)

4. **Counterfactual Operators**

   - Handle counterfactual reasoning about alternative possibilities
   - Includes both primitive operators:
     - Counterfactual conditional (□→): "if A were the case, B would be the case"
     - Imposition operator (\\imposition): Kit Fine's semantics for counterfactuals
   - And defined operators:
     - Might counterfactual (◇→): "if A were the case, B might be the case"
     - Might imposition (\\could): possibility under imposition
   - The semantics for these operators is developed and compared to Fine's semantics in Brast-McKie (2025)

5. **Intensional Operators**
   - Handle modal reasoning about necessity and possibility
   - Necessity (□) is primitive: "it is necessarily the case that"
   - Possibility (◇) is defined as ¬□¬: "it is possibly the case that"
   - Counterfactual necessity (\\CFBox) is defined as ⊤ □→: "if anything were the case, it would be the case that"
   - Counterfactual possibility (\\CFDiamond) is defined as ⊤ ◇→: "if anything were the case, it might be the case that"

Each operator class implements four key methods that define its semantic behavior:

- `true_at/false_at`: Define when the operator is true/false at an evaluation point
- `extended_verify/extended_falsify`: Define which states verify/falsify complex formulas
- `find_verifiers_and_falsifiers`: Compute the verifier and falsifier sets
- `print_method`: Handle pretty printing of formulas with truth values

The module integrates with other components:

- Uses the Semantics class from `semantic.py` for core semantic operations
- Inherits from base classes in `syntactic.py` for operator structure
- Interfaces with Z3 through bit vector operations for constraint solving
- Works with ModelStructure for model evaluation and printing

The operators are collected in the `default_operators` collection, which is used by the model checker to recognize and interpret formulas in the input language.

### `Examples.py`

The `examples.py` module contains a comprehensive collection of logical inferences organized into countermodels and theorems.
The module provides:

- Testing of logical properties
- Comparison between semantic theories
- Flexible unit test specification

#### Accessing Examples

You can access examples from this theory using the `get_examples` function from the parent module:

```python
from model_checker.theory_lib import get_examples

# Get all examples from the default theory
examples = get_examples('default')

# Access a specific example
example = examples['CF_CM_1']
premises, conclusions, settings = example
```

For test examples or semantic theories:

```python
from model_checker.theory_lib import get_test_examples, get_semantic_theories

# Get test examples for automated testing
test_examples = get_test_examples('default')

# Get semantic theory implementations
theories = get_semantic_theories('default')
```

#### Example Structure

Each example is structured as a list containing premises, conclusions, and settings:

```python
example = [premises, conclusions, settings]
```

Each example includes configurable settings:

- `N`: Number of atomic states
- `contingent`: Use contingent valuations
- `disjoint`: Enforce disjoint valuations
- `non_empty`: Enforce non-empty valuations
- `max_time`: Maximum computation time
- `iterate`: Number of iterations
- `expectation`: Expected result (True for countermodel found)

The examples currently included in `examples.py` are organized into four main categories:

1. **Counterfactual Countermodels (CF*CM*\*)**

   - Tests invalid counterfactual arguments including:
     - Antecedent strengthening: `A □→ C` ⊭ `(A ∧ B) □→ C`
     - Transitivity: `A □→ B, B □→ C` ⊭ `A □→ C`
     - Sobel sequences demonstrating context sensitivity

2. **Counterfactual Theorems (CF*TH*\*)**

   - Tests valid counterfactual arguments including:
     - Identity: `A □→ A`
     - Modus ponens: `A, A □→ B` ⊨ `B`
     - Modal interactions: `□A` ⊨ `⊤ □→ A`

3. **Constitutive Logic Countermodels (CL*CM*\*)**

   - Tests invalid constitutive arguments involving:
     - Ground operator (≤): Content-based entailment
     - Essence operator (⊑): Content-based necessity
     - Identity operator (≡): Content equivalence

4. **Constitutive Logic Theorems (CL*TH*\*)**
   - Tests valid constitutive arguments including:
     - Ground to essence: `A ≤ B` ⊨ `¬A ⊑ ¬B`
     - Identity properties: `A ≡ B` ⊨ `¬A ≡ ¬B`

The module defines three key data structures:

1. **semantic_theories**: Maps theory names to their implementations

```python
semantic_theories = {
    "Brast-McKie": default_theory,
    # Additional theories can be added
}
```

Each theory specifies:

- Core semantic class
- Proposition handling
- Model structure
- Operator definitions
- Optional notation dictionary

2. **example_range**: Defines examples for the model checker

```python
example_range = {
    "CF_CM_1": CF_CM_1_example,
    "CF_TH_1": CF_TH_1_example,
    # Additional examples...
}
```

3. **test_example_range**: Specifies examples for automated testing

```python
test_example_range = {
    "CF_CM_1": CF_CM_1_example,
    "CF_CM_2": CF_CM_2_example,
    # Additional test examples...
}
```

All examples use operators defined in `operators.py` and rely on the semantic foundations provided by `semantic.py`.

### `__init__.py`

The `__init__.py` module serves as the entry point and public API for the hyperintensional semantics package, organizing and exposing the core components in a clean, intuitive way.
It brings together the following key elements:

1. **Core Classes**

   - Exposes the three fundamental classes from `semantic.py`:
     - `Semantics`: The semantic framework and evaluation rules
     - `Proposition`: Representation and evaluation of logical formulas
     - `ModelStructure`: Management of state spaces and accessibility relations
   - These classes work together to provide the complete semantic machinery

2. **Operator Collection**

   - Exposes `default_operators` from `operators.py`
   - This is a comprehensive dictionary of logical operators including:
     - Extensional operators (¬, ∧, ∨, →, ←→)
     - Modal operators (□, ◇)
     - Counterfactual operators (□→, ◇→)
     - Constitutive operators (≡, ≤, ⊑, ≼)
   - Each operator is properly configured with its semantic interpretation

3. **Integration Layer**

   - Carefully manages imports to avoid circular dependencies
   - Provides a clean public API through `__all__`
   - Includes version information via `__version__`
   - Comments indicate potential extensions (e.g., example integration)

4. **Usage Pattern**
   - Demonstrates the typical workflow:
     1. Import needed components
     2. Create semantic framework
     3. Build model structure
     4. Construct and evaluate propositions
   - Makes it easy to get started with basic model checking

## Basic Usage

> TO BE CONTINUED...

## Unit Testing

> TO BE CONTINUED...

Run `pytest` from the project directory to quickly evaluate whether the examples included in `examples.py` return the expected result.

## Programmatic Semantics

> TO BE CONTINUED...
