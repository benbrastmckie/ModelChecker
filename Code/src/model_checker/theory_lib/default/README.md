# Model-Checker: Hyperintensional Semantics

The hyperintensional semantics implements the semantic theories defended in the following papers:

- Brast-McKie ["Identity and Aboutness"](https://link.springer.com/article/10.1007/s10992-021-09612-w) (2021)
- Brast-McKie ["Counterfactual Worlds"](https://github.com/benbrastmckie/ModelChecker/blob/master/Counterfactuals.pdf) (2025)

This work builds on the truthmaker semantics developed by Kit Fine in the following papers:

- Fine ["Counterfactuals without Possible Worlds"](https://link.springer.com/article/10.1007/BF00248737) (2012)
- Fine ["A Theory of Truthmaker Content I: Conjunction, Disjunction and Negation"](https://link.springer.com/article/10.1007/s10992-016-9413-y) (2017)

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

### `Semantic.py`

The `semantic.py` module implements the core semantic framework for the model checker, consisting of three main classes that work together:

1. **Semantics Class**

- This is the foundation that implements the hyperintensional semantic theory
- Defines primitive semantic relations like:
  - Verification/falsification of atomic propositions
  - Compatibility between states
  - Fusion operations for combining states
  - Alternative world calculations for counterfactuals
- Provides the semantic interpretation for all logical operators
- Draws on the ModelDefaults class from model.py for basic model structure
- Interfaces with Z3 solver through bit vector operations

2. **Proposition Class**

- Represents the semantic content of sentences in the logic
- Links syntactic expressions to their semantic interpretation
- Manages:
  - Verifier sets (states that make a proposition true)
  - Falsifier sets (states that make a proposition false)
  - Truth value evaluation at possible worlds
  - Pretty printing of propositions with truth values
- Uses the Semantics class for core semantic operations
- Inherits from PropositionDefaults in model.py

3. **ModelStructure Class**

- Constructs and manages the overall semantic model
- Handles:
  - Z3 solver integration and constraint satisfaction
  - State space construction and management
  - Model evaluation and verification
  - Visualization and printing utilities
- Builds on ModelDefaults from model.py
- Uses both Semantics and Proposition classes

The key relationships between these components:

- The Semantics class provides the foundational semantic operations that both Proposition and ModelStructure use
- Proposition uses Semantics to determine truth values and verifier/falsifier sets
- ModelStructure uses both Semantics and Proposition to build and evaluate complete models
- All three classes interface with the Z3 solver through bit vector operations

This module is central to the model checker as it provides the semantic foundation that everything else builds upon. It implements the theoretical framework while providing practical model construction and evaluation capabilities.

The design allows for extending the semantics by:

- Subclassing Semantics to add new semantic relations
- Adding new operators in operators.py that use the semantic primitives
- Extending ModelStructure to support different kinds of models

### `Operators.py`

The `operators.py` module implements the semantics for the logical operators needed to express the examples in `examples.py`.
Each operator is a class that inherits from either the base Operator class (for primitive operators) or DefinedOperator class (for operators defined in terms of primitives) from the syntactic module.
The operators are organized into the following categories:

1. **Extensional Operators**
   - Basic truth-functional operators from classical logic
   - Includes primitives like negation (¬), conjunction (∧), and disjunction (∨)
   - Defined operators include material implication (→) and biconditional (↔)
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
   - The semantics for these operators is defended in Brast-McKie (2021)

4. **Relevance Operators**
   - Express content relevance between propositions
   - The relevance operator (≼) captures when one proposition is relevant to another
   - Implements a weaker notion than grounding or essence
   - The semantics for this operator is also defended in Brast-McKie (2021)

5. **Counterfactual Operators**
   - Handle counterfactual reasoning about alternative possibilities
   - Includes both primitive operators:
     - Counterfactual conditional (□→): "if A were the case, B would be the case"
     - Imposition operator (\\imposition): Kit Fine's semantics for counterfactuals
   - And defined operators:
     - Might counterfactual (◇→): "if A were the case, B might be the case"
     - Might imposition (\\could): possibility under imposition
   - The semantics for these operators is developed and compared in Brast-McKie (2025)

6. **Intensional Operators**
   - Handle modal reasoning about necessity and possibility
   - Necessity (□) is primitive: "it is necessarily the case that"
   - Possibility (◇) is defined as ¬□¬: "it is possibly the case that"

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

The `examples.py` module provides a comprehensive test suite for the hyperintensional semantics, organized into several categories:

1. **Counterfactual Countermodels (CF_CM_*)**: Tests invalid counterfactual arguments like:
   - Antecedent strengthening: `A □→ C` does not imply `(A ∧ B) □→ C`
   - Transitivity: `A □→ B, B □→ C` does not imply `A □→ C`
   - Complex sequences like Sobel sequences showing context sensitivity

2. **Constitutive Logic Countermodels (CL_CM_*)**: Tests invalid constitutive arguments involving:
   - Ground operator (≤): Content-based entailment
   - Essence operator (⊑): Content-based necessity
   - Identity operator (≡): Content equivalence

3. **Counterfactual Theorems (CF_TH_*)**: Tests valid counterfactual arguments like:
   - Identity: `A □→ A` is valid
   - Modus ponens: `A, A □→ B` implies `B`
   - Modal interactions: `□A` implies `⊤ □→ A`

4. **Constitutive Logic Theorems (CL_TH_*)**: Tests valid constitutive arguments like:
   - Ground to essence: `A ≤ B` implies `¬A ⊑ ¬B`
   - Identity properties: `A ≡ B` implies `¬A ≡ ¬B`

Each example is structured as:

```
example = [premises, conclusions, settings]
```

The `settings` control parameters like:

- `N`: Number of atomic states
- `contingent`: Whether to use contingent valuations
- `disjoint`: Whether to enforce disjoint valuations
- `max_time`: Maximum computation time
- `expectation`: Expected result (True for countermodel found)

The examples draw on operators defined in `operators.py` described above.
Accordingly, examples are limited to the expressive resources provided by `operators.py` given the foundations provided by `semantic.py`.

### `__init__.py`

The `__init__.py` module serves as the entry point and public API for the hyperintensional semantics package, organizing and exposing the core components in a clean, intuitive way. It brings together the following key elements:

1. **Core Classes**
   - Exposes the three fundamental classes from `semantic.py`:
     - `Semantics`: The semantic framework and evaluation rules
     - `Proposition`: Representation and evaluation of logical formulas
     - `ModelStructure`: Management of state spaces and accessibility relations
   - These classes work together to provide the complete semantic machinery

2. **Operator Collection**
   - Exposes `default_operators` from `operators.py`
   - This is a comprehensive dictionary of logical operators including:
     - Extensional operators (¬, ∧, ∨, →, ↔)
     - Modal operators (□, ◇)
     - Counterfactual operators (□→, ◇→)
     - Constitutive operators (≡, ≤, ⊑)
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
