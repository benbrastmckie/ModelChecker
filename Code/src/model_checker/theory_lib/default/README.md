# Model-Checker: Hyperintensional Semantics

The hyperintensional semantics implements the semantic theories defended in the following papers:

- Brast-McKie (2021) ["Identity and Aboutness"](https://link.springer.com/article/10.1007/s10992-021-09612-w), Journal of Philosophical Logic
- Brast-McKie (2025) ["Counterfactual Worlds"](https://link.springer.com/article/10.1007/s10992-025-09793-8), Journal of Philosophical Logic

This work builds on the truthmaker semantics developed by Kit Fine in the following papers:

- Fine (2017) ["Counterfactuals without Possible Worlds"](https://link.springer.com/article/10.1007/BF00248737), Journal of Philosophy
- Fine (2017) ["A Theory of Truthmaker Content I: Conjunction, Disjunction and Negation"](https://link.springer.com/article/10.1007/s10992-016-9413-y), Journal of Philosophical Logic
- Fine (2017) ["A Theory of Truthmaker Content II: Subject-Matter, Common Content, Remainder and Ground"](https://doi.org/10.1007/s10992-016-9419-5) Journal of Philosophical Logic
- Fine (2017) ["Truthmaker Semantics"](https://doi.org/10.1002/9781118972090.ch22), Wiley-Blackwell

I have implemented Fine's semantics for the counterfactual conditional alongside the present theory in the `imposition` theory for comparison.
You can create an imposition project with `model-checker -l imposition`.

## Table of Contents

- [Basic Usage](#basic-usage)
  - [Settings](#settings)
  - [Example Structure](#example-structure)
  - [Running Examples](#running-examples)
    - [1. From the Command Line](#1-from-the-command-line)
    - [2. In VSCodium/VSCode](#2-in-vscodiumvscode)
    - [3. In Development Mode](#3-in-development-mode)
    - [4. Using the API](#4-using-the-api)
  - [Finding Multiple Models](#finding-multiple-models)
- [Model Iteration](#model-iteration)
  - [Iteration Architecture](#iteration-architecture)
  - [Using Model Iteration](#using-model-iteration)
  - [Visual Differences](#visual-differences)
  - [Performance Considerations](#performance-considerations)
- [Unit Testing](#unit-testing)
  - [Running Tests](#running-tests)
  - [Test Examples](#test-examples)
- [Package Contents](#package-contents)
  - [Directory Structure](#directory-structure)
  - [Core Modules](#core-modules)
    - [Semantic.py](#semanticpy)
    - [Operators.py](#operatorspy)
    - [Examples.py](#examplespy)
    - [Iterate.py](#iteratepy)
    - [Init Module](#init-module)
  - [Operator Categories](#operator-categories)
  - [Class Relationships](#class-relationships)

## Basic Usage

### Settings

The default theory defines two types of settings:

#### General Settings

General settings control output and debugging behavior:

```python
general_settings = {
    "print_constraints": False,  # Print constraints when no model is found
    "print_impossible": False,   # Print impossible states
    "print_z3": False,           # Print raw Z3 model
    "save_output": False,        # Prompt to save output
    "maximize": False,           # Maximize common components across models
}
```

#### Example Settings

Example settings control the specific behavior of model checking:

| Setting | Type | Default | Description |
|---------|------|---------|-------------|
| `N` | int | 3 | Number of atomic states (determines state space size) |
| `contingent` | bool | False | Whether sentence letters are assigned to contingent propositions |
| `disjoint` | bool | False | Whether sentence letters must have disjoint subject matters |
| `non_empty` | bool | False | Whether proposition must have non-empty verifier/falsifier sets |
| `non_null` | bool | False | Whether null state can be a verifier/falsifier |
| `max_time` | int | 1 | Maximum Z3 solver time in seconds |
| `iterate` | int | 1 | Number of distinct models to find |
| `iteration_timeout` | float | 1.0 | Maximum time per iteration when searching for multiple models |
| `iteration_attempts` | int | 5 | Number of attempts for finding non-isomorphic models |
| `expectation` | bool | None | Expected model finding result (for testing) |

The default theory explicitly omits settings that aren't applicable to it, following the principle that each theory should only define settings relevant to its specific semantics. For example, the default theory doesn't define:

- `M`: Only relevant for theories with a temporal dimension (like bimodal)
- `align_vertically`: Only relevant for theories with time-based visualization (like bimodal)

If you provide command-line flags for settings that don't exist in a theory (like using `-e` for 'non_empty' with the default theory), you'll see a warning that the flag doesn't correspond to any known setting, but the system will continue running normally.

For more information about how the settings system handles theory-specific settings, please see the [Settings Documentation](../../settings/README.md).

### Example Structure

Examples are structured as a list containing three elements:

```python
[premises, conclusions, settings]
```

Where:
- `premises`: List of formulas that must be true in the model
- `conclusions`: List of formulas to check (invalid if all premises are true and at least one conclusion is false)
- `settings`: Dictionary of settings for this example

Here's a complete example definition:

```python
# Counterfactual Antecedent Strengthening
example = [
    ['\\neg A', '(A \\boxright C)'],           # Premises 
    ['((A \\wedge B) \\boxright C)'],          # Conclusions
    {                                          # Settings
        'N': 4,
        'contingent': True,
        'non_null': True,
        'non_empty': True,
        'max_time': 1,
        'iterate': 1,
    }
]
```

### Running Examples

You can run examples in several ways:

#### 1. From the Command Line

```bash
# Run a specific example module
model-checker path/to/examples/counterfactual.py

# Run the combined examples from __init__.py
model-checker path/to/examples/__init__.py

# Run with constraints printed 
model-checker -p path/to/examples/modal.py

# Run with Z3 output
model-checker -z path/to/examples/constitutive.py
```

#### 2. In VSCodium/VSCode

1. Open any example module (e.g., `examples/counterfactual.py`) in VSCodium/VSCode
2. Use one of these methods:
   - Click the "Run Python File" play button in the top-right corner
   - Right-click in the editor and select "Run Python File in Terminal"
   - Use keyboard shortcut (Shift+Enter) to run selected lines
   
You can also open the combined entry point (`examples/__init__.py`) to run examples from multiple modules.

#### 3. In Development Mode

For development purposes, you can use the `dev_cli.py` script from the project root directory:

```bash
# Run a specific example module
./dev_cli.py path/to/examples/counterfactual.py

# Run the combined examples from __init__.py
./dev_cli.py path/to/examples/__init__.py

# Run with constraints printed 
./dev_cli.py -p path/to/examples/modal.py

# Run with Z3 output
./dev_cli.py -z path/to/examples/constitutive.py
```

#### 4. Using the API

The default theory exposes a clean API:

```python
from model_checker.theory_lib.default import (
    Semantics, Proposition, ModelStructure, default_operators
)
from model_checker import ModelConstraints

# Import example collections directly
from model_checker.theory_lib.default.examples import (
    counterfactual_examples,
    modal_examples
)

# Or use the helper function to get all examples
from model_checker.theory_lib import get_examples
examples = get_examples('default')

# Get a specific example
example_data = counterfactual_examples['CF_CM_1']
premises, conclusions, settings = example_data

# Create semantic structure
semantics = Semantics(settings)
model_constraints = ModelConstraints(semantics, default_operators)
model = ModelStructure(model_constraints, settings)

# Check a formula
prop = Proposition("A \\wedge B", model)
is_true = prop.truth_value_at(model.main_world)
```

## Model Iteration

The default theory provides a sophisticated model iteration framework through the `DefaultModelIterator` class defined in `iterate.py`. This functionality allows you to find multiple distinct models for a given set of constraints.

### Iteration Architecture

The model iteration system is built on four key concepts:

1. **Model Difference Detection**: Identifies meaningful differences between models in terms of:
   - World state changes (added or removed worlds)
   - Possible state changes (new states becoming possible/impossible)
   - Changes in verification and falsification of sentence letters
   - Changes in part-whole relationships between states

2. **Difference Constraints**: Creates Z3 constraints that force the next model to differ from previous ones by requiring at least one change in:
   - Verification or falsification of atomic propositions
   - Part-whole relationships between states
   - Possible state or world status

3. **Non-Isomorphism Constraints**: Forces structural differences in models by:
   - Changing the number of worlds
   - Modifying verification/falsification patterns
   - Altering part-whole relationship structure

4. **Escape Strategies**: When the solver repeatedly finds isomorphic models, increasingly aggressive constraints are applied:
   - First attempt: Target significantly different world counts
   - Later attempts: Force extreme property values (minimal/maximal worlds, all/no verifiers)

### Using Model Iteration

Model iteration can be enabled through two methods:

1. **Example Settings**: Add `'iterate': n` to your example settings, where `n` is the maximum number of models to find.

```python
example_settings = {
    'N': 3,
    'max_time': 1,
    'iterate': 5,  # Find up to 5 models
    'iteration_timeout': 1.0  # Timeout per iteration
}
```

2. **Direct API**: Use the `iterate_example()` function:

```python
from model_checker.theory_lib.default.iterate import iterate_example

# Create a BuildExample instance first
models = iterate_example(example, max_iterations=5)
```

### Visual Differences

When running in iteration mode, the system will show differences between consecutive models:

```
=== DIFFERENCES FROM PREVIOUS MODEL ===

World Changes:
  + 110 (world)
  - 011 (world)

Possible State Changes:
  + 100
  - 001

Proposition Changes:
  A:
    Verifiers: + {100}
    Verifiers: - {001}
    Falsifiers: + {010}
    Falsifiers: - {110}

Part-Whole Relationship Changes:
  001,110: no longer part of
  100,111: now part of
```

### Performance Considerations

- Each iteration may take up to the specified `iteration_timeout` value
- Increasing `N` (number of atomic states) significantly increases the search space
- For complex constraints, consider increasing both `max_time` and `iteration_timeout`

## Unit Testing

### Running Tests

The default theory includes comprehensive test cases:

```bash
# Run all default theory tests
pytest src/model_checker/theory_lib/default/tests/

# Run specific test file
pytest src/model_checker/theory_lib/default/tests/test_default.py

# Run a specific test by name
pytest src/model_checker/theory_lib/default/tests/test_default.py -k "CF_CM_1"

# Run with verbose output
pytest -v src/model_checker/theory_lib/default/tests/test_default.py

# Run with real-time output
pytest -v src/model_checker/theory_lib/default/tests/test_default.py --capture=no
```

### Test Examples

The default theory provides a comprehensive suite of test examples covering:

1. **Counterfactual Countermodels** (`CF_CM_*`):
   - Tests for invalid counterfactual arguments
   - Includes antecedent strengthening, transitivity, contraposition examples
   - Complex scenarios like Sobel sequences

2. **Counterfactual Theorems** (`CF_TH_*`):
   - Tests for valid counterfactual arguments
   - Basic properties like identity and modus ponens
   - Modal interactions with necessity

3. **Constitutive Logic Countermodels** (`CL_CM_*`):
   - Tests for invalid constitutive arguments
   - Ground/essence operators and identity relations

4. **Constitutive Logic Theorems** (`CL_TH_*`):
   - Tests for valid constitutive arguments
   - Relationships between ground, essence and identity

These examples are available through the API:

```python
from model_checker.theory_lib import get_test_examples

# Get all test examples
test_examples = get_test_examples('default')

# Access a specific test example
example = test_examples['CF_CM_1']
```

## Package Contents

### Directory Structure

The default theory package has the following structure:

```
default/
├── __init__.py           # Public API and imports
├── examples/             # Example definitions organized by category
│   ├── __init__.py       # Main entry point for examples with consolidated collections
│   ├── README.md         # Examples documentation
│   ├── counterfactual.py # Counterfactual-specific examples (independently runnable)
│   ├── constitutive.py   # Constitutive-specific examples (independently runnable)
│   ├── modal.py          # Modal-specific examples (independently runnable)
│   ├── extensional.py    # Extensional-specific examples (independently runnable)
│   └── relevance.py      # Relevance-specific examples (independently runnable)
├── iterate.py            # Iteration functionality for finding multiple models
├── operators.py          # Logical operator definitions
├── README.md             # Documentation (this file)
├── semantic.py           # Core semantic classes
├── notebooks/            # Jupyter notebook examples
│   ├── README.md         # Notebook documentation
│   ├── constitutive.ipynb  # Interactive constitutive logic demos
│   ├── counterfactual.ipynb # Interactive counterfactual logic demos
│   ├── extensional.ipynb   # Interactive extensional logic demos
│   ├── modal.ipynb        # Interactive modal logic demos
│   └── relevance.ipynb    # Interactive relevance logic demos
└── tests/                # Test suite
    ├── __init__.py       # Test package initialization
    ├── test_default.py   # Main theory tests
    └── test_iterate.py   # Iteration-specific tests
```

### Core Modules

#### Semantic.py

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

#### Operators.py

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

#### Examples Package

The `examples/` package contains a comprehensive collection of logical inferences organized into separate modules by operator type:

- `counterfactual.py`: Examples for counterfactual operators (would/might conditionals)
- `constitutive.py`: Examples for constitutive operators (ground, essence, identity)
- `modal.py`: Examples for modal operators (necessity, possibility)
- `extensional.py`: Examples for extensional operators (conjunction, disjunction, etc.)
- `relevance.py`: Examples for relevance operators (content relevance)

See the [Examples README](examples/README.md) for detailed documentation on each module.

The main entry point is `examples/__init__.py`, which provides:
- Consolidated collections of examples from all modules
- Testing of logical properties across theories
- Comparison between semantic theories
- Flexible unit test specification

##### Example Structure

Each example is structured as a list containing premises, conclusions, and settings:

```python
example = [premises, conclusions, settings]
```

The package defines several key collections:

1. **Example Collections by Category**:
   - `counterfactual_examples`: All counterfactual examples
   - `modal_examples`: All modal examples
   - `constitutive_examples`: All constitutive examples
   - `extensional_examples`: All extensional examples
   - `relevance_examples`: All relevance examples

2. **Example Collections by Type**:
   - `counterfactual_cm_examples`: Counterfactual countermodels
   - `counterfactual_th_examples`: Counterfactual theorems
   - Similar collections for other categories

3. **Consolidated Collections for Testing**:
   - `test_example_range`: All examples combined for unit testing
   - `example_range`: Selected examples for direct execution

This modular organization provides several benefits:
- Independent execution of individual example modules
- Better separation of concerns
- Easier navigation of similar examples
- More maintainable codebase 
- Ability to extend with new example categories without modifying existing code

#### Jupyter Notebooks

The `notebooks/` directory contains interactive Jupyter notebooks for exploring the default theory:

- `constitutive.ipynb`: Interactive demonstration of ground, essence, and identity operators
- `counterfactual.ipynb`: Examples of counterfactual reasoning patterns and countermodels
- `extensional.ipynb`: Classical logic with focus on conjunction, disjunction, and material implication
- `modal.ipynb`: Exploration of necessity and possibility operators with modal axioms
- `relevance.ipynb`: Content-sensitive relevance logic demonstrations

Each notebook provides:
- Visual model structure exploration with color-coded states
- Step-by-step evaluation of premises and conclusions
- Verification and falsification patterns for each formula
- Direct correspondence with examples in the `examples/` package

Notebooks offer an excellent starting point for users to:
- Understand why certain arguments are valid or invalid
- Visualize the semantic structure underlying logical operators
- Explore the relationships between different logical systems

See the [Notebooks README](notebooks/README.md) for comprehensive documentation on usage and output formats.

#### Iterate.py

Implements model iteration functionality:

```python
class DefaultModelIterator(BaseModelIterator):
    """Model iterator for the default theory."""
    
    def _calculate_differences(self, new_structure, previous_structure):
        """Calculate differences between models."""
        pass
        
    def _create_difference_constraint(self, previous_models):
        """Create constraints to force different models."""
        pass
        
    def _create_non_isomorphic_constraint(self, z3_model):
        """Create constraints for structural differences."""
        pass
        
    def _create_stronger_constraint(self, isomorphic_model):
        """Create stronger constraints to escape isomorphic models."""
        pass

def iterate_example(example, max_iterations=None):
    """Find multiple models for a default theory example."""
    iterator = DefaultModelIterator(example)
    if max_iterations is not None:
        iterator.max_iterations = max_iterations
    return iterator.iterate()
```

#### Init Module

Exposes the public API:

```python
from .semantic import Semantics, Proposition, ModelStructure
from .operators import default_operators
from .iterate import DefaultModelIterator, iterate_example

__all__ = [
    "Semantics",             # Core semantic framework
    "Proposition",           # Proposition representation
    "ModelStructure",        # Model structure management
    "default_operators",     # Logical operators
    "DefaultModelIterator",  # Model iteration
    "iterate_example",       # Helper function for iteration
]
```

### Operator Categories

The default theory implements operators in five categories:

1. **Extensional Operators**
   - Basic truth-functional operators from classical logic
   - Includes primitives like negation (¬), conjunction (∧), disjunction (∨)
   - Defined operators like material implication (→) and biconditional (↔)

2. **Extremal Operators**
   - Logical constants: top (⊤) for tautology and bottom (⊥) for contradiction
   - Fixed truth values regardless of context
   - Not interdefinable with negation in bilateral semantics

3. **Constitutive Operators**
   - Express relationships between propositional content
   - Identity (≡): exact content identity between propositions
   - Ground (≤): content-based entailment relation
   - Essence (⊑): content-based necessity relation
   - Relevance (≼): content-based relevance relation

4. **Counterfactual Operators**
   - Handle counterfactual reasoning about alternative possibilities
   - Counterfactual conditional (□→): "if A were the case, B would be the case"
   - Might counterfactual (◇→): "if A were the case, B might be the case"

5. **Modal Operators**
   - Handle necessity and possibility
   - Necessity (□): "it is necessarily the case that"
   - Possibility (◇): "it is possibly the case that"

### Class Relationships

The default theory architecture follows a clear separation of concerns:

- `Semantics` provides the core semantic framework
- `Proposition` uses the `Semantics` to evaluate and represent formulas
- `ModelStructure` manages the overall model built from `Semantics` and `Proposition`
- `DefaultModelIterator` extends the model finding to multiple distinct models
- `Operators` define how complex formulas should be evaluated

This modular design allows for extension and specialization of each component independently.
