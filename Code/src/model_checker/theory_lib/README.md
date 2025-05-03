# ModelChecker Theory Library

## Overview

The ModelChecker Theory Library is a collection of semantic theories implemented using Z3. Each theory provides a programmatic implementation of a different semantic framework, enabling automated verification of logical arguments and discovery of countermodels.

The library follows a modular architecture that allows:

- Comparison between different semantic theories
- Extension with new theories
- Reuse of common components
- Standardized testing and evaluation

## Available Theories

The library currently includes the following theories:

### Default Theory (Hyperintensional Semantics)

- **Theory Author**: Brast-McKie
- **Implementation Authors**: Brast-McKie and Buitrago
- **Description**: Implements a hyperintensional semantics for counterfactuals, constitutive operators, and modal logic.
- **Key Papers**:
  - Brast-McKie (2021) "Identity and Aboutness", Journal of Philosophical Logic
  - Brast-McKie (2025) "Counterfactual Worlds", Journal of Philosophical Logic
- **Key Features**:
  - State-based hyperintensional propositions with verifiers and falsifiers
  - Truthmaker semantics for extensional connectives
  - Counterfactual conditionals via alternatives
  - Constitutive operators for essence, ground, and identity

### Exclusion Theory

- **Primary Authors**: Lucas Champollion & Paul Bernard
- **Implementation Authors**: Brast-McKie and Buitrago
- **Description**: Implements exclusion semantics for counterfactuals and related operators.
- **Key Paper**: Bernard & Champollion "Exclusion Counterfactuals"
- **Key Features**:
  - Unilateral operators (conjunction, disjunction)
  - Exclusion operator
  - Alternative approach to counterfactual semantics

### Imposition Theory

- **Primary Author**: Kit Fine
- **Description**: Implements Fine's truthmaker semantics for counterfactuals.
- **Implementation Author**: Brast-McKie
- **Key Papers**:
  - Fine (2012) "Counterfactuals without Possible Worlds", Journal of Philosophy
  - Fine (2012) "A Theory of Truth-Conditional Content", Synthese
- **Key Features**:
  - Imposition operator for counterfactuals
  - Could operator for possibility
  - Distinctive approach to counterfactual reasoning

### Bimodal Theory

- **Theory Author**: Brast-McKie
- **Implementation Author**: Brast-McKie
- **Description**: Extends default theory with temporal modal operators.
- **Key Features**:
  - Both counterfactual and temporal modalities
  - Interaction between different modal operators
  - Extended framework for reasoning about time and possibility

## Theory Architecture

Each theory in the library follows a standardized architecture consisting of:

- `README.md`: Documentation specific to the theory
- `__init__.py`: Public API and dependency management
- `semantic.py`: Core semantic framework implementation
- `operators.py`: Operator definitions and semantics
- `examples.py`: Test cases and examples
- `test/`: Unit tests for the theory (when available)
- `notebooks/`: Jupyter notebook demonstrations and examples (when available)

### The `semantic.py` Module

This module implements the core semantic framework for the theory and typically consists of three primary classes:

#### 1. Semantics Class

The Semantics class (e.g., `Semantics`, `BimodalSemantics`, etc.) provides the foundation of the semantic theory and defines:

- **Z3 Semantic Primitives**:
  - **Z3 Sorts**: Define basic types used in the theory (e.g., states, worlds, times)
  - **Z3 Functions**: Declare primitive relations and functions (e.g., `verify`, `falsify`, `possible`)
  - **Z3 Constants**: Define reference points for evaluation (e.g., `main_world`)

- **Semantic Relations and Operations**:
  - **State Relations**: Define relations between states (e.g., `is_part_of`, `compatible`, `fusion`)
  - **World Identification**: Methods to identify worlds within the model (e.g., `is_world`, `maximal`)
  - **Relation Definitions**: Define theory-specific relations (e.g., `is_alternative`, `accessibility`)

- **Evaluation Context Management**:
  - **Main Evaluation Point**: The primary context for evaluation (e.g., `main_point`)
  - **Frame Constraints**: Constraints that define the logical frame for the theory
  - **Validity Conditions**: Behaviors for premise and conclusion evaluation

- **Truth Evaluation Methods**:
  - **true_at/false_at**: Methods to evaluate truth/falsity of sentences at evaluation points
  - **extended_verify/extended_falsify**: Methods to determine verifiers/falsifiers for complex formulas

- **Extraction Methods**: Provides data needed by the Structure class
  - **Primitive Elements**: Methods to extract primitive elements from the model (states, verifiers, falsifiers)
  - **Defined Elements**: Methods to extract the defined elements from a model (compatibility, worlds, alternatives)

- **Settings Management**:
  - **DEFAULT_EXAMPLE_SETTINGS**: Theory-specific example settings with defaults
  - **DEFAULT_GENERAL_SETTINGS**: Theory-specific general settings for output control

#### 2. Proposition Class

The Proposition class (e.g., `Proposition`, `BimodalProposition`, etc.) represents propositional content in the theory and provides:

- **Proposition Representation**:
  - **Verifiers and Falsifiers**: Sets of states that verify/falsify propositions
  - **Truth Values**: Methods to determine truth values at evaluation points
  - **Proposition Constraints**: Z3 constraints governing what counts as a proposition

- **Constraint Generation**:
  - **Standard Constraints**: Semantic constraints for default behavior (e.g., no truth-value gaps/gluts)
  - **Optional Constraints**: Settings-based constraints (contingency, disjointness, etc.)

- **Model Integration**:
  - **Extraction Methods**: Methods to extract verifiers/falsifiers from models
  - **Evaluation Methods**: Methods to evaluate propositions in models
  - **Visualization Methods**: Methods to display propositional content

- **Equality and Representation**:
  - **Comparison Operations**: Methods to compare propositions
  - **String Representation**: Formatted display of propositional content

#### 3. ModelStructure Class

The ModelStructure class (e.g., `ModelStructure`, `BimodalStructure`) manages the overall semantic model and provides:

- **Model Construction**:
  - **Z3 Model Management**: Integration with Z3 solver and model
  - **Representation Management**: Methods to construct and manage model representation
  - **Constraint Handling**: Methods to process and apply constraints

- **Evaluation Infrastructure**:
  - **Element Identification**: Methods to identify elements in the model
  - **Evaluation Methods**: Methods to evaluate formulas in the model

- **Model Visualization**:
  - **Element Display**: Methods to print a model's elements
  - **Evaluation Display**: Methods to show evaluation results
  - **Difference Tracking**: Methods to track changes between models

- **Model Persistence**:
  - **Serialization**: Methods to save model structures
  - **Diagnostics**: Methods to record model information
  - **Test Generation**: Methods to generate test cases from models

- **Theory-Specific Model Operations**:
  - **Structure Analysis**: Methods to analyze model properties
  - **Relation Calculations**: Methods to compute theory-specific relations
  - **Structural Constraints**: Methods to force structural variations

### The `operators.py` Module

This module defines the logical operators used in the theory. It typically includes:

#### 1. Primary Operator Classes

- **Basic Operators**: Implementations of primitive logical operators (e.g., conjunction, disjunction, etc.)
  - Inherit from `Operator` class
  - Define names, symbols, and arities
  - Implement semantic clauses for truth/falsity evaluation
  - Provide verification/falsification conditions (if hyperintensional)

- **Derived Operators**: Operators defined in terms of other operators
  - Inherit from `DefinedOperator` class
  - Define equivalence with combinations of primitive operators
  - May override semantic methods for efficiency

- **Special Operators**: Theory-specific operators (e.g., counterfactual, modal operators, etc.)
  - Implement specialized semantic clauses
  - Define unique verification/falsification conditions
  - Provide theory-specific evaluation methods

#### 2. Operator Registry

- **Operator Collection**: Dictionary of all operators in the theory
  - Maps operator symbols to operator instances
  - Serves as the registry for the theory's operators
  - Used by the parser to handle formulas

- **Export Management**: Functions to expose operators to other modules
  - Provides public access to operator instances
  - Manages dependencies between operators

#### 3. Common Operator Implementations

- **Truth-Functional Operators**: Standard logical operators (e.g., negation, conjunction, disjunction, implication)
- **Modal Operators**: Operators for possibility and necessity
- **Theory-Specific Operators**: Specialized operators unique to the theory (e.g., counterfactual, essence, ground)

### The `examples.py` Module

This module contains examples and test cases for the theory and must include specific required definitions as well as optional components:

#### 1. Example Categories

- **Countermodels (Naming Convention: XX_CM_#)**
  - **Modal Logic (ML_CM_#)**: Countermodels for modal principles
  - **Counterfactual Logic (CF_CM_#)**: Countermodels for counterfactual principles
  - **Constitutive Logic (CL_CM_#)**: Countermodels for constitutive principles

- **Theorems (Naming Convention: XX_TH_#)**
  - **Modal Logic (ML_TH_#)**: Theorems of modal logic
  - **Counterfactual Logic (CF_TH_#)**: Theorems of counterfactual logic
  - **Constitutive Logic (CL_TH_#)**: Theorems of constitutive logic

#### 2. Example Definitions

- **Countermodel Example (Invalid Formula)**
  ```python
  # ML_CM_1: BOX NECESSITATION FAILURE
  ML_CM_1_premises = ['A']
  ML_CM_1_conclusions = ['\\Box A']
  ML_CM_1_settings = {
      'N': 3,
      'contingent': True,
      'non_empty': True,
      'disjoint': False,
      'max_time': 1,
      'expectation': True,  # Expect to find a countermodel
  }
  ML_CM_1_example = [
      ML_CM_1_premises,
      ML_CM_1_conclusions,
      ML_CM_1_settings,
  ]
  ```

- **Theorem Example (Valid Formula)**
  ```python
  # CL_TH_2: IDENTITY AND GROUND
  CL_TH_2_premises = []
  CL_TH_2_conclusions = ['((A = B) \\imp (A \\Ground B))']
  CL_TH_2_settings = {
      'N': 3,
      'contingent': False,
      'non_empty': True, 
      'disjoint': False,
      'max_time': 1,
      'expectation': False,  # Expect no countermodel (theorem is valid)
  }
  CL_TH_2_example = [
      CL_TH_2_premises,
      CL_TH_2_conclusions,
      CL_TH_2_settings,
  ]
  ```

#### 3. Example Configuration Options

- **Core Settings (Required)**
  ```python
  "example_settings": {
      "N": 3,               # Number of atomic states (required)
      "max_time": 1,        # Maximum solver time in seconds (required)
      "expectation": True,  # True=expect countermodel, False=expect theorem
  }
  ```

- **Proposition Constraints (Optional)**
  ```python
  "example_settings": {
      "contingent": True,   # Require contingent valuations
      "non_empty": True,    # Require non-empty verifier/falsifier sets
      "non_null": True,     # Prevent null states as verifiers/falsifiers
      "disjoint": False,    # Control overlapping constraints
  }
  ```

- **Theory-Specific Settings (Optional)**
  ```python
  "example_settings": {
      "iterate": 1,         # Number of models to find
  }
  ```

#### 1. Required Module Definitions

- **`semantic_theories` Dictionary**: Contains at least one theory definition
  ```python
  semantic_theories = {
      "Brast-McKie": {
          "semantics": Semantics,
          "proposition": Proposition,
          "model": ModelStructure,
          "operators": default_operators
      }
  }
  ```

- **`example_range` Dictionary**: Specifies which examples to run
  ```python
  example_range = {
      "ML_CM_1": ML_CM_1_example,  # Modal Logic Countermodel 1
      "CL_TH_2": CL_TH_2_example,  # Constitutive Logic Theorem 2
  }
  ```

- **`test_example_range` Dictionary**: Examples for unit testing
  ```python
  test_example_range = {
      "ML_CM_1": ML_CM_1_example,
      "CL_TH_2": CL_TH_2_example,
  }
  ```

- **`general_settings` Dictionary**: Global settings for all examples
  ```python
  general_settings = {
      "print_constraints": False,
      "print_impossible": True,
      "print_z3": False,
      "save_output": False,
  }
  ```

- **`__all__` List**: Exports specific variables for import
  ```python
  __all__ = [
      'general_settings',
      'default_theory',
      'semantic_theories',
      'example_range',
      'test_example_range',
  ]
  ```

#### 5. Using Example Dictionaries

- **For Manual Testing**: Use `example_range` to specify which examples to run
  ```python
  # Uncomment specific examples to include them in the test run
  example_range = {
      "ML_CM_1": ML_CM_1_example,  # Include this countermodel example
      # "CL_TH_2": CL_TH_2_example,  # Exclude this theorem example
  }
  ```

- **For Unit Testing**: Use `test_example_range` to include examples in automated tests
  ```python
  test_example_range = {
      "ML_CM_1": ML_CM_1_example,
      "CL_TH_2": CL_TH_2_example,
  }
  ```

### The `__init__.py` Module

This module provides the public API for the theory and typically includes:

#### 1. Import Management

- **Module Exports**: Exposed classes and functions
  - Public classes (Semantics, Proposition, ModelStructure)
  - Operator collections
  - Utility functions

- **Dependency Management**: Import necessary components
  - Standard library imports
  - Core framework imports
  - Theory-specific imports

#### 2. Theory Registration

- **Theory Information**: Metadata about the theory
  - Theory name
  - Version information
  - Author information

- **API Construction**: Functions to build the theory's API
  - Initialization functions
  - Integration with the broader framework

#### 3. Convenience Functions

- **Shorthand Access**: Simplified access to common operations
  - Formula checking functions
  - Model building functions
  - Example loading functions

## Using Theories

### Import Strategies

Theory projects support two primary import strategies, each with different use cases:

#### 1. Local Module Imports (for Generated Projects)

When you generate a new theory project with `model-checker -l bimodal`, the examples.py file uses local imports:

```python
# Standard imports
import sys
import os

# Add current directory to path before importing modules
current_dir = os.path.dirname(os.path.abspath(__file__))
if current_dir not in sys.path:
    sys.path.insert(0, current_dir)

# Direct imports from local modules
from semantic import BimodalStructure, BimodalSemantics, BimodalProposition
from operators import bimodal_operators
```

**Benefits:**

- Simple, direct imports from files in the same directory
- Projects can be run directly with `model-checker examples.py`
- Changes to the local files are immediately reflected
- Ideal for development and experimentation

**When to use:**

- When you want to modify and experiment with a theory
- When creating a standalone project
- When running the examples.py file directly

#### 2. Package Imports (for Comparison)

To compare your modified theory with the original implementation, you can use package imports:

```python
# Import from the core package
from model_checker.theory_lib.bimodal import (
    BimodalStructure,
    BimodalSemantics,
    BimodalProposition
)
from model_checker.theory_lib.bimodal import bimodal_operators

# Or more generally
from model_checker import get_theory
from model_checker.theory_lib import get_examples

# Load the original theory
theory = get_theory("bimodal")
```

**Benefits:**

- Access to the original implementations for comparison
- Consistency with the package's versioned APIs
- Clear separation between your modifications and the original

**When to use:**

- When comparing your modifications to the original
- When extending the original without modifying it
- When using multiple theories together

### Basic Usage Examples

```python
from model_checker import get_theory
from model_checker.theory_lib import get_examples

# Load a theory
theory = get_theory("default")  # or "exclusion", "imposition", "bimodal"

# Get examples from the theory
examples = get_examples("default")

# Create a model from an example
from model_checker import BuildExample
model = BuildExample("example_name", theory)

# Check a formula
result = model.check_formula("\\Box p -> p")
print(result)
```

### Theory Selection and Configuration

```python
from model_checker import BuildExample

# Load with specific settings
settings = {
    "N": 4,               # Number of atomic states
    "contingent": True,   # Require contingent valuations
    "non_empty": True,    # Require non-empty verifiers/falsifiers
    "disjoint": False,    # Allow overlapping verifiers/falsifiers
    "max_time": 5         # Maximum solving time (seconds)
}

# Build example with theory and settings
model = BuildExample("example_name", get_theory("default"), settings=settings)
```

### Comparing Theories

```python
from model_checker import BuildModule

# Create a module to compare theories
module = BuildModule("comparison")

# Add theories to compare
module.add_theory("default")
module.add_theory("exclusion")

# Run tests across theories
module.run_tests(["test1", "test2"])
```

## Extending with New Theories

To create a new theory:

1. Create a directory under `theory_lib/` (e.g., `theory_lib/my_theory/`)
2. Implement the required files:

   - `semantic.py`: Define your semantic framework
   - `operators.py`: Implement your logical operators
   - `examples.py`: Create test cases
   - `__init__.py`: Export your public API
   - `README.md`: Document your theory

3. Implement theory-specific settings in `semantic.py`
4. Register your theory in `theory_lib/__init__.py`

### Theory-Specific Settings

Each theory in the ModelChecker framework defines its own settings based on the **relevance principle** - only include settings that are relevant to your specific semantic theory. There are two types of settings:

#### Default Example Settings

These settings control the behavior of specific examples:

```python
# In your semantic.py file
class MySemantics(SemanticDefaults):
    DEFAULT_EXAMPLE_SETTINGS = {
        # Core settings included by most theories
        'N': 3,                   # Number of atomic states (required)
        'max_time': 1,            # Maximum solver time (required)
        'contingent': False,      # Whether propositions must be contingent

        # Theory-specific settings (include only what's relevant)
        'my_special_setting': False,  # Setting unique to your theory
    }
```

#### Default General Settings

These settings control global behavior and output format:

```python
# In your semantic.py file
class MySemantics(SemanticDefaults):
    DEFAULT_GENERAL_SETTINGS = {
        # Common output settings
        "print_constraints": False,
        "print_z3": False,
        "save_output": False,

        # Theory-specific settings (only if needed)
        "my_display_setting": True,  # Setting unique to your theory
    }
```

#### Settings Guidelines

1. **Only include settings relevant to your theory**

   - Don't implement settings that don't apply to your semantic framework
   - For example, temporal theories include `M` and `align_vertically`, but others don't

2. **Common settings across theories**

   - `N`: Number of atomic states (required by all theories)
   - `max_time`: Maximum solver time (required by all theories)
   - `contingent`: Whether propositions must be contingent (common but optional)
   - `disjoint`: Whether propositions must have disjoint subject matters (common but optional)

3. **Theory-specific settings examples**
   - `M`: Number of time points (bimodal theory only)
   - `align_vertically`: Display time flowing vertically (bimodal theory only)
   - `non_empty`: Non-empty verifier/falsifier sets (exclusion theory)
   - `fusion_closure`: Enforce fusion closure (exclusion theory)

For detailed information about the settings system and how theory-specific settings are managed, see the [Settings Documentation](../settings/README.md).
You can also find theory specific settings here:

- [Default Theory Settings](theory_lib/default/README.md#default-theory-settings)
- [Bimodal Theory Settings](theory_lib/bimodal/README.md#bimodal-specific-settings)
- [Exclusion Theory Settings](theory_lib/exclusion/README.md#theory-specific-settings)

### Operator Constraints and Syntax Rules

When implementing operators for your theory, adhere to these important constraints:

1. **Reserved Nullary Operators**:

   - `\\top` and `\\bot` are designated nullary operators that cannot be reused as operator names
   - These represent logical truth and falsehood respectively and have special parsing treatment

2. **Well-Formed Formula Rules**:

   - Binary operators must have outer parentheses in well-formed sentences: `(A \\wedge B)`
   - Unary operators do not use parentheses for their main connective: `\\neg A`
   - Nested expressions follow standard parenthesization rules: `\\neg (A \\wedge B)`

3. **LaTeX Notation**:

   - All special symbols should use LaTeX notation: `\\wedge`, `\\vee`, `\\neg`, etc.
   - Operators are designated with a double backslash as in `\\Box` and `\\Future`
   - Custom operators should follow this pattern: `\\myoperator`

4. **Sentence Letters**:

   - Sentence letters are alpha-numeric strings: `A`, `B_2`, `Mary_sings`, etc.
   - Use underscore `_` for spaces in sentence letters (e.g., `Mary_sings`)
   - Sentence letters must not start with a backslash (reserved for operators)

5. **Parsing Considerations**:
   - The parser treats sentences as space-separated tokens
   - Ensure proper spacing in complex formulas: `(A \\wedge (B \\vee C))`
   - Avoid operator names that could conflict with reserved operators

Following these constraints ensures proper parsing and evaluation of logical formulas within the model checker framework.

### Minimal Theory Template

```python
# semantic.py
from model_checker.model import SemanticDefaults, PropositionDefaults, ModelDefaults

class MySemantics(SemanticDefaults):
    """Core semantics for my theory."""

    # Define theory-specific default settings
    DEFAULT_EXAMPLE_SETTINGS = {
        'N': 3,                   # Number of atomic states (required)
        'max_time': 1,            # Maximum solver time (required)
        'contingent': False,      # Common optional setting
        # Add only settings relevant to your theory
    }

    DEFAULT_GENERAL_SETTINGS = {
        "print_constraints": False,
        "print_z3": False,
        "save_output": False,
        # Add only settings relevant to your theory
    }

    # Implement semantic primitives and relations

class MyProposition(PropositionDefaults):
    """Proposition implementation for my theory."""
    # Implement proposition evaluation

class MyModelStructure(ModelDefaults):
    """Model structure for my theory."""
    # Implement model construction and evaluation

# operators.py
from model_checker.syntactic import Operator, DefinedOperator

class MyOperator(Operator):
    """A primitive operator in my theory."""
    def __init__(self):
        super().__init__("my_op", "\\myop", 1)  # name, symbol, arity

    # Implement semantic methods

my_operators = {
    "\\myop": MyOperator(),
    # Add more operators
}

# __init__.py
from .semantic import MySemantics, MyProposition, MyModelStructure
from .operators import my_operators

__all__ = [
    "MySemantics", "MyProposition", "MyModelStructure",
    "my_operators"
]
```

## Advanced Features

### Theory Translation

Theories can provide translation dictionaries to map operators between theories:

```python
# Translation from Theory A to Theory B
translation_dict = {
    "\\opA": "\\opB",
    "\\another_opA": "\\another_opB"
}

# Use in theory definition
theory_a = {
    "semantics": SemanticA,
    "proposition": PropositionA,
    "operators": operators_a,
    "dictionary": translation_dict  # Used when translating to theory B
}
```

### Custom Model Constraints

Theories can define custom constraints on models:

```python
class CustomSemantics(SemanticDefaults):
    def get_constraints(self):
        """Add custom constraints to the model."""
        constraints = super().get_constraints()

        # Add theory-specific constraints
        my_constraint = self.z3.ForAll([self.s1, self.s2],
                          self.z3.Implies(self.custom_relation(self.s1, self.s2),
                                      self.some_condition(self.s1, self.s2)))
        constraints.append(my_constraint)

        return constraints
```

### Jupyter Notebook Integration

Each theory can include Jupyter notebooks for interactive exploration, documentation, and demonstration. These notebooks serve several important purposes:

1. **Theory Documentation**: Explain your theory's semantics with interactive examples
2. **Feature Demonstrations**: Show your theory's operators and key principles in action
3. **Research Exploration**: Provide tools for researchers to experiment with the theory
4. **Teaching Resources**: Create educational materials for students and newcomers
5. **Countermodel Demonstrations**: Show specific examples of interesting countermodels

Notebooks should be placed in a `notebooks/` directory within your theory package, for example:

```
theory_lib/
└── my_theory/
    ├── __init__.py
    ├── semantic.py
    ├── operators.py
    ├── examples.py
    └── notebooks/
        ├── introduction.ipynb   # Basic introduction to the theory
        ├── operators.ipynb      # Examples of operator behavior
        └── countermodels.ipynb  # Interesting countermodel examples
```

#### Theory-Specific Visualizations

Theories can provide custom visualization methods for Jupyter notebook integration:

```python
class CustomModelStructure(ModelDefaults):
    def visualize(self):
        """Custom visualization for this theory."""
        import matplotlib.pyplot as plt
        # Implement theory-specific visualization
        return plt.gcf()
```

These visualization methods will be automatically used by the Jupyter integration when displaying models.

For comprehensive information about Jupyter notebook integration, including implementation details, APIs, and usage examples, see the [Jupyter Integration Documentation](../jupyter/README.md).

## Best Practices

1. **Consistent Naming**: Follow established naming conventions
2. **Documentation**: Include thorough docstrings and README files
3. **Examples**: Provide comprehensive test cases
4. **Unit Tests**: Include tests to verify theory correctness
5. **Modular Design**: Keep semantic components separate from operators
6. **Code Reuse**: Inherit from base classes when possible
7. **Error Handling**: Validate inputs and provide helpful error messages
8. **Performance**: Consider constraint complexity and solving time

## Theory Contribution Guidelines

When contributing a new theory:

1. Ensure your theory follows the standard architecture
2. Include comprehensive documentation
3. Provide test cases that demonstrate key features
4. Add Jupyter notebook examples in a `notebooks/` directory
5. Submit a pull request with a description of your theory

## API Reference

See the [API Documentation](../README.md) for detailed information on the ModelChecker API.
