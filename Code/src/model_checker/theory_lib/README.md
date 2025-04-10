# ModelChecker Theory Library

## Overview

The ModelChecker Theory Library is a collection of formal semantic theories implemented using Z3 constraint solving for logical reasoning. Each theory provides a programmatic implementation of a different semantic framework, enabling automated verification of logical arguments and discovery of countermodels.

The library follows a modular architecture that allows:
- Comparison between different semantic theories
- Extension with new theories
- Reuse of common components
- Standardized testing and evaluation

## Available Theories

The library currently includes the following theories:

### Default Theory (Hyperintensional Semantics)
- **Primary Author**: Ben Brast-McKie
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
- **Description**: Implements exclusion semantics for counterfactuals and related operators.
- **Key Paper**: Bernard & Champollion "Exclusion Counterfactuals" 
- **Key Features**:
  - Unilateral operators (conjunction, disjunction)
  - Exclusion operator
  - Alternative approach to counterfactual semantics

### Imposition Theory
- **Primary Author**: Kit Fine
- **Description**: Implements Fine's truthmaker semantics for counterfactuals.
- **Key Papers**:
  - Fine (2012) "Counterfactuals without Possible Worlds", Journal of Philosophy
  - Fine (2012) "A Theory of Truth-Conditional Content", Synthese
- **Key Features**:
  - Imposition operator for counterfactuals
  - Could operator for possibility
  - Distinctive approach to counterfactual reasoning

### Bimodal Theory
- **Description**: Extends default theory with temporal modal operators.
- **Key Features**:
  - Both counterfactual and temporal modalities
  - Interaction between different modal operators
  - Extended framework for reasoning about time and possibility

## Theory Architecture

Each theory in the library follows a standardized architecture consisting of:

### Core Components

1. **Semantics** (`semantic.py`)
   - Defines the semantic framework and model structure
   - Implements core semantic relations and operations
   - Specifies Z3 constraints that define the theory

2. **Operators** (`operators.py`)
   - Implements logical operators and their semantics
   - Defines primitive operators with verification/falsification conditions
   - Provides derived operators based on primitives

3. **Examples** (`examples.py`)
   - Contains test cases to verify theory behavior
   - Includes both valid theorems and countermodels
   - Provides configuration settings for model checking

4. **API** (`__init__.py`)
   - Exports the theory's public interface
   - Manages dependencies between components
   - Provides a clean entry point for users

### Standard Files

Each theory directory contains:

- `README.md`: Documentation specific to the theory
- `__init__.py`: Public API and dependency management
- `semantic.py`: Core semantic framework implementation
- `operators.py`: Operator definitions and semantics
- `examples.py`: Test cases and examples
- `test/`: Unit tests for the theory (when available)
- `notebooks/`: Jupyter notebook demonstrations and examples (when available)

## Using Theories

### Basic Import Pattern

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

3. Register your theory in `theory_lib/__init__.py`

### Minimal Theory Template

```python
# semantic.py
from model_checker.model import SemanticDefaults, PropositionDefaults, ModelDefaults

class MySemantics(SemanticDefaults):
    """Core semantics for my theory."""
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
