# Contributing New Theories to ModelChecker

[← Back to Theory Library](../README.md) | [Usage Guide →](USAGE_GUIDE.md) | [Architecture Guide →](THEORY_ARCHITECTURE.md)

## Table of Contents

1. [Why Contribute?](#why-contribute)
2. [Getting Started](#getting-started)
3. [Theory-Specific Settings](#theory-specific-settings)
4. [Operator Implementation](#operator-implementation)
5. [Required Files](#required-files)
6. [Testing Your Theory](#testing-your-theory)
7. [Advanced Features](#advanced-features)
8. [Licensing and Attribution](#licensing-and-attribution)

## Why Contribute?

- **Share your research**: Make your semantic theory accessible to other researchers
- **Enable verification**: Allow others to test logical arguments in your framework
- **Receive feedback**: Get input from the community on your semantic approach
- **Compare theories**: See how your theory handles examples compared to others

New semantic theories can be submitted to the ModelChecker Theory Library by following the guidelines detailed below. For questions or assistance, please open an [issue](https://github.com/benbrastmckie/ModelChecker/issues) on the GitHub repository.

## Getting Started

Follow these steps to develop and contribute a new theory to the ModelChecker project:

### 1. Fork and Clone

```bash
# First, fork the repository on GitHub
# Then clone your fork
git clone https://github.com/YOUR-USERNAME/ModelChecker.git
cd ModelChecker

# Add the original repo as upstream
git remote add upstream https://github.com/benbrastmckie/ModelChecker.git
```

### 2. Create a New Branch

```bash
git checkout -b theory/my-new-theory
```

### 3. Generate a Template Project

Choose the existing `THEORY_NAME` that most closely resembles your intended theory (e.g., logos, bimodal, exclusion, imposition) and use it as a template:

```bash
model-checker -l THEORY_NAME
```

This creates a local project with all necessary files based on the chosen theory. Choose an appropriate `theory_name` for your project.

### 4. Implement Your Theory

Modify the generated files to implement your semantic framework:

- `semantic.py`: Define your semantic classes and relations
- `operators.py`: Implement your logical operators
- `examples.py`: Create test cases specific to your theory
- `__init__.py`: Update exports with your theory's classes
- `README.md`: Document your theory's features and usage

### 5. Test Your Implementation

```bash
# Run your examples
model-checker examples.py

# Run specific tests
model-checker -t my_test_name
```

### 6. Move Your Theory to the Library

Once your theory is working locally, integrate it into the main library:

```bash
# Create a directory for your theory in the library
mkdir -p Code/src/model_checker/theory_lib/my_theory

# Move your project directory to the theory library
mv project_theory_name/* Code/src/model_checker/theory_lib/my_theory/
```

### 7. Register Your Theory

Add your theory to the `__all__` list in `Code/src/model_checker/theory_lib/__init__.py`:

```python
__all__ = [
    "logos",
    "exclusion",
    "imposition",
    "bimodal",
    "my_theory"  # Add your theory here
]
```

### 8. Submit a Pull Request

```bash
# Ensure your fork is up to date with upstream
git fetch upstream
git checkout main
git merge upstream/main

# Switch back to your feature branch and rebase on main
git checkout theory/my-new-theory
git rebase main

# Stage and commit your changes
git add Code/src/model_checker/theory_lib/my_theory
git add Code/src/model_checker/theory_lib/__init__.py
git commit -m "Add MyTheory implementation"

# Push to your fork
git push -u origin theory/my-new-theory
```

Then create a pull request on GitHub with:

- A clear description of your theory
- References to relevant papers or research
- Examples of what makes your theory unique
- Any special requirements or dependencies

## Theory-Specific Settings

Each theory in the ModelChecker framework defines its own settings based on the **relevance principle** - only include settings that are relevant to your specific semantic theory.

### Default Example Settings

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

### Default General Settings

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

### Settings Guidelines

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

For detailed information about the settings system, see the [Settings Documentation](../../settings/README.md).

## Operator Implementation

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

## Required Files

Each theory must include these core files:

### semantic.py

Define your semantic framework with the core classes:

```python
from model_checker.models.semantic import SemanticDefaults
from model_checker.models.proposition import PropositionDefaults
from model_checker.models.structure import ModelDefaults

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
```

### operators.py

Implement your logical operators:

```python
from model_checker.syntactic import Operator, DefinedOperator, OperatorCollection

class MyOperator(Operator):
    """A primitive operator in my theory."""
    def __init__(self):
        super().__init__("my_op", "\\myop", 1)  # name, symbol, arity

    # Implement semantic methods

my_operators = OperatorCollection(
    # primitive extensional operators
    NegationOperator,
    AndOperator,
    OrOperator,

    # new operators
    MyOperator,
    AnotherOperator,
)
```

### **init**.py

Export your public API:

```python
from .semantic import MySemantics, MyProposition, MyModelStructure
from .operators import my_operators

__all__ = [
    "MySemantics", "MyProposition", "MyModelStructure",
    "my_operators"
]
```

### examples.py

Create comprehensive test cases following the standard format:

```python
# Standard imports
import os
import sys

# Add current directory to path for imports
current_dir = os.path.dirname(os.path.abspath(__file__))
if current_dir not in sys.path:
    sys.path.insert(0, current_dir)

# Import theory components
from .semantic import MySemantics, MyProposition, MyModelStructure
from .operators import my_operators

# Theory definition
my_theory = {
    "semantics": MySemantics,
    "proposition": MyProposition,
    "model": MyModelStructure,
    "operators": my_operators,
    "dictionary": {}
}

# MY_CM_1: COUNTERMODEL EXAMPLE DESCRIPTION
MY_CM_1_premises = ["A"]
MY_CM_1_conclusions = ["\\Box A"]
MY_CM_1_settings = {
    'N': 3,
    'contingent': False,
    'non_null': False,
    'non_empty': False,
    'disjoint': False,
    'max_time': 1,
    'iterate': 1,
    'expectation': True,
}
MY_CM_1_example = [
    MY_CM_1_premises,
    MY_CM_1_conclusions,
    MY_CM_1_settings,
]

# MY_TH_1: THEOREM EXAMPLE DESCRIPTION
MY_TH_1_premises = []
MY_TH_1_conclusions = ["(A \\rightarrow A)"]
MY_TH_1_settings = {
    'N': 3,
    'contingent': False,
    'non_null': False,
    'non_empty': False,
    'disjoint': False,
    'max_time': 1,
    'iterate': 1,
    'expectation': False,
}
MY_TH_1_example = [
    MY_TH_1_premises,
    MY_TH_1_conclusions,
    MY_TH_1_settings,
]

# Organize examples by category
countermodel_examples = {
    "MY_CM_1": MY_CM_1_example,
}

theorem_examples = {
    "MY_TH_1": MY_TH_1_example,
}

# Combine for unit_tests (used by test framework)
unit_tests = {**countermodel_examples, **theorem_examples}

# Define which examples to run
example_range = unit_tests

# Define semantic theories
semantic_theories = {
    "MyTheory": my_theory,
}

# Make module executable
if __name__ == '__main__':
    import subprocess
    file_name = os.path.basename(__file__)
    subprocess.run(["model-checker", file_name], check=True, cwd=current_dir)
```

### README.md

Document your theory following the standard structure:

```markdown
# My Theory: [Descriptive Tagline]

[← Back to Theory Library](../README.md) | [Documentation →](docs/README.md)

## Directory Structure

[Include complete file tree]

## Overview

[Theory description, features, theoretical background]

## Quick Start

[Working code examples]

## Subdirectories

[Describe docs/, tests/, notebooks/ directories]

## Documentation

[Organized by user type]

## References

[Academic references and related resources]
```

## Testing Your Theory

### Test Structure

Create comprehensive tests for your theory:

```
my_theory/
└── tests/
    ├── README.md           # Test documentation
    ├── __init__.py
    ├── test_semantic.py    # Test semantic components
    ├── test_operators.py   # Test individual operators
    ├── test_examples.py    # Test example formulas
    └── test_integration.py # Integration tests
```

### Running Tests

```bash
# Test your specific theory
python test_theories.py --theories my_theory

# Test theory library infrastructure
python test_package.py --components theory_lib

# Test everything
python test_package.py && python test_theories.py
```

For detailed testing guidance, see the [Theory Testing Framework Guide](../tests/README.md#theory-testing-framework-guide).

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

Create interactive notebooks for your theory:

```
my_theory/
└── notebooks/
    ├── README.md            # Notebook navigation guide
    ├── introduction.ipynb   # Basic introduction to the theory
    ├── operators.ipynb      # Examples of operator behavior
    └── countermodels.ipynb  # Interesting countermodel examples
```

#### Custom Visualizations

Theories can provide custom visualization methods:

```python
class CustomModelStructure(ModelDefaults):
    def visualize(self):
        """Custom visualization for this theory."""
        import matplotlib.pyplot as plt
        # Implement theory-specific visualization
        return plt.gcf()
```

For comprehensive information about Jupyter integration, see the [Jupyter Integration Documentation](../../jupyter/README.md).

## Licensing and Attribution

All theories in the ModelChecker Theory Library are licensed under the GNU General Public License v3.0 (GPL-3.0). This ensures that:

1. **Open Source Philosophy**: All theories remain freely available and modifiable
2. **Copyleft Protection**: Any derivative works must also be licensed under GPL-3.0
3. **Academic Attribution**: Academic credit is preserved through citation requirements

### Theory Licensing Structure

Each theory includes:

- **LICENSE.md**: Contains the GPL-3.0 license text specific to the theory
- **CITATION.md**: Contains proper academic citation information
- **Version Tracking**: Each theory has its own version, tracked in `__init__.py`

### License Compliance for Theory Authors

When contributing a theory:

1. Your theory must be compatible with GPL-3.0 licensing
2. You retain copyright for your theory implementation
3. By contributing, you agree to license your theory under GPL-3.0
4. Proper academic attribution will be maintained in CITATION.md

This structure ensures that the ModelChecker ecosystem remains open while providing proper attribution to theory authors.

---

[← Back to Theory Library](../README.md) | [Usage Guide →](USAGE_GUIDE.md) | [Architecture Guide →](THEORY_ARCHITECTURE.md)
