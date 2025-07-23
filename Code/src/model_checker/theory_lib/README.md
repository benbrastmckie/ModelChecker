# TheoryLib

## Overview

The `TheoryLib` includes a collection of programmatic semantic theories implemented using Z3.
Each theory enables automated verification of the validity of logical arguments as well as the discovery of countermodels.

The library follows a modular architecture that allows:

- Comparison between different semantic theories
- Extension with new theories
- Reuse of common components
- Standardized testing and evaluation

## Available Theories

The theory library includes theories with different architectural approaches optimized for their semantic complexity. Each theory follows common interface patterns while adapting structure to their specific needs.

### Theory Architecture Patterns

The ModelChecker supports two primary theory architectures:

#### **Simple Theory Pattern** (Single-File Architecture)
Used by theories with focused semantic frameworks that don't require complex operator hierarchies.

**Structure:**
- `semantic.py`: Core semantic classes and relations
- `operators.py`: All operator implementations in a single file
- `examples.py`: Test cases and demonstrations
- `tests/`: Unit tests and example validation

**Example:** **Exclusion Theory** - implements unilateral semantics with a small set of operators

**Benefits:**
- Simple to understand and modify
- Direct access to all operators
- Minimal overhead
- Fast development and testing

#### **Modular Theory Pattern** (Subtheory Architecture)
Used by theories with complex operator hierarchies that benefit from logical organization.

**Structure:**
- `semantic.py`: Core semantic framework
- `operators.py`: Registry and loading system
- `examples.py`: Cross-subtheory test cases
- `subtheories/`: Organized operator groups
  - `extensional/`: Truth-functional operators
  - `modal/`: Modal logic operators
  - `constitutive/`: Content operators
  - `counterfactual/`: Counterfactual operators
- `tests/`: Multi-level testing infrastructure

**Example:** **Logos Theory** - implements a comprehensive hyperintensional framework with 20+ operators

**Benefits:**
- Logical organization of complex operator sets
- Selective loading of operator subsets
- Independent development of operator groups
- Manageable complexity for large theories

### Common Interface Elements

All theories implement these standard interfaces regardless of architecture:

1. **Semantic Classes**: `<Theory>Semantics`, `<Theory>Proposition`, `<Theory>Structure`
2. **Operator Collection**: Unified access through `.operator_dictionary`
3. **Testing Infrastructure**: Consistent test patterns and validation
4. **Documentation**: Standard README format with examples and API docs
5. **Jupyter Integration**: Compatible with interactive exploration tools

### Theory Selection Guide

**Choose Simple Pattern when:**
- Theory has fewer than 10 operators
- Operators don't form natural groupings
- Rapid prototyping is priority
- Theory is experimental or specialized

**Choose Modular Pattern when:**
- Theory has 10+ operators
- Operators fall into logical categories
- Selective operator loading is needed
- Multiple developers will contribute
- Theory integrates multiple logical systems

The library currently includes the following theories:

### Logos Theory (Modular Pattern)

The Logos provides a unified hyperintensional semantic theory using the **modular subtheory architecture**.

- **Theory Author**: Benjamin Brast-McKie
- **Implementation Author**: Benjamin Brast-McKie
- **Contributors**: Miguel Buitrago
- **Architecture**: Modular (5 subtheories with 20+ operators)
- **Description**: Implements a hyperintensional semantics for counterfactuals, constitutive operators, and modal logic.
- **Key Papers**:
  - Brast-McKie (2021) "Identity and Aboutness", Journal of Philosophical Logic
  - Brast-McKie (2025) "Counterfactual Worlds", Journal of Philosophical Logic
- **Key Features**:
  - Hyperintensional bilateral propositions
  - Truthmaker semantics for extensional connectives
  - Counterfactual conditionals via alternative world-states
  - Constitutive operators for essence, ground, and propositional identity
  - Selective subtheory loading: `logos.get_theory(['extensional', 'modal'])`

More information about the Logos theory can be found in [logos/README.md](logos/README.md).

**Interactive Learning**: [Jupyter Notebooks](logos/notebooks/README.md) - Complete tutorial collection with hands-on demonstrations

### Exclusion Theory (Simple Pattern)

The Exclusion Theory implements unilateral semantics using the **simple single-file architecture**.

- **Primary Authors**: Lucas Champollion & Paul Bernard
- **Implementation Authors**: Miguel Buitrago and Benjamin Brast-McKie
- **Architecture**: Simple (4 operators in single file)
- **Description**: Implements exclusion semantics for counterfactuals and related operators.
- **Key Paper**: Bernard & Champollion "Exclusion Counterfactuals"
- **Key Features**:
  - Unilateral operators (conjunction, disjunction, uninegation)
  - Witness-based exclusion semantics
  - Alternative approach to counterfactual semantics
  - Compact, focused implementation

More information about the exclusion theory can be found in [exclusion/README.md](exclusion/README.md).

**Interactive Learning**: [Jupyter Notebooks](exclusion/notebooks/README.md) - Explore unilateral semantics and architectural innovations

### Imposition Theory

- **Primary Author**: Kit Fine
- **Description**: Implements Fine's truthmaker semantics for counterfactuals.
- **Implementation Author**: Benjamin Brast-McKie
- **Key Papers**:
  - Fine (2012) "Counterfactuals without Possible Worlds", Journal of Philosophy
  - Fine (2012) "A Theory of Truth-Conditional Content", Synthese
- **Key Features**:
  - Imposition operator for counterfactuals
  - Could operator for possibility
  - Distinctive approach to counterfactual reasoning

More information abut the imposition theory can be found in [imposition/README.md](imposition/README.md).

### Bimodal Theory

- **Theory Author**: Benjamin Brast-McKie
- **Implementation Author**: Benjamin Brast-McKie
- **Description**: Includes modal and temporal operators
- **Key Features**: Interaction between tense and circumstantial modality

More information abut the bimodal theory can be found in [bimodal/README.md](bimodal/README.md).

## Using Theories

This section includes details for the following:

- Import Strategies
- Basic Usage Examples
- Theory Selection and Configuration
- Comparing Theories

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
theory = get_theory("logos")  # or "exclusion", "imposition", "bimodal"

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
model = BuildExample("example_name", get_theory("logos"), settings=settings)
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

## Contributing New Theories

New semantic theories can be submitted to the ModelChecker Theory Library by following the guidelines detailed below.
For questions or assistance, please open an [issue](https://github.com/benbrastmckie/ModelChecker/issues) on the GitHub repository, providing a detailed description of the problem that you are having and creating a new issue for each separate topic.

### Implementation Guides

- **[Theory Architecture Guide](docs/THEORY_ARCHITECTURE.md)**: Choose between Simple and Modular patterns based on your theory's complexity
- **[Theory Testing Framework Guide](tests/README.md#theory-testing-framework-guide)**: Comprehensive testing implementation for both architectural patterns
- **[Jupyter Integration](../jupyter/README.md)**: Make your theory available in interactive notebooks

### Why Contribute?

- **Share your research**: Make your semantic theory accessible to other researchers
- **Enable verification**: Allow others to test logical arguments in your framework
- **Receive feedback**: Get input from the community on your semantic approach
- **Compare theories**: See how your theory handles examples compared to others

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

### Getting Started

Follow these steps to develop and contribute a new theory to the ModelChecker project:

1. **Fork and Clone**:
   ```bash
   # First, fork the repository on GitHub
   # Then clone your fork
   git clone https://github.com/YOUR-USERNAME/ModelChecker.git
   cd ModelChecker
   
   # Add the original repo as upstream
   git remote add upstream https://github.com/benbrastmckie/ModelChecker.git
   ```

2. **Create a New Branch**:
   ```bash
   git checkout -b theory/my-new-theory
   ```

3. **Generate a Template Project**:
   Choose the existing `THEORY_NAME` that most closely resembles your intended theory (e.g., default, bimodal, exclusion, imposition) and use it as a template:
   ```bash
   model-checker -l THEORY_NAME
   ```
   This creates a local project with all necessary files based on the bimodal theory.
   Choose an appropriate `theory_name` for your project, where the theory directory will be renamed again later.

4. **Implement Your Theory**:
   Modify the generated files to implement your semantic framework:
   - `semantic.py`: Define your semantic classes and relations
   - `operators.py`: Implement your logical operators
   - `examples.py`: Create test cases specific to your theory
   - `__init__.py`: Update exports with your theory's classes
   - `README.md`: Document your theory's features and usage

5. **Test Your Implementation**:
   ```bash
   # Run your examples
   model-checker examples.py
   
   # Run specific tests
   model-checker -t my_test_name
   ```

6. **Move Your Theory to the Library**:
   Once your theory is working locally, integrate it into the main library:
   ```bash
   # Create a directory for your theory in the library
   mkdir -p Code/src/model_checker/theory_lib/my_theory
   
   # Move your project directory to the theory library
   mv project_theory_name/* Code/src/model_checker/theory_lib/my_theory/
   ```

7. **Register Your Theory**:
   Add your theory to the `__all__` list in `Code/src/model_checker/theory_lib/__init__.py`:
   ```python
   __all__ = [
       "default",
       "exclusion",
       "imposition",
       "bimodal",
       "my_theory"  # Add your theory here
   ]
   ```

8. **Submit a Pull Request**:
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
   
   Then go to your fork on GitHub and click "Compare & pull request". In your pull request:
   - Use a clear title that describes your theory (e.g. "Add MyTheory implementation")
   - Provide a detailed description including:
     - Overview of your semantic theory
     - Key features and innovations
     - References to relevant papers
     - Example use cases
     - Any special requirements or dependencies
   - Check that the "base repository" is set to the main ModelChecker repo
   - Check that the "base" branch is `main`
   - Check that the "head repository" is your fork
   - Check that the "compare" branch is `theory/my-new-theory`
   
   Then open a pull request on GitHub with:
   - A clear description of your theory
   - References to relevant papers or research
   - Examples of what makes your theory unique
   - Any special requirements or dependencies

### Required Files for a New Theory

Each theory must include these core files:

- `semantic.py`: Define your semantic framework
- `operators.py`: Implement your logical operators
- `examples.py`: Create test cases
- `__init__.py`: Export your public API
- `README.md`: Document your theory

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

my_operators = syntactic.OperatorCollection(
    # primitive extensional operators
    NegationOperator,
    AndOperator,
    OrOperator,

    # new operators
    NewOperator,
    OtherNewOperator,

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
```markdown
theory_lib/
└── my_theory/
    ├── __init__.py
    ├── semantic.py
    ├── operators.py
    ├── examples.py
    ├── test/
    │   ├── test_semantic.py     # Tests for semantic components
    │   ├── test_operators.py    # Tests for operators
    │   └── test_examples.py     # Tests for example models
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

## Testing

The theory library includes comprehensive testing infrastructure to ensure reliability and correctness across all semantic theories.

### Test Organization

**Infrastructure Tests** ([tests/README.md](tests/README.md)):
- Common functionality shared across theories
- Metadata management (versioning, citations, licenses)
- Theory discovery and loading mechanisms
- Cross-theory compatibility and integration

**Theory-Specific Tests**:
- Individual theory implementations and their logical properties
- See individual theory directories for detailed test documentation:
  - [logos/tests/README.md](logos/tests/README.md) - Logos theory and subtheories
  - [default/tests/README.md](default/tests/README.md) - Default semantic theory
  - [exclusion/tests/README.md](exclusion/tests/README.md) - Exclusion semantics
  - [imposition/tests/README.md](imposition/tests/README.md) - Imposition semantics
  - [bimodal/tests/README.md](bimodal/tests/README.md) - Bimodal temporal logic

### Running Tests

```bash
# Test theory library infrastructure
python test_package.py --components theory_lib

# Test specific theories
python test_theories.py --theories logos exclusion imposition

# Test everything
python test_package.py && python test_theories.py
```

For detailed testing information, debugging guides, and development workflows, see [tests/README.md](tests/README.md).

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
