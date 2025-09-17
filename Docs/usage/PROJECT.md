# Creating and Developing ModelChecker Projects

[← Back to Usage](README.md) | [Workflow →](WORKFLOW.md) | [Examples →](EXAMPLES.md)

## Table of Contents

1. [Overview](#overview)
2. [Creating a New Project](#creating-a-new-project)
   - [Basic Project Creation](#basic-project-creation)
   - [Copying from Existing Theories](#copying-from-existing-theories)
   - [Project Structure](#project-structure)
3. [Development Workflow](#development-workflow)
   - [Running Examples Locally](#running-examples-locally)
   - [Modifying Semantics](#modifying-semantics)
   - [Adding Operators](#adding-operators)
   - [Creating Examples](#creating-examples)
4. [Testing Your Project](#testing-your-project)
   - [Local Testing](#local-testing)
   - [Unit Tests](#unit-tests)
   - [Integration Testing](#integration-testing)
5. [Project Management](#project-management)
   - [Version Control](#version-control)
   - [Documentation](#documentation)
   - [Publishing](#publishing)
6. [Common Patterns](#common-patterns)
7. [Troubleshooting](#troubleshooting)

## Overview

This guide covers creating new ModelChecker projects for developing custom semantic theories. You'll learn how to generate project scaffolding, copy from existing theories, and develop your theory using local project files without needing to modify the core ModelChecker installation.

## Creating a New Project

### Basic Project Creation

Generate a new project with the `model-checker` command without any arguments:

```bash
# Run without arguments to enter interactive mode
model-checker

# You'll be prompted:
# "Would you like to generate a new logos-project? (y/n):"
# Answer 'y' and enter your project name

# This creates (copying from logos template):
# project_<your_name>/
#   ├── __init__.py          # Package initialization
#   ├── semantic.py          # Core semantics implementation  
#   ├── operators.py         # Operator definitions
#   ├── examples.py          # Example formulas and test cases
#   ├── iterate.py           # Model iteration utilities
#   ├── README.md            # Theory documentation
#   ├── VERSION              # Version number
#   ├── LICENSE.md           # GPL-3.0 license
#   ├── CITATION.md          # Citation information
#   ├── docs/                # Additional documentation
#   ├── tests/               # Unit and integration tests
#   └── subtheories/         # Modular subtheories (logos only)
```

### Copying from Existing Theories

Base your project on an existing theory using the `-l` (load_theory) flag:

```bash
# Copy from logos theory (interactive mode)
model-checker -l logos
# Prompts: "Would you like to generate a new logos-project? (y/n):"
# Then: "Enter the name of your project using snake_case:"

# Copy from exclusion theory
model-checker -l exclusion

# Copy from imposition theory  
model-checker -l imposition

# Copy from bimodal theory
model-checker -l bimodal
```

The `-l` flag loads a specific theory template and enters interactive mode where you'll be prompted for a project name. The complete structure and code from the specified theory is copied, giving you a working starting point.

### Project Structure

After creation, your project contains the actual files from the theory template:

```
project_my_theory/
├── __init__.py              # Package initialization with get_theory()
├── semantic.py              # Semantic class implementation
│   └── class TheorySemantics(Semantics):
│       ├── def __init__(self)
│       ├── def _generate_constraints(self)
│       └── operator methods (true_at, compute_verifiers, etc.)
├── operators.py             # Operator class definitions
│   └── class CustomOperator(Operator):
│       ├── name = "symbol"
│       ├── arity = N
│       └── def true_at(self, ...)
├── examples.py              # Test examples and configurations
│   ├── example_range = {...}      # Named test cases
│   └── semantic_theories = {...}  # Theory configurations
├── iterate.py               # Model iteration utilities
│   └── class TheoryModelIterator:
│       └── def iterate_models(self, ...)
├── tests/                   # Test suite
│   ├── __init__.py
│   ├── unit/               # Unit tests
│   ├── integration/        # Integration tests
│   └── fixtures/           # Test data
├── docs/                    # Documentation
│   ├── README.md           # Usage guide
│   ├── API_REFERENCE.md   # API documentation
│   └── ARCHITECTURE.md    # Design decisions
├── README.md                # Main documentation
├── VERSION                  # Version number (e.g., "1.0.0")
├── LICENSE.md              # GPL-3.0 license text
└── CITATION.md             # How to cite this theory

Additional directories (theory-specific):
├── subtheories/            # Modular components (logos)
├── notebooks/              # Jupyter notebooks (exclusion, imposition)
├── history/                # Version history (exclusion)
└── reports/                # Analysis reports (imposition)
```

## Development Workflow

### Running Examples Locally

Run examples using your local project files without installation:

```bash
# Navigate to your project
cd project_my_theory

# Run examples directly
model-checker examples.py

# Run with specific settings
model-checker examples.py --N=4 --verbose

# Run specific examples
model-checker examples.py --example=TEST_1

# Save output for analysis
model-checker examples.py --save markdown
```

### Modifying Semantics

Edit `semantic.py` to implement your semantic theory:

```python
# semantic.py  
from model_checker.semantic import Semantics, Proposition, ModelStructure
from model_checker.syntactic import OperatorCollection
from z3 import *

class MyTheorySemantics(Semantics):
    """Custom semantic theory implementation."""
    
    def __init__(self, operators=None):
        super().__init__()
        # Initialize your semantics
        self.name = "My Theory"
        
        # Set up operators if provided
        if operators:
            self.operator_collection = operators
        else:
            from .operators import get_operators
            self.operator_collection = get_operators()
        
    def _generate_constraints(self):
        """Generate Z3 constraints for your semantics."""
        constraints = []
        
        # Add your semantic constraints
        # Example: reflexivity for modal operators
        if self.settings.get('reflexive', False):
            for w in range(self.N):
                constraints.append(self.R[w][w])
        
        return constraints
    
    def evaluate(self, formula, eval_point):
        """Evaluate formula at given point."""
        # Delegate to operators
        op = self.operator_collection[formula.operator]
        return op(self).true_at(*formula.arguments, eval_point)
```

### Adding Operators

Define new operators in `operators.py` using the `OperatorCollection` class and `Operator` base classes:

```python
# operators.py
from model_checker.syntactic import Operator, OperatorCollection

class NegationOperator(Operator):
    """Custom negation operator."""
    name = "\\neg"
    arity = 1
    
    def true_at(self, arg, eval_point):
        """Negation is true when argument is false."""
        # Classical truth condition
        return not self.semantics.evaluate(arg, eval_point)
    
    def false_at(self, arg, eval_point):
        """Negation is false when argument is true."""
        return self.semantics.evaluate(arg, eval_point)
    
    def extended_verify(self, verifier, arg, eval_point):
        """A state verifies ¬A if it falsifies A."""
        # For hyperintensional semantics
        return self.semantics.extended_falsify(verifier, arg, eval_point)
    
    def extended_falsify(self, falsifier, arg, eval_point):
        """A state falsifies ¬A if it verifies A."""
        return self.semantics.extended_verify(falsifier, arg, eval_point)
    
    def compute_verifiers(self, arg, model, eval_point):
        """Compute verifiers as falsifiers of the argument."""
        # Optional: for extracting exact verifier sets
        return self.semantics.compute_falsifiers(arg, model, eval_point)

class IndicativeConditional(Operator):
    """Custom indicative conditional operator."""
    name = "\\Rightarrow"
    arity = 2
    
    def true_at(self, antecedent, consequent, eval_point):
        """Define indicative conditional truth conditions."""
        # Your custom implementation
        # Example: material conditional with relevance constraint
        pass
    
    def false_at(self, antecedent, consequent, eval_point):
        """Define when indicative conditional is false."""
        # Your custom implementation
        pass
    
    # ... other methods like extended_verify, extended_falsify ...
    
    def compute_verifiers(self, antecedent, consequent, model, eval_point):
        """Compute verifiers for hyperintensional semantics."""
        # Optional: implement for truthmaker semantics
        pass

# Create operator collection
def get_operators():
    """Return operator collection for this theory."""
    collection = OperatorCollection()
    
    # Add individual operators
    collection.add_operator(NegationOperator)
    collection.add_operator(ConjunctionOperator) 
    collection.add_operator(IndicativeConditional)
    
    # Or add multiple at once
    collection.add_operator([
        DisjunctionOperator,
        ImplicationOperator,
        NecessityOperator,
        PossibilityOperator
    ])
    
    return collection
```

The `OperatorCollection` class manages operator registration and provides methods to:
- `add_operator()`: Add single or multiple operators
- Apply operators to prefix notation sentences
- Look up operators by name

See [syntactic/collection.py](../../Code/src/model_checker/syntactic/collection.py) for the full API.

### Creating Examples

Add test cases to `examples.py`:

```python
# examples.py
from .semantic import MyTheorySemantics
from .operators import get_operators

# Initialize your theory
def get_theory():
    """Get theory with operators."""
    operators = get_operators()
    return {
        'semantics': MyTheorySemantics,
        'operators': operators.operator_dictionary,
    }

theory = get_theory()

# Example 1: Basic test
BASIC_TEST_premises = ["A", "A \\rightarrow B"]
BASIC_TEST_conclusions = ["B"]
BASIC_TEST_settings = {'N': 3}
BASIC_TEST_example = [
    BASIC_TEST_premises,
    BASIC_TEST_conclusions,
    BASIC_TEST_settings
]

# Example 2: Custom operator test
INDICATIVE_TEST_premises = ["A \\Rightarrow B", "A"]
INDICATIVE_TEST_conclusions = ["B"]
INDICATIVE_TEST_settings = {
    'N': 3,
    'require_relevance': True  # Custom setting for indicative conditional
}
INDICATIVE_TEST_example = [
    INDICATIVE_TEST_premises,
    INDICATIVE_TEST_conclusions,
    INDICATIVE_TEST_settings
]

# Export examples
example_range = {
    'BASIC_TEST': BASIC_TEST_example,
    'INDICATIVE_TEST': INDICATIVE_TEST_example,
}

semantic_theories = {
    'my_theory': theory
}
```

## Testing Your Project

### Important Note on Local Development

**Current Limitation**: Generated projects copy files from theory templates that use relative imports (like `from .semantic import`). However, when you run `model-checker examples.py` on these files, the relative imports will fail with "attempted relative import with no known parent package" because the files are not being run as part of a proper Python package structure.

### Workarounds for Local Testing

To test local changes, you need to modify your `examples.py` file to use explicit local imports:

```python
# examples.py - Modified for local testing
import sys
import os

# Add current directory to path for local imports
sys.path.insert(0, os.path.dirname(__file__))

# Use direct imports instead of relative imports
import semantic  # Import local semantic.py
import o

# Create your theory using local modules
def get_theory():
    """Get theory with local modifications."""
    return {
        'semantics': semantic.MyTheorySemantics,
        'operators': operators.get_operators().operator_dictionary,
    }

# Rest of your examples...
```

Alternative approach - create a standalone test file:

```bash
# Create test_local.py in your project directory
# This file uses absolute local imports

# test_local.py
import sys
import os
sys.path.insert(0, os.path.dirname(__file__))

from semantic import MyTheorySemantics
from operators import get_operators
from examples import example_range

# Run your tests here
semantics = MyTheorySemantics()
# ... test code ...
```

Then run:
```bash
# Run your local test file
python test_local.py

# Or use model-checker on the modified examples
model-checker examples.py
```

### Unit Tests

Create unit tests in `tests/`:

```python
# tests/test_semantic.py
import pytest
from ..semantic import MyTheorySemantics
from ..operators import my_theory_operators

def test_basic_semantics():
    """Test basic semantic functionality."""
    sem = MyTheorySemantics()
    sem.settings = {'N': 3}
    
    # Test your semantics
    constraints = sem._generate_constraints()
    assert len(constraints) > 0

def test_custom_operator():
    """Test custom operator implementation."""
    sem = MyTheorySemantics()
    
    # Test indicative conditional operator
    result = sem.evaluate_indicative("A", "B", {'world': 0})
    assert result is not None

def test_example_validity():
    """Test that examples work correctly."""
    from ..examples import example_range, semantic_theories
    
    # Run basic test
    theory = semantic_theories['my_theory']
    example = example_range['BASIC_TEST']
    
    # Use model checker to validate
    # ... test implementation
```

### Integration Testing

Test integration with ModelChecker framework:

```bash
# Run integration tests
./run_tests.py project_my_theory

# Test with different configurations
model-checker examples.py --test-all-settings

# Benchmark performance
model-checker examples.py --benchmark
```

## Project Management

### Version Control

Initialize git repository for your project:

```bash
cd project_my_theory
git init
git add .
git commit -m "Initial project structure"

# Create .gitignore
cat > .gitignore << EOF
__pycache__/
*.pyc
.pytest_cache/
output/
*.log
EOF

git add .gitignore
git commit -m "Add gitignore"
```

### Documentation

Document your theory in `docs/`:

```markdown
# docs/THEORY.md

## Theoretical Background

My theory extends classical logic with...

## Semantic Framework

The semantics are based on...

## Operator Definitions

- **Indicative Conditional (⇒)**: An indicative conditional A ⇒ B is true when...

## Examples

See examples.py for test cases demonstrating...
```

### Publishing

Share your project:

```bash
# Package for distribution
python setup.py sdist

# Install locally for testing
pip install -e .

# Share via GitHub
git remote add origin https://github.com/user/my_theory.git
git push -u origin main
```

## Common Patterns

### Pattern 1: Extending Existing Theory

```python
# semantic.py - Extend logos with custom features
from model_checker.theory_lib.logos import LogosSemantics

class MyExtendedLogos(LogosSemantics):
    def __init__(self):
        super().__init__()
        self.name = "Extended Logos"
    
    def _generate_constraints(self):
        # Get base constraints
        constraints = super()._generate_constraints()
        
        # Add your extensions
        constraints.extend(self._my_custom_constraints())
        
        return constraints
```

### Pattern 2: Combining Multiple Theories

```python
# semantic.py - Combine features from multiple theories
from model_checker.theory_lib.logos import LogosSemantics
from model_checker.theory_lib.exclusion import ExclusionSemantics

class HybridSemantics(LogosSemantics):
    def __init__(self):
        super().__init__()
        self.exclusion = ExclusionSemantics()
    
    def _generate_constraints(self):
        constraints = super()._generate_constraints()
        
        # Add exclusion-style witnesses
        constraints.extend(self.exclusion._witness_constraints())
        
        return constraints
```

### Pattern 3: Theory with Custom Settings

```python
# In examples.py - settings are defined per example
CUSTOM_SETTINGS = {
    'N': 3,
    'max_time': 30,
    
    # Custom theory settings
    'require_relevance': True,
    'relevance_depth': 2,
    'allow_vacuous': False,
}

# semantic.py
class MyTheorySemantics(Semantics):
    def _generate_constraints(self):
        constraints = []
        
        if self.settings.get('require_relevance', True):
            constraints.extend(self._relevance_constraints())
        
        if not self.settings.get('allow_vacuous', False):
            constraints.extend(self._non_vacuous_constraints())
        
        return constraints
```

## Troubleshooting

### Common Issues

**Issue**: ImportError when running examples
```bash
# Solution: Run from project directory
cd project_my_theory
model-checker examples.py

# Or add to PYTHONPATH
export PYTHONPATH="${PYTHONPATH}:$(pwd)"
```

**Issue**: Custom operators not recognized
```python
# Solution: Register operators using OperatorCollection
# In operators.py
from model_checker.syntactic import OperatorCollection

collection = OperatorCollection()
collection.add_operator(MyCustomOperator)

# In semantic.py
from .operators import get_operators

def __init__(self):
    super().__init__()
    self.operator_collection = get_operators()
```

**Issue**: Settings not applied
```python
# Solution: Check settings hierarchy
# Command line > Example > Theory defaults
print(self.settings)  # Debug settings in semantic.py
```

**Issue**: Z3 timeout with complex semantics
```python
# Solution: Optimize constraints
# 1. Reduce N value
# 2. Simplify constraints
# 3. Use incremental solving
```

### Development Tips

1. **Start Simple**: Begin with basic operators, add complexity gradually
2. **Test Often**: Run examples after each change
3. **Use Debug Output**: `--print-constraints` and `--verbose` are your friends
4. **Check Existing Theories**: Look at theory_lib for implementation patterns
5. **Document as You Go**: Update docs/ while features are fresh

## See Also

### Usage Guides
- [Workflow Guide](WORKFLOW.md) - General ModelChecker usage
- [Examples Guide](EXAMPLES.md) - Writing example files
- [Settings Guide](SETTINGS.md) - Configuration options
- [Output Guide](OUTPUT.md) - Saving results

### Technical Documentation  
- [Theory Library](../../Code/src/model_checker/theory_lib/README.md) - Existing theories
- [Syntactic Package](../../Code/src/model_checker/syntactic/README.md) - Operator and syntax handling
- [OperatorCollection API](../../Code/src/model_checker/syntactic/collection.py) - Operator registry class
- [Operator Base Classes](../../Code/src/model_checker/syntactic/operators.py) - Operator implementation
- [Contributing Guide](../../Code/src/model_checker/theory_lib/docs/CONTRIBUTING.md) - Contributing theories
- [Architecture](../architecture/THEORY_LIB.md) - Theory framework design

---

[← Back to Usage](README.md) | [Workflow →](WORKFLOW.md) | [Examples →](EXAMPLES.md)
