# Getting Started: Creating Your First ModelChecker Project

[← Back to Usage](README.md) | [Next: Workflow Overview →](WORKFLOW.md)

## Quick Start (2 minutes)

```bash
# Interactive mode - creates a project from logos template
model-checker
# Answer: y (to generate project)
# Enter: my_project (your project name)
# Result: project_my_project/ created

# OR copy from a specific theory
model-checker -l exclusion  # Copy exclusion theory
model-checker -l imposition  # Copy imposition theory
model-checker -l bimodal     # Copy bimodal theory

# Create logos project with specific subtheories (default loads all)
model-checker -l logos --subtheory modal       # Just modal + dependencies
model-checker -l logos --subtheory counterfactual constitutive  # Multiple
model-checker -l logos -st extensional         # Just extensional
```

You now have a complete project with:
- All theory files copied
- Relative imports working automatically
- Ready to run: `model-checker project_my_project/examples.py`

## What You Get

Your generated project is a **proper Python package** with these key files:

```
project_my_project/
├── semantic.py      # Core logic implementation
├── operators.py     # Logical operators (∧, ∨, →, etc.)
├── examples.py      # Test cases to run
├── __init__.py      # Makes it a Python package
└── .modelchecker    # Identifies as ModelChecker project
```

**Architecture Context**: For understanding how these files work together, see [Theory Library Architecture](../architecture/THEORY_LIB.md). For the complete system design, see [Architecture Overview](../architecture/README.md).

## First Steps After Creation

### 1. Test Your Project Works

```bash
cd project_my_project
model-checker examples.py  # Should show validity results
```

### 2. Create Your Own Examples

```python
# Create examples2.py with your own tests
cat > examples2.py << 'EOF'
from .semantic import *  # Relative imports work!
from .operators import *

MY_TEST_premises = ["A", "A → B"]
MY_TEST_conclusions = ["B"]
MY_TEST_settings = {'N': 3}

example_range = {
    "MY_TEST": [MY_TEST_premises, MY_TEST_conclusions, MY_TEST_settings]
}

semantic_theories = {"my_theory": get_theory()}
EOF

model-checker examples2.py  # Run your custom examples
```

### 3. Modify the Theory

Edit `semantic.py` to change how logic works, or `operators.py` to add new operators.

**Next Step**: Read [WORKFLOW.md](WORKFLOW.md) to understand the complete ModelChecker workflow.

---

## Detailed Guide

### Creating a New Project

#### Interactive Mode (Recommended for Beginners)

```bash
model-checker
# Prompts: "Would you like to generate a new logos-project? (y/n):"
# Enter: y
# Prompts: "Enter the name of your project using snake_case:"
# Enter: my_theory
# Creates: project_my_theory/
```

This copies the complete logos theory as your starting point.

#### Copying from Other Theories

Choose a different theory as your template:

```bash
model-checker -l exclusion   # Witness-based semantics
model-checker -l imposition   # Imposition semantics
model-checker -l bimodal      # Two modal operators
```

#### Selecting Logos Subtheories

For the logos theory, you can specify which subtheories to include:

```bash
# Load specific subtheories (default loads all)
model-checker -l logos --subtheory modal            # Modal logic operators
model-checker -l logos --subtheory counterfactual   # Counterfactual conditionals
model-checker -l logos -st constitutive relevance   # Multiple subtheories
```

Each theory provides different features:
- **logos**: Standard hyperintensional logic with modular subtheories
- **exclusion**: Uses witness states for verification
- **imposition**: Combines theories with imposition
- **bimodal**: Includes necessity and possibility operators

### Understanding Your Project Structure

#### Essential Files (You'll Edit These)

```python
# semantic.py - Define how your logic works
class MyTheorySemantics(Semantics):
    def _generate_constraints(self):
        # Your logical rules here
        
# operators.py - Define logical operators
class MyOperator(Operator):
    name = "\\oplus"  # Your operator symbol (LaTeX notation)
    arity = 2         # Number of arguments
    
# examples.py - Test cases
TEST_premises = ["A", "B"]
TEST_conclusions = ["A ∧ B"]
example_range = {"TEST": [TEST_premises, TEST_conclusions, {'N': 3}]}
```

#### Supporting Files (Automatically Handled)

- `__init__.py` - Makes relative imports work
- `.modelchecker` - Identifies as ModelChecker project
- `iterate.py` - Advanced model iteration (if needed)
- Other files depend on which theory you copied

### Running Examples

Your project supports unlimited example files with automatic relative imports:

```bash
# Run default examples
model-checker examples.py

# Create custom example files
model-checker examples2.py
model-checker test_modal.py
model-checker experiment.py
# All support relative imports!

# Run with options
model-checker examples.py --N=4           # More states
model-checker examples.py --verbose       # Debug output
model-checker examples.py --save markdown # Save results
```

**Key Feature**: All files in your project can use relative imports:
```python
from .semantic import MySemantics  # Works automatically!
from .operators import *           # No path configuration needed
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

### Local Testing

Generated projects are now proper Python packages, so relative imports work automatically:

```python
# examples.py - No modifications needed!
from .semantic import MyTheorySemantics  # Works out of the box
from .operators import get_operators     # Relative imports supported

# Your theory code with relative imports
def get_theory():
    """Get theory with local modifications."""
    return {
        'semantics': MyTheorySemantics,
        'operators': get_operators().operator_dictionary,
    }

# Rest of your examples...
```

You can create as many test files as needed:

```python
# test_custom.py - Create new files with relative imports
from .semantic import MyTheorySemantics
from .operators import my_custom_operator
from .examples import example_range

# Run your custom tests
semantics = MyTheorySemantics()
# ... test code ...
```

Then run any file directly:
```bash
# Run original examples
model-checker examples.py

# Run custom test files
model-checker test_custom.py

# All files support relative imports!
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

**Issue**: ImportError with relative imports (RESOLVED)
```bash
# Previous versions had issues with relative imports
# This is now automatically handled by package detection

# Projects created with older versions can be fixed by adding:
# 1. A .modelchecker marker file
# 2. An __init__.py file if missing

# Or regenerate the project with the latest version
model-checker -l your_theory

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

### Architecture Documentation
- [Theory Library Architecture](../architecture/THEORY_LIB.md) - Theory framework design
- [Builder Architecture](../architecture/BUILDER.md) - Project execution pipeline
- [Pipeline Overview](../architecture/PIPELINE.md) - Complete system data flow
- [Syntactic Architecture](../architecture/SYNTACTIC.md) - Formula parsing and AST
- [Models Architecture](../architecture/MODELS.md) - Semantic model generation

### Technical Documentation
- [Theory Library](../../Code/src/model_checker/theory_lib/README.md) - Existing theories
- [Syntactic Package](../../Code/src/model_checker/syntactic/README.md) - Operator and syntax handling
- [OperatorCollection API](../../Code/src/model_checker/syntactic/collection.py) - Operator registry class
- [Operator Base Classes](../../Code/src/model_checker/syntactic/operators.py) - Operator implementation
- [Contributing Guide](../../Code/src/model_checker/theory_lib/docs/CONTRIBUTING.md) - Contributing theories

---

[← Back to Usage](README.md) | [Workflow →](WORKFLOW.md) | [Examples →](EXAMPLES.md)
