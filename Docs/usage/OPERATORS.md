# Operators Guide

This guide explains how to define and work with operators in the ModelChecker framework, both by using existing defined operators and creating new primitive operators.

## Table of Contents

- [Understanding Operators](#understanding-operators)
- [Using Defined Operators](#using-defined-operators)
- [Creating New Defined Operators](#creating-new-defined-operators)
- [Defining Primitive Operators](#defining-primitive-operators)
- [Operator Dependencies](#operator-dependencies)
- [Testing Custom Operators](#testing-custom-operators)

## Understanding Operators

In the ModelChecker framework, operators come in two types:

1. **Primitive Operators**: Base-level operators that directly generate Z3 constraints
2. **Defined Operators**: Operators built from primitive operators or other defined operators

**Architecture Context**: For the theoretical foundations of operator processing and AST construction, see [Syntactic Architecture](../architecture/SYNTACTIC.md). For how operators integrate with the semantic framework, see [Semantics Architecture](../architecture/SEMANTICS.md).

### Architecture Overview

The ModelChecker uses a clean separation between semantic framework and operator implementations:

- **Operators** (`operators.py`) - Standalone classes that define logical behavior
- **Semantics** (`semantic.py`) - Framework that coordinates operators and provides infrastructure
- **Registry** (`get_operators()`) - Discovery mechanism that makes operators available to the framework

**Key Point**: Operators are NOT defined in `semantic.py`. The semantic class provides methods like `true_at()`, `false_at()`, etc., but these are framework methods that delegate to the appropriate operator implementations. Each operator is a separate class that implements its own semantic behavior.

**Architecture Deep Dive**: For the complete pipeline showing how operators are parsed, processed, and evaluated, see [Pipeline Architecture](../architecture/PIPELINE.md). For theory-specific operator organization, see [Theory Library Architecture](../architecture/THEORY_LIB.md).

## Using Defined Operators

Defined operators are specified in your theory's `operators.py` file. They allow you to create complex logical operators from simpler ones.

### Basic Structure

The ModelChecker framework supports two types of operators: **primitive operators** (implemented as classes) and **defined operators** (implemented as syntactic.DefinedOperator subclasses).

### Defined Operators

Defined operators are built from existing primitive or defined operators. They inherit from `syntactic.DefinedOperator` and implement a `derived_definition()` method that specifies how they decompose into simpler operators.

```python
# operators.py
from model_checker import syntactic

class ConditionalOperator(syntactic.DefinedOperator):
    """Material conditional operator (A → B)."""

    name = "\\rightarrow"
    arity = 2

    def derived_definition(self, leftarg, rightarg):
        # Define A → B as ¬A ∨ B using existing operators
        return [OrOperator, [NegationOperator, leftarg], rightarg]

class PossibilityOperator(syntactic.DefinedOperator):
    """Possibility operator (◇A)."""

    name = "\\Diamond"
    arity = 1

    def derived_definition(self, argument):
        # Define ◇A as ¬□¬A
        return [NegationOperator, [NecessityOperator, [NegationOperator, argument]]]
```

For more examples, see the [modal operators](../../../Code/src/model_checker/theory_lib/logos/subtheories/modal/operators.py) in the logos theory.

All operators must be registered with the framework through the operator registration system - see [Operator Registration System](#operator-registration-system) for details on how this works.

### Available Syntax

When defining operators, you can use:

- Parentheses for grouping: `(A \\wedge B)`
- Existing primitive operators from your semantic theory
- Other defined operators (they're resolved in dependency order)
- Variable placeholders: `A`, `B`, `C`, etc. for the operator's arguments

### LaTeX Notation Requirements

Always use LaTeX commands in your operator definitions:

| Operator              | LaTeX Code         | Example Usage            |
| --------------------- | ------------------ | ------------------------ |
| Negation              | `\\neg`            | `\\neg A`                |
| Conjunction           | `\\wedge`          | `(A \\wedge B)`          |
| Disjunction           | `\\vee`            | `(A \\vee B)`            |
| Implication           | `\\rightarrow`     | `(A \\rightarrow B)`     |
| Biconditional         | `\\leftrightarrow` | `(A \\leftrightarrow B)` |
| Necessity             | `\\Box`            | `\\Box A`                |
| Possibility           | `\\Diamond`        | `\\Diamond A`            |
| Counterfactual        | `\\boxright`       | `(A \\boxright B)`       |
| Constitutive Identity | `\\equiv`          | `(A \\equiv B)`          |

## Creating New Defined Operators

To add a new defined operator to your theory:

1. **Open `operators.py`** in your project directory

2. **Add your operator class**:

```python
from model_checker import syntactic

class XorOperator(syntactic.DefinedOperator):
    """Exclusive or operator (A ⊕ B)."""

    name = "\\oplus"
    arity = 2

    def derived_definition(self, leftarg, rightarg):
        # Define A ⊕ B as (A ∧ ¬B) ∨ (¬A ∧ B)
        left_part = [AndOperator, leftarg, [NegationOperator, rightarg]]
        right_part = [AndOperator, [NegationOperator, leftarg], rightarg]
        return [OrOperator, left_part, right_part]
```

3. **Use in examples**:

```python
# examples.py
premises = ["(P \\oplus Q)"]  # Using your new XOR operator
conclusions = ["\\neg (P \\wedge Q)"]
```

## Defining Primitive Operators

Primitive operators are implemented as standalone classes that inherit from `syntactic.Operator`. They define the core semantic behavior through Z3 constraints and must implement specific methods for truth conditions, verification, and falsification.

### Understanding Primitive Operators

Primitive operators implement the fundamental semantic operations of your theory. Each operator class must implement:

- `true_at()` - defines when the operator is true at an evaluation point
- `false_at()` - defines when the operator is false at an evaluation point
- `extended_verify()` - defines what states verify the operator (hyperintensional semantics)
- `extended_falsify()` - defines what states falsify the operator (hyperintensional semantics)
- `find_verifiers_and_falsifiers()` - computes the actual verifier/falsifier sets

### Steps to Add a Primitive Operator

1. **Create the operator class in `operators.py`**:

```python
# operators.py
import z3
from model_checker import syntactic
from model_checker.utils import ForAll, Exists

class MyPrimitiveOperator(syntactic.Operator):
    """Implementation of my primitive operator (⊗)."""

    name = "\\otimes"  # LaTeX command
    arity = 2          # Binary operator

    def true_at(self, leftarg, rightarg, eval_point):
        """Defines when A ⊗ B is true at an evaluation point."""
        semantics = self.semantics
        # Define truth conditions using Z3 constraints
        return z3.And(
            semantics.true_at(leftarg, eval_point),
            semantics.true_at(rightarg, eval_point)
            # Add your specific logic here
        )

    def false_at(self, leftarg, rightarg, eval_point):
        """Defines when A ⊗ B is false at an evaluation point."""
        semantics = self.semantics
        # Define falsity conditions using Z3 constraints
        return z3.Or(
            semantics.false_at(leftarg, eval_point),
            semantics.false_at(rightarg, eval_point)
            # Add your specific logic here
        )

    def extended_verify(self, state, leftarg, rightarg, eval_point):
        """Defines what states verify A ⊗ B."""
        semantics = self.semantics
        # Define verification conditions
        # This determines what states make the formula true
        return z3.And(
            # Add your hyperintensional verification logic
        )

    def extended_falsify(self, state, leftarg, rightarg, eval_point):
        """Defines what states falsify A ⊗ B."""
        semantics = self.semantics
        # Define falsification conditions
        # This determines what states make the formula false
        return z3.And(
            # Add your hyperintensional falsification logic
        )

    def find_verifiers_and_falsifiers(self, leftarg, rightarg, eval_point):
        """Computes the actual verifier and falsifier sets."""
        # Get verifiers/falsifiers from arguments
        left_V, left_F = leftarg.proposition.find_proposition()
        right_V, right_F = rightarg.proposition.find_proposition()

        # Compute based on your operator's semantics
        # Example: intersection for conjunction-like behavior
        verifiers = left_V.intersection(right_V)
        falsifiers = left_F.union(right_F)

        return verifiers, falsifiers
```

2. **Register the operator in `get_operators()`**:

```python
# At the end of operators.py
def get_operators():
    """Get all operators defined in this module."""
    return {
        "\\otimes": MyPrimitiveOperator,
        # ... other operators
    }
```

### Real Examples

For concrete examples of primitive operators, see:

- [NecessityOperator](../../../Code/src/model_checker/theory_lib/logos/subtheories/modal/operators.py) - Modal necessity (□)
- [AndOperator](../../../Code/src/model_checker/theory_lib/logos/subtheories/extensional/operators.py) - Conjunction (∧)
- [CounterfactualOperator](../../../Code/src/model_checker/theory_lib/logos/subtheories/counterfactual/operators.py) - Counterfactual conditional (□→)

These show the complete implementation pattern including Z3 constraint generation, hyperintensional semantics, and verifier/falsifier computation.

## Operator Dependencies

When defining operators that depend on other defined operators:

1. The framework automatically resolves dependencies through imports
2. Circular dependencies will raise import errors
3. Import the operators you need at the top of your operators.py file

Example with dependencies:

```python
# operators.py
from model_checker import syntactic
# Import operators this operator depends on
from .extensional.operators import NegationOperator
from .modal.operators import NecessityOperator

class PossibilityOperator(syntactic.DefinedOperator):
    """Possibility operator defined using necessity and negation."""

    name = "\\Diamond"
    arity = 1

    def derived_definition(self, argument):
        # Define ◇A as ¬□¬A (uses imported operators)
        return [NegationOperator, [NecessityOperator, [NegationOperator, argument]]]

class ContingentOperator(syntactic.DefinedOperator):
    """Contingency operator defined using possibility."""

    name = "\\nabla"
    arity = 1

    def derived_definition(self, argument):
        # Define ∇A as (◇A ∧ ◇¬A) (uses PossibilityOperator defined above)
        return [AndOperator,
                [PossibilityOperator, argument],
                [PossibilityOperator, [NegationOperator, argument]]]
```

The operator registry handles loading all operators in the correct order based on their dependencies.

## Operator Registration System

The operator registration system is how the ModelChecker framework discovers, loads, and integrates operators from different modules. Every operator module must implement a `get_operators()` function that exports its operators to the framework.

### Why Registration Matters

The registration system serves several critical purposes:

1. **Operator Discovery** - Tells the framework which operators are available in a module
2. **Parser Integration** - Maps LaTeX operator names to their implementation classes
3. **Dependency Management** - Ensures operators are loaded in the correct order
4. **Theory Composition** - Allows theories to selectively include operators from subtheories
5. **Modularity** - Each module exports only its own operators
6. **Flexibility** - Theories can easily enable/disable operators by modifying the dictionary

### Basic Registry Structure

Every `operators.py` file must end with a `get_operators()` function:

```python
# At the end of operators.py
def get_operators():
    """
    Registry function that exports all operators in this module.

    The framework calls this function to discover available operators
    and register them with the parser and semantic system.

    Returns:
        dict: Dictionary mapping LaTeX operator names to operator classes
    """
    return {
        # Primitive operators
        "\\neg": NegationOperator,
        "\\wedge": AndOperator,
        "\\vee": OrOperator,
        "\\Box": NecessityOperator,

        # Defined operators
        "\\rightarrow": ConditionalOperator,
        "\\Diamond": PossibilityOperator,

        # Custom operators
        "\\otimes": MyCustomOperator,
    }
```

### How Registration Works

1. **Module Import**: The framework imports your operators.py module
2. **Registry Call**: It calls `get_operators()` to discover available operators
3. **Class Registration**: Each operator class is registered with its LaTeX name
4. **Parser Integration**: The LaTeX names become available to the formula parser
5. **Semantic Integration**: Operators are linked to the semantic evaluation system

### Registration in Practice

Here's how different theories handle registration:

**Simple Theory (Single Module):**
```python
# All operators in one file
def get_operators():
    return {
        "\\neg": NegationOperator,
        "\\wedge": AndOperator,
        "\\Box": NecessityOperator,
    }
```

**Complex Theory (Multiple Submodules):**
```python
# Main theory coordinates subtheories
from .extensional.operators import get_operators as get_ext_ops
from .modal.operators import get_operators as get_modal_ops

def get_operators():
    operators = {}
    operators.update(get_ext_ops())    # Load extensional operators
    operators.update(get_modal_ops())  # Load modal operators
    return operators
```

### Real Examples from Logos

See how the logos theory implements registration:

- [Modal operators registry](../../../Code/src/model_checker/theory_lib/logos/subtheories/modal/operators.py) (lines 155-167)
- [Extensional operators registry](../../../Code/src/model_checker/theory_lib/logos/subtheories/extensional/operators.py) (lines 313-325)
- [Main logos registry](../../../Code/src/model_checker/theory_lib/logos/operators.py) that coordinates subtheories

### Registration Best Practices

- **Consistent naming**: Use standard LaTeX commands for common operators
- **Complete export**: Include all operators defined in the module
- **Clear documentation**: Document what each operator does in comments
- **Logical grouping**: Group related operators together in the dictionary
- **Dependency awareness**: Ensure imported operators are available when needed

## Testing Custom Operators

After defining new operators:

1. **Create test cases** in `examples.py`:

```python
TEST_premises = ["(A \\otimes B)"]  # Your new operator
TEST_conclusions = ["C"]
TEST_settings = {
    'N': 3,
    'contingent': False,
    'max_time': 10,
    'iterate': 1,
    'expectation': True,  # True if expecting countermodel
}
```

2. **Run tests**:

```bash
model-checker examples.py
```

3. **Verify behavior** by checking:

- Countermodels match expected semantics
- Theorems validate correctly
- Edge cases are handled properly

## Best Practices

1. **Start with defined operators** when possible - they're easier to debug
2. **Document your operators** with clear explanations of their semantics
3. **Test incrementally** - add one operator at a time
4. **Use meaningful names** that reflect the operator's logical role
5. **Check existing theories** for similar operators you can adapt
6. **Always use LaTeX notation** - never use Unicode in code

## Common Patterns

### Modal-style Operators

```python
class WeakNecessityOperator(syntactic.DefinedOperator):
    """Weak necessity: necessarily A or necessarily not A."""

    name = "\\square"
    arity = 1

    def derived_definition(self, argument):
        # Define □A as (□A ∨ □¬A)
        return [OrOperator,
                [NecessityOperator, argument],
                [NecessityOperator, [NegationOperator, argument]]]
```

### Compound Operators

```python
class StrictEquivalenceOperator(syntactic.DefinedOperator):
    """Strict equivalence: necessarily biconditional."""

    name = "\\Leftrightarrow"
    arity = 2

    def derived_definition(self, leftarg, rightarg):
        # Define A ⇔ B as □((A → B) ∧ (B → A))
        biconditional = [AndOperator,
                        [ConditionalOperator, leftarg, rightarg],
                        [ConditionalOperator, rightarg, leftarg]]
        return [NecessityOperator, biconditional]
```

## Formula Formatting Rules

When using operators in formulas, follow these conventions:

1. **Binary operators** require outer parentheses:
   - Correct: `"(A \\wedge B)"`
   - Wrong: `"A \\wedge B"`

2. **Unary operators** must not have outer parentheses:
   - Correct: `"\\neg A"`
   - Wrong: `"(\\neg A)"`

3. **Nested formulas** follow the main operator rule at each level:
   - `"\\neg (A \\wedge B)"` - Negation of conjunction
   - `"(\\neg A \\vee \\neg B)"` - Disjunction of negations

## Troubleshooting

Common issues when defining operators:

1. **Import errors**: Ensure all operator classes you reference are properly imported
2. **Registry errors**: Check that your `get_operators()` function returns the correct dictionary
3. **LaTeX parsing errors**: Ensure you're using LaTeX notation (`\\wedge`, not `∧`) in operator names
4. **Class definition errors**: Verify operator classes inherit from correct base class (`syntactic.Operator` or `syntactic.DefinedOperator`)
5. **Method implementation errors**: For primitive operators, ensure all required methods are implemented
6. **Circular dependencies**: Review import statements and operator definitions for cycles
7. **Z3 constraint errors**: For primitive operators, verify constraint logic in `true_at()`, `false_at()` methods

### Debugging Tips

- Check the `get_operators()` function returns a proper dictionary mapping strings to classes
- Verify LaTeX operator names match exactly what you use in formulas
- For defined operators, ensure all referenced operators are available in scope
- For primitive operators, test each method (`true_at`, `false_at`, etc.) independently

### Architecture Reminders

- Operators are standalone classes, NOT methods in semantic classes
- The semantic.py file provides the framework, operators.py provides the implementations
- Always register new operators in the `get_operators()` function

For more details on semantic constraints, see the [Semantics Guide](SEMANTICS.md). For the underlying model theory and constraint architecture, see [Models Architecture](../architecture/MODELS.md).
