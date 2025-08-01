# Subtheory Name Subtheory: Descriptive Tagline

[← Back to Subtheories](../README.md) | [Tests →](tests/README.md) | [Examples →](examples.py)

## Directory Structure

```
subtheory_name/
├── README.md               # This file - subtheory overview
├── __init__.py            # Subtheory initialization
├── operators.py           # Operator definitions
├── examples.py            # Example formulas
├── tests/                 # Test suite (see tests/README.md)
└── notebooks/             # Interactive tutorials (see notebooks/README.md)
```

## Overview

The **Subtheory Name** subtheory implements hyperintensional semantics for [operator types]. All operators follow hyperintensional truthmaker semantics based on verifier and falsifier sets, allowing fine-grained distinctions between propositional contents that goes beyond extensional equivalence or necessary equivalence.

Within the parent theory framework, this subtheory provides [specific role and capabilities]. It integrates with [other subtheories] through [integration mechanism]. The subtheory includes [X primitive operators] and [Y defined operators] supporting [key logical features].

## Theory Examples

### Theory-Specific Imports

```python
from model_checker.theory_lib.parent_theory import ParentOperatorRegistry

# Create registry and load this subtheory
registry = ParentOperatorRegistry()
registry.load_subtheories(['subtheory_name'])
operators = registry.get_operators()
```

### Example: [Descriptive Name]

```python
# Example demonstrating key operator
SUBTH_TH_1_premises = ['\\operator A']
SUBTH_TH_1_conclusions = ['A']
SUBTH_TH_1_settings = {
    'N': 3,                    # Number of atomic propositions
    'subtheory_setting': True, # Subtheory-specific setting
    'expectation': False,      # False = expect theorem
}
```

### Running Examples

```bash
# Run subtheory examples
model-checker src/model_checker/theory_lib/parent_theory/subtheories/subtheory_name/examples.py
```

For complete examples.py file structure, see [Examples Standards](../../../maintenance/EXAMPLES_STRUCTURE.md).

## Subdirectories

### [tests/](tests/)
Comprehensive test coverage for operator implementations and semantic behavior. Validates both individual operators and integration with parent theory. See [tests/README.md](tests/README.md) for details.

### [notebooks/](notebooks/)
Interactive demonstrations of subtheory concepts and operator usage. Includes progressive tutorials from basic to advanced applications. See [notebooks/README.md](notebooks/README.md) for navigation.

## Documentation

### For New Users
- **[Parent Theory Guide](../../docs/USER_GUIDE.md)** - Introduction to the full theory
- **[Interactive Notebooks](notebooks/README.md)** - Hands-on subtheory tutorials
- **[Operator Examples](#operator-reference)** - Usage examples below

### For Researchers
- **[Theoretical Background](#semantic-theory)** - Formal foundations
- **[Test Cases](examples.py)** - Validation examples
- **[Integration Guide](#integration)** - Cross-subtheory interaction

### For Developers
- **[Operator Implementation](operators.py)** - Source code
- **[Parent Theory API](../../docs/API_REFERENCE.md)** - Full API reference
- **[Testing Guide](tests/README.md)** - Test methodology

## Operator Reference

This subtheory provides [X operators] for [purpose]:

### Primitive Operators ([number])

#### Operator Name
- **Symbol**: `\\command` (displayed as ◯)
- **Name**: Official Operator Name
- **Arity**: 1 or 2
- **Type**: Primitive operator

**Meaning**: One-line informal description of what the operator does.

**Truth Conditions**: 
Informally, the operator is true when [condition]. 

Z3 Implementation:
```python
def operator_verify(model, formula):
    # Actual implementation from operators.py
    return verification_condition
```

**Usage Examples**:
```python
# Basic usage
formula1 = "\\operator A"

# Complex usage
formula2 = "(\\operator A \\wedge B)"
```

**Key Properties**:
- Property 1: `A ⊢ ◯A` (description)
- Property 2: `◯A ∧ ◯B ⊢ ◯(A ∧ B)` (description)

### Defined Operators ([number])

#### Defined Operator Name
- **Symbol**: `\\defcommand` (displayed as ◈)
- **Name**: Official Name
- **Arity**: 1 or 2
- **Type**: Defined operator

**Meaning**: One-line description.

**Definition**: `◈A := primitive expression using A`

**Usage Examples**:
```python
# Show how defined operator relates to primitives
formula = "\\defcommand A"  # Equivalent to primitive expression
```

## Examples

The subtheory includes [total number] examples demonstrating [what they demonstrate]:

### Countermodels ([number])
Examples showing invalid inferences:
- `SUBTH_CM_1` through `SUBTH_CM_N`: [What these test]

### Theorems ([number])
Examples showing valid principles:
- `SUBTH_TH_1` through `SUBTH_TH_N`: [What these validate]

### Running Examples

```python
from model_checker.theory_lib.parent_theory.subtheories.subtheory_name.examples import unit_tests

# Run specific example
example = unit_tests['SUBTH_TH_1']
premises, conclusions, settings = example
```

## Semantic Theory

[Explanation of the formal semantic framework specific to this subtheory]

### Key Innovations
- [What makes this subtheory's approach unique]
- [Important theoretical contributions]

### Formal Properties
- [Key logical properties that hold]
- [Important limitations or non-properties]

## Integration

### Dependencies
This subtheory depends on:
- **[Other Subtheory](../other/)**: For [what functionality]

### Used By
The following subtheories depend on this one:
- **[Dependent Subtheory](../dependent/)**: Uses [which operators]

### Cross-Subtheory Examples
```python
# Example combining with other subtheory
registry.load_subtheories(['subtheory_name', 'other_subtheory'])
```

## References

### Primary Sources
- Author (Year) ["Subtheory Paper"](link). *Journal*.

### Related Resources
- **[Parent Theory Overview](../../README.md)** - Full theory documentation
- **[Subtheory Index](../README.md)** - All subtheories
- **[Related Subtheory](../related/)** - [How they connect]

---

[← Back to Subtheories](../README.md) | [Tests →](tests/README.md) | [Examples →](examples.py)