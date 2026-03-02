# Writing Example Files for ModelChecker

[← Back to Usage](README.md) | [Workflow →](WORKFLOW.md) | [Output →](OUTPUT.md)

## Table of Contents

1. [Overview](#overview)
2. [Basic Example Structure](#basic-example-structure)
3. [Required Components](#required-components)
4. [Example Patterns](#example-patterns)
   - [Single Example](#single-example)
   - [Multiple Examples](#multiple-examples)
   - [Theory Comparison](#theory-comparison)
   - [Parametric Examples](#parametric-examples)
5. [Settings Configuration](#settings-configuration)
6. [Formula Syntax](#formula-syntax)
7. [Advanced Examples](#advanced-examples)
8. [Best Practices](#best-practices)
9. [Common Patterns](#common-patterns)
10. [Troubleshooting](#troubleshooting)

## Overview

Example files are Python modules that define logical formulas, settings, and theory configurations for the ModelChecker to process. They serve as the primary input format for testing logical inferences, exploring semantic theories, and validating philosophical arguments.

The examples.py structure serves as both **documentation and executable code**, demonstrating theory capabilities through carefully crafted logical formulas. These files are essential for validating semantic implementations, providing test cases, and offering practical usage examples for researchers and developers.

**Architecture Context**: For how example files are processed through the system, see [Pipeline Architecture](../architecture/PIPELINE.md) and [Builder Architecture](../architecture/BUILDER.md). For formula parsing details, see [Syntactic Architecture](../architecture/SYNTACTIC.md).

## Basic Example Structure

Every ModelChecker example file must export two dictionaries:

```python
# Minimal example file
from model_checker.theory_lib.logos import get_theory

# Get the semantic theory (loads all subtheories by default)
theory = get_theory()

# Or load specific subtheories for logos
# theory = get_theory(['modal', 'counterfactual'])  # Just modal and counterfactual
# theory = get_theory(['extensional'])  # Just extensional operators

# Define the example
MY_EXAMPLE_premises = ["A", "A \\rightarrow B"]
MY_EXAMPLE_conclusions = ["B"]
MY_EXAMPLE_settings = {'N': 3}
MY_EXAMPLE_example = [MY_EXAMPLE_premises, MY_EXAMPLE_conclusions, MY_EXAMPLE_settings]

# Required exports
example_range = {
    "MY_EXAMPLE": MY_EXAMPLE_example
}

semantic_theories = {
    "logos": theory
}
```

## Required Components

### 1. Theory Import and Initialization

```python
# Single theory
from model_checker.theory_lib.logos import get_theory
theory = get_theory()

# Multiple theories
from model_checker.theory_lib.logos import get_theory as get_logos
from model_checker.theory_lib.exclusion import get_theory as get_exclusion

logos_theory = get_logos()
exclusion_theory = get_exclusion()

# Theory with specific subtheories (logos)
from model_checker.theory_lib.logos import get_theory
theory = get_theory(['extensional', 'modal'])
```

### 2. Example Definition

Each example follows the **PREFIX_TYPE_NUMBER** naming convention:

```python
# PREFIX: Theory abbreviation (2-3 characters)
# TYPE: CM (countermodel) or TH (theorem)
# NUMBER: Sequential number starting from 1

# Standard examples:
EXT_TH_1_premises = [...]      # Extensional theorem 1
LOG_CM_3_premises = [...]      # Logos countermodel 3
IMP_TH_2_premises = [...]      # Imposition theorem 2

# Complete structure:
EXAMPLE_NAME_premises = [...]      # List of premise formulas
EXAMPLE_NAME_conclusions = [...]   # List of conclusion formulas  
EXAMPLE_NAME_settings = {...}      # Dictionary of settings
EXAMPLE_NAME_example = [           # Combined list
    EXAMPLE_NAME_premises,
    EXAMPLE_NAME_conclusions,
    EXAMPLE_NAME_settings
]
```

#### Standard Theory Prefixes

| Theory          | Prefix | Full Name                   |
| --------------- | ------ | --------------------------- |
| Extensional     | EXT    | Basic extensional logic     |
| Modal           | MOD    | Modal operators             |
| Counterfactual  | CF     | Counterfactual conditionals |
| Constitutive    | CON    | Identity and essence        |
| Relevance       | REL    | Relevance logic             |
| Logos (general) | LOG    | Hyperintensional logic      |
| Exclusion       | EX     | Unilateral semantics        |
| Imposition      | IMP    | Fine's counterfactuals      |
| Bimodal         | BIM    | Temporal-modal logic        |

### 3. Export Dictionaries

```python
# Map example names to example data
example_range = {
    "EXAMPLE_NAME": EXAMPLE_NAME_example,
    # Add more examples as needed
}

# Map theory names to theory objects
semantic_theories = {
    "theory_name": theory_object,
    # Add more theories for comparison
}
```

## Example Patterns

### Single Example

Basic pattern for testing one inference:

```python
from model_checker.theory_lib.logos import get_theory

theory = get_theory()

# Modus Ponens
MP_premises = ["P", "P \\rightarrow Q"]
MP_conclusions = ["Q"]
MP_settings = {'N': 3}
MP_example = [MP_premises, MP_conclusions, MP_settings]

example_range = {"MP": MP_example}
semantic_theories = {"logos": theory}
```

### Multiple Examples

Testing several inferences in one file:

```python
from model_checker.theory_lib.logos import get_theory

theory = get_theory(['extensional', 'modal'])

# Example 1: Conjunction Elimination
CONJ_ELIM_premises = ["A \\wedge B"]
CONJ_ELIM_conclusions = ["A", "B"]
CONJ_ELIM_settings = {'N': 3}
CONJ_ELIM_example = [CONJ_ELIM_premises, CONJ_ELIM_conclusions, CONJ_ELIM_settings]

# Example 2: Disjunction Introduction
DISJ_INTRO_premises = ["A"]
DISJ_INTRO_conclusions = ["A \\vee B"]
DISJ_INTRO_settings = {'N': 3}
DISJ_INTRO_example = [DISJ_INTRO_premises, DISJ_INTRO_conclusions, DISJ_INTRO_settings]

# Example 3: Modal Distribution
MODAL_DIST_premises = ["\\Box (A \\rightarrow B)", "\\Box A"]
MODAL_DIST_conclusions = ["\\Box B"]
MODAL_DIST_settings = {'N': 3}
MODAL_DIST_example = [MODAL_DIST_premises, MODAL_DIST_conclusions, MODAL_DIST_settings]

example_range = {
    "CONJ_ELIM": CONJ_ELIM_example,
    "DISJ_INTRO": DISJ_INTRO_example,
    "MODAL_DIST": MODAL_DIST_example
}

semantic_theories = {"logos_modal": theory}
```

### Theory Comparison

Compare how different theories handle the same inference:

```python
from model_checker.theory_lib.logos import get_theory as get_logos
from model_checker.theory_lib.exclusion import get_theory as get_exclusion
from model_checker.theory_lib.imposition import get_theory as get_imposition

# Initialize theories
logos = get_logos(['extensional'])
exclusion = get_exclusion()
imposition = get_imposition()

# Define test case
NEGATION_TEST_premises = ["\\neg \\neg A"]
NEGATION_TEST_conclusions = ["A"]
NEGATION_TEST_settings = {'N': 3}
NEGATION_TEST_example = [
    NEGATION_TEST_premises,
    NEGATION_TEST_conclusions,
    NEGATION_TEST_settings
]

# Export for comparison
example_range = {
    "DOUBLE_NEGATION": NEGATION_TEST_example
}

semantic_theories = {
    "Logos": logos,
    "Exclusion": exclusion,
    "Imposition": imposition
}
```

### Parametric Examples

Generate examples programmatically:

```python
from model_checker.theory_lib.logos import get_theory

theory = get_theory(['extensional', 'modal'])

# Generate chain of implications
def create_implication_chain(length):
    premises = []
    for i in range(length - 1):
        prop_from = chr(65 + i)  # A, B, C, ...
        prop_to = chr(65 + i + 1)
        premises.append(f"{prop_from} \\rightarrow {prop_to}")
    premises.append("A")  # Starting point
    
    conclusion = chr(65 + length - 1)  # Final proposition
    settings = {'N': length + 1}
    
    return [premises, [conclusion], settings]

# Create examples of different lengths
example_range = {}
for n in [3, 5, 7]:
    example_name = f"CHAIN_{n}"
    example_range[example_name] = create_implication_chain(n)

semantic_theories = {"logos": theory}
```

## Settings Configuration

### Core Settings

Every example must include these settings with descriptive comments:

```python
settings = {
    'N': 3,                    # Max number of atomic propositions
    'contingent': False,       # Allow non-contingent propositions
    'non_null': False,         # Allow the null state
    'non_empty': False,        # Allow empty verifier/falsifier sets
    'disjoint': False,         # Allow verifier/falsifier overlap
    'max_time': 10,            # Timeout in seconds
    'iterate': 1,              # Number of models to find
    'expectation': False,      # True = expect countermodel, False = expect theorem
}
```

**Important**: All settings dictionaries MUST include inline comments after each setting.

### Theory-Specific Settings

Some theories define additional settings:

```python
# Bimodal settings (temporal-modal logic)
'M': 2,                    # Number of time points/steps

# Exclusion settings (unilateral semantics)
'possible': False,         # Require possible propositions
'fusion_closure': False,   # Enforce fusion closure constraints

# Logos modal settings (when using modal subtheory)
'reflexive': True,        # Reflexive accessibility
'transitive': True,       # Transitive accessibility
'euclidean': False,       # Euclidean accessibility
```

### Setting Guidelines

1. **Always include 'expectation'**: Explicitly state whether expecting countermodel (True) or theorem (False)
2. **Use descriptive comments**: Every setting needs a brief explanation
3. **Order consistently**: Core settings first, theory-specific settings after
4. **Document constraints**: If settings interact, explain in comments

## Formula Syntax

### Basic Operators

```python
# Propositional operators
"\\neg A"                  # Negation
"A \\wedge B"             # Conjunction
"A \\vee B"               # Disjunction  
"A \\rightarrow B"        # Implication
"A \\leftrightarrow B"    # Biconditional

# Modal operators (requires modal subtheory)
"\\Box A"                 # Necessity
"\\Diamond A"             # Possibility

# Counterfactual operators (requires counterfactual subtheory)
"A \\boxright B"          # Counterfactual conditional
```

### Complex Formulas

```python
# Nested operators
"\\Box (A \\rightarrow B)"
"(A \\vee B) \\wedge \\neg C"
"\\Diamond (A \\wedge B) \\rightarrow \\Box C"

# Multiple premises/conclusions
premises = [
    "A \\rightarrow B",
    "B \\rightarrow C",
    "C \\rightarrow D"
]
conclusions = ["A \\rightarrow D"]
```

### Formula Formatting Standards

Binary operators require outer parentheses:

```python
# CORRECT - Outer parentheses required for binary operators
formulas = [
    "(A \\wedge B)",          # Conjunction
    "(A \\vee B)",            # Disjunction
    "(A \\rightarrow B)",     # Implication
    "(A \\leftrightarrow B)", # Biconditional
    "(A \\boxright B)",       # Counterfactual
]

# INCORRECT - Missing parentheses
formulas = [
    "A \\wedge B",            # Will cause parsing errors
    "A \\vee B",
]

# Unary operators do not need outer parentheses
"\\neg A"                     # Correct as-is
"\\Box A"                     # Correct as-is
"\\Diamond A"                 # Correct as-is
```

### Unicode Display (Explanatory Text Only)

Unicode symbols may appear in output or explanatory text:
- ¬ for NOT (use \\neg in code)
- ∧ for AND (use \\wedge in code)
- ∨ for OR (use \\vee in code)
- → for IMPLIES (use \\rightarrow in code)
- ↔ for IFF (use \\leftrightarrow in code)
- □ for NECESSARY (use \\Box in code)
- ◇ for POSSIBLE (use \\Diamond in code)

## Advanced Examples

### Testing Specific Semantic Properties

```python
# Test frame conditions
REFLEXIVITY_TEST_premises = []
REFLEXIVITY_TEST_conclusions = ["A \\rightarrow \\Box A"]
REFLEXIVITY_TEST_settings = {
    'N': 2,
    'reflexive': True  # Should make this valid
}

TRANSITIVITY_TEST_premises = ["\\Box A"]
TRANSITIVITY_TEST_conclusions = ["\\Box \\Box A"]
TRANSITIVITY_TEST_settings = {
    'N': 2,
    'transitive': True  # Should make this valid
}
```

### Countermodel Generation

```python
# Intentionally invalid for countermodel analysis
INVALID_premises = ["A \\vee B"]
INVALID_conclusions = ["A", "B"]  # Can't derive both
INVALID_settings = {
    'N': 3,
    'find_countermodel': True,
    'verbose': True  # Show countermodel details
}
```

### Performance Testing

```python
# Large-scale example
PERFORMANCE_premises = [f"P{i} \\rightarrow P{i+1}" for i in range(10)]
PERFORMANCE_premises.append("P0")
PERFORMANCE_conclusions = ["P10"]
PERFORMANCE_settings = {
    'N': 12,
    'max_time': 60,
    'optimize': True
}
```

## Best Practices

### 1. Naming Conventions

```python
# Use descriptive uppercase names
MODUS_PONENS_example = [...]          # Clear
MP_example = [...]                     # Acceptable abbreviation
test1_example = [...]                  # Avoid generic names
```

### 2. Documentation

```python
"""
Example file for testing classical propositional logic.
Theory: Logos (extensional subtheory)
Author: Your Name
Date: 2024-01-15
"""

# Document complex examples
# Test case: Verify distributivity of ∧ over ∨
DISTRIBUTIVITY_premises = ["A \\wedge (B \\vee C)"]
DISTRIBUTIVITY_conclusions = ["(A \\wedge B) \\vee (A \\wedge C)"]
```

### 3. Organization

```python
# Group related examples
# === Conjunction Tests ===
CONJ_INTRO_example = [...]
CONJ_ELIM_L_example = [...]
CONJ_ELIM_R_example = [...]

# === Disjunction Tests ===
DISJ_INTRO_L_example = [...]
DISJ_INTRO_R_example = [...]
DISJ_ELIM_example = [...]
```

### 4. Settings Management

```python
# Define reusable settings
BASE_SETTINGS = {'N': 3, 'max_time': 30}

# Extend for specific tests
MODAL_SETTINGS = {**BASE_SETTINGS, 'reflexive': True}
PERFORMANCE_SETTINGS = {**BASE_SETTINGS, 'N': 10, 'max_time': 120}
```

## Common Patterns

### Classical Logic Tests

```python
# Standard logical laws
EXCLUDED_MIDDLE_premises = []
EXCLUDED_MIDDLE_conclusions = ["A \\vee \\neg A"]

CONTRADICTION_premises = ["A", "\\neg A"]
CONTRADICTION_conclusions = ["B"]  # Ex falso

DEMORGAN_1_premises = ["\\neg (A \\wedge B)"]
DEMORGAN_1_conclusions = ["\\neg A \\vee \\neg B"]
```

### Modal Logic Tests

```python
# Modal axioms
K_AXIOM_premises = ["\\Box (A \\rightarrow B)", "\\Box A"]
K_AXIOM_conclusions = ["\\Box B"]

T_AXIOM_premises = ["\\Box A"]
T_AXIOM_conclusions = ["A"]

S4_AXIOM_premises = ["\\Box A"]
S4_AXIOM_conclusions = ["\\Box \\Box A"]
```

### Inference Patterns

```python
# Common inference rules
HYPOTHETICAL_SYLLOGISM_premises = ["A \\rightarrow B", "B \\rightarrow C"]
HYPOTHETICAL_SYLLOGISM_conclusions = ["A \\rightarrow C"]

DISJUNCTIVE_SYLLOGISM_premises = ["A \\vee B", "\\neg A"]
DISJUNCTIVE_SYLLOGISM_conclusions = ["B"]

CONSTRUCTIVE_DILEMMA_premises = [
    "A \\rightarrow B",
    "C \\rightarrow D",
    "A \\vee C"
]
CONSTRUCTIVE_DILEMMA_conclusions = ["B \\vee D"]
```

## Troubleshooting

### Example Output:

When running counterfactual examples, the output shows detailed semantic evaluations:

```
========================================

EXAMPLE CF_CM_1: there is a countermodel.

Atomic States: 4
Semantic Theory: Brast-McKie

Premises:
1. \neg A
2. (A \boxright C)

Conclusion:
3. ((A \wedge B) \boxright C)

Z3 Run Time: 0.0341 seconds

========================================

State Space:
  #b0101 = a.c (world)
  #b0110 = b.c (world)
  #b1001 = a.d (world)

The evaluation world is: b.c

INTERPRETED PREMISES:

1. |\neg A| = < {b.c}, {a, a.b.c.d} >  (True in b.c)
    |A| = < {a, a.b.c.d}, {b.c} >  (False in b.c)

2. |(A \boxright C)| = < {a.c, b.c}, {a.d} >  (True in b.c)
    |A|-alternatives to b.c = {a.c}
    |C| = < {a.c}, {a.b.c.d, a.b.d, a.d, b} >  (True in a.c)

INTERPRETED CONCLUSION:

3. |((A \wedge B) \boxright C)| = < {}, {a.c, a.d, b.c} >  (False in b.c)
    |(A \wedge B)|-alternatives to b.c = {a.d}
    |C| = < {a.c}, {a.b.c.d, a.b.d, a.d, b} >  (False in a.d)

Total Run Time: 0.389 seconds
========================================
```

This output demonstrates:
- **Countermodel Found**: Shows the argument is invalid
- **State Space**: Lists possible worlds and their properties
- **Evaluation World**: The world where the countermodel exists
- **Interpreted Formulas**: Shows verifiers/falsifiers for each premise and conclusion
- **Counterfactual Alternatives**: Displays the nearest possible worlds for counterfactual evaluation

### Common Errors and Solutions

**Error**: `NameError: name 'example_range' is not defined`
```python
# Solution: Ensure you export both required dictionaries
example_range = {"EXAMPLE": example_data}
semantic_theories = {"theory": theory_object}
```

**Error**: `Invalid operator: \implies`
```python
# Solution: Use correct LaTeX commands
# Wrong: "\implies", "\land", "\lor"
# Right: "\rightarrow", "\wedge", "\vee"
```

**Error**: `Settings key 'N' not found`
```python
# Solution: Always include required settings
settings = {
    'N': 3  # Required: maximum atomic propositions
    # Other settings are optional
}
```

**Error**: Theory not loading
```python
# Solution: Check import and initialization
from model_checker.theory_lib.logos import get_theory
theory = get_theory()  # Don't forget parentheses
```

### Debugging Tips

1. **Start simple**: Test with basic formulas first
2. **Use verbose mode**: Add `'verbose': True` to settings
3. **Print constraints**: Add `'print_constraints': True`
4. **Reduce N**: Start with `'N': 2` or `'N': 3`
5. **Check syntax**: Validate LaTeX commands and escaping

## See Also

### Usage Guides
- [Workflow Guide](WORKFLOW.md) - Running examples
- [Settings Guide](SETTINGS.md) - Configuring examples
- [Output Guide](OUTPUT.md) - Saving and formatting results
- [ModelChecker Tools](TOOLS.md) - Advanced features and multi-theory examples
- [Constraints Testing](SEMANTICS.md) - Advanced testing techniques

### Architecture Documentation
- [Syntactic Processing](../architecture/SYNTACTIC.md) - How formulas are parsed and AST is constructed
- [Builder Architecture](../architecture/BUILDER.md) - How examples are orchestrated and executed
- [Pipeline Overview](../architecture/PIPELINE.md) - Complete data flow from examples to outputs
- [Settings Architecture](../architecture/SETTINGS.md) - How example settings are processed
- [Models Architecture](../architecture/MODELS.md) - How examples generate semantic models

---

[← Back to Usage](README.md) | [Workflow →](WORKFLOW.md) | [Output →](OUTPUT.md)