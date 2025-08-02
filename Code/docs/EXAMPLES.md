# Examples.py Standard Form Documentation

[← Back to Docs](README.md) | [Maintenance Standards →](../maintenance/README.md) | [Development Guide →](../../Docs/DEVELOPMENT.md)

## Table of Contents

1. [Overview](#overview)
2. [Naming Conventions](#naming-conventions)
3. [Required Structure](#required-structure)
4. [Variable Definitions](#variable-definitions)
5. [Settings Documentation](#settings-documentation)
6. [Formula Formatting](#formula-formatting)
7. [Complete Template](#complete-template)
8. [Theory-Specific Considerations](#theory-specific-considerations)
9. [Validation Checklist](#validation-checklist)

## Overview

This document establishes the **standard form for examples.py files** throughout the ModelChecker framework, ensuring consistency, maintainability, and compatibility across all theory implementations. Every examples.py file must follow these standards to integrate properly with the testing framework and command-line interface.

The examples.py structure serves as both **documentation and executable code**, demonstrating theory capabilities through carefully crafted logical formulas. These files are essential for validating semantic implementations, providing test cases, and offering practical usage examples for researchers and developers.

All examples.py files must adhere to the **[formula formatting standards](../maintenance/FORMULA_FORMATTING.md)**, using capital letters for propositions, proper parentheses for operators, and LaTeX notation throughout. The standardized structure ensures automated testing, theory comparison, and consistent user experience across the framework.

## Naming Conventions

### Example Naming Pattern

All examples must follow the **PREFIX_TYPE_NUMBER** naming convention:

```python
# PREFIX: Theory abbreviation (2-3 characters)
# TYPE: CM (countermodel) or TH (theorem)
# NUMBER: Sequential number starting from 1

# Correct examples:
EXT_TH_1_example    # Extensional theorem 1
LOG_CM_3_example    # Logos countermodel 3
IMP_TH_2_example    # Imposition theorem 2
BIM_CM_1_example    # Bimodal countermodel 1
```

### Standard Theory Prefixes

| Theory          | Prefix | Full Name                   |
| --------------- | ------ | --------------------------- |
| Extensional     | EXT    | Basic extensional logic     |
| Modal           | MOD    | Modal operators (□, ◇)      |
| Counterfactual  | CF     | Counterfactual conditionals |
| Constitutive    | CON    | Identity and essence        |
| Relevance       | REL    | Relevance logic             |
| Logos (general) | LOG    | Hyperintensional logic      |
| Exclusion       | EX     | Unilateral semantics        |
| Imposition      | IMP    | Fine's counterfactuals      |
| Bimodal         | BIM    | Temporal-modal logic        |

### Variable Naming Requirements

```python
# Each example requires four variables:
PREFIX_TYPE_NUMBER_premises = [...]      # List of premise formulas
PREFIX_TYPE_NUMBER_conclusions = [...]   # List of conclusion formulas
PREFIX_TYPE_NUMBER_settings = {...}      # Dictionary of settings
PREFIX_TYPE_NUMBER_example = [...]       # Combined list
```

## Required Structure

Every examples.py file must include these components in order:

### 1. Module Docstring

```python
"""
[Theory Name] Examples

This module provides example formulas demonstrating [theory description].
Examples are organized into countermodels (showing invalidity) and
theorems (showing validity).

Example Categories:
------------------
1. [Theory] Countermodels (PREFIX_CM_*):
   - Brief description of countermodel types
   - Key invalidity patterns demonstrated

2. [Theory] Theorems (PREFIX_TH_*):
   - Brief description of theorem types
   - Key validity patterns demonstrated

Usage:
------
Run directly with model-checker or dev_cli.py:
model-checker path/to/examples.py
./dev_cli.py path/to/examples.py
"""
```

### 2. Standard Imports

```python
# Standard imports
import os
import sys

# Add current directory to path for imports
current_dir = os.path.dirname(os.path.abspath(__file__))
if current_dir not in sys.path:
    sys.path.insert(0, current_dir)
```

### 3. Theory Imports

```python
# Import theory components
from .semantic import TheorySemantics, TheoryProposition, TheoryStructure
from .operators import theory_operators  # or get_operators()

# For theories using shared components:
from . import Proposition, ModelStructure  # Imported via __init__.py
```

### 4. Theory Definition

```python
# Theory definition
theory_name = {
    "semantics": TheorySemantics,
    "proposition": TheoryProposition,
    "model": TheoryStructure,
    "operators": theory_operators,
    "dictionary": {}  # Translation dictionary if needed
}
```

### 5. Example Definitions

```python
# Individual example definitions following naming convention
PREFIX_TYPE_NUMBER_premises = ["A", "(A \\rightarrow B)"]
PREFIX_TYPE_NUMBER_conclusions = ["B"]
PREFIX_TYPE_NUMBER_settings = {
    'N': 3,                    # Max number of atomic propositions
    'contingent': False,       # Allow non-contingent propositions
    'non_null': False,         # Allow the null state
    'non_empty': False,        # Allow empty verifier/falsifier sets
    'disjoint': False,         # Allow verifier/falsifier overlap
    'max_time': 10,            # Timeout in seconds
    'iterate': 1,              # Number of models to find
    'expectation': False,      # True = expect countermodel, False = expect theorem
}
PREFIX_TYPE_NUMBER_example = [
    PREFIX_TYPE_NUMBER_premises,
    PREFIX_TYPE_NUMBER_conclusions,
    PREFIX_TYPE_NUMBER_settings,
]
```

### 6. Collections

```python
# Organize examples by category
countermodel_examples = {
    "PREFIX_CM_1": PREFIX_CM_1_example,
    "PREFIX_CM_2": PREFIX_CM_2_example,
    # ... all countermodel examples
}

theorem_examples = {
    "PREFIX_TH_1": PREFIX_TH_1_example,
    "PREFIX_TH_2": PREFIX_TH_2_example,
    # ... all theorem examples
}

# Combine for unit_tests (used by test framework)
unit_tests = {**countermodel_examples, **theorem_examples}

# The framework expects this to be named 'example_range'
example_range = {
    "PREFIX_CM_1": PREFIX_CM_1_example,  # Run specific examples
}

# Optional: General settings for execution
general_settings = {
    "print_constraints": False,
    "print_impossible": False,
    "print_z3": False,
    "save_output": False,
    "maximize": False,  # Set to True to compare multiple theories
}

# Define semantic theories to use
semantic_theories = {
    "theory_name": theory_name,
    # Additional theories for comparison
}
```

### 7. Main Block

```python
# Make module executable
if __name__ == '__main__':
    import subprocess
    file_name = os.path.basename(__file__)
    subprocess.run(["model-checker", file_name], check=True, cwd=current_dir)
```

## Variable Definitions

### Required Variables

Every examples.py file must define these variables in this order:

1. **unit_tests** (Required)

   - Dictionary mapping example names to example definitions
   - Used by the test framework for validation
   - Must include ALL examples defined in the file

2. **example_range** (Required)

   - Dictionary of examples to execute when file is run
   - Can be a subset of unit_tests or equal to unit_tests
   - Controls which examples run by default

3. **general_settings** (Optional but Recommended)

   - Controls output formatting and debugging
   - Standard keys: print_constraints, print_impossible, print_z3, save_output, maximize

4. **semantic_theories** (Required)
   - Dictionary mapping theory names to theory definitions
   - Can include multiple theories for comparison
   - Keys become column headers in output


## Settings Documentation

### Core Settings

Every example must include these settings with descriptive comments after each setting:

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

**Important**: All settings dictionaries MUST include inline comments after each setting. This provides crucial context for understanding what each setting controls and how it affects the model checking process.

### Theory-Specific Settings

Some theories define additional settings beyond the core settings:

```python
# Bimodal settings (temporal-modal logic)
'M': 2,                    # Number of time points/steps

# Exclusion settings (unilateral semantics)
'possible': False,         # Require possible propositions
'fusion_closure': False,   # Enforce fusion closure constraints

# Logos settings (all subtheories use same core settings)
# No theory-specific settings - uses standard N, contingent, non_null, etc.

# Imposition settings
# No theory-specific settings - uses standard settings
```

### Setting Guidelines

1. **Always include 'expectation'**: Explicitly state whether expecting countermodel (True) or theorem (False)
2. **Use descriptive comments**: Every setting needs a brief explanation
3. **Order consistently**: Core settings first, theory-specific settings after
4. **Document constraints**: If settings interact, explain in comments

## Formula Formatting

### Binary Operators

```python
# CORRECT - Outer parentheses required
formulas = [
    "(A \\wedge B)",          # Conjunction
    "(A \\vee B)",            # Disjunction
    "(A \\rightarrow B)",     # Implication
    "(A \\leftrightarrow B)", # Biconditional
    "(A \\boxright B)",       # Counterfactual
]

# INCORRECT - Missing parentheses
formula = "A \\rightarrow B"  # WRONG
```

### Unary Operators

```python
# CORRECT - No outer parentheses
formulas = [
    "\\neg A",        # Negation
    "\\Box A",        # Necessity
    "\\Diamond A",    # Possibility
]

# INCORRECT - Unnecessary parentheses
formula = "(\\neg A)"  # WRONG
```

### Complex Formulas

```python
# CORRECT - Proper nesting
formulas = [
    "\\neg (A \\wedge B)",                    # Negation of conjunction
    "(\\neg A \\vee \\neg B)",                # Disjunction of negations
    "\\Box (A \\rightarrow B)",               # Box around implication
    "(\\Box A \\rightarrow \\Box B)",         # Implication of boxes
]
```

## Complete Template

```python
"""
[Theory Name] Examples

This module provides example formulas demonstrating [detailed theory description].
Examples are organized into countermodels (showing invalidity) and theorems (showing validity).

Example Categories:
------------------
1. [Theory] Countermodels (PREFIX_CM_*):
   - Description of countermodel patterns
   - Key invalidities demonstrated

2. [Theory] Theorems (PREFIX_TH_*):
   - Description of theorem patterns
   - Key validities demonstrated

Usage:
------
Run directly with model-checker or dev_cli.py:
model-checker path/to/examples.py
./dev_cli.py path/to/examples.py
"""

# Standard imports
import os
import sys

# Add current directory to path for imports
current_dir = os.path.dirname(os.path.abspath(__file__))
if current_dir not in sys.path:
    sys.path.insert(0, current_dir)

# Import theory components
from .semantic import TheorySemantics, TheoryProposition, TheoryStructure
from .operators import theory_operators

# Theory definition
theory_name = {
    "semantics": TheorySemantics,
    "proposition": TheoryProposition,
    "model": TheoryStructure,
    "operators": theory_operators,
    "dictionary": {}
}

# ===== COUNTERMODEL EXAMPLES =====

# Example 1: Description of what this tests
PREFIX_CM_1_premises = ["A", "(A \\rightarrow B)"]
PREFIX_CM_1_conclusions = ["\\Box B"]
PREFIX_CM_1_settings = {
    'N': 3,                    # Max number of atomic propositions
    'contingent': False,       # Allow non-contingent propositions
    'non_null': False,         # Allow the null state
    'non_empty': False,        # Allow empty verifier/falsifier sets
    'disjoint': False,         # Allow verifier/falsifier overlap
    'max_time': 10,            # Timeout in seconds
    'iterate': 1,              # Number of models to find
    'expectation': True,       # True = expect countermodel, False = expect theorem
}
PREFIX_CM_1_example = [
    PREFIX_CM_1_premises,
    PREFIX_CM_1_conclusions,
    PREFIX_CM_1_settings,
]

# ===== THEOREM EXAMPLES =====

# Example 2: Description of what this validates
PREFIX_TH_1_premises = ["A", "(A \\rightarrow B)"]
PREFIX_TH_1_conclusions = ["B"]
PREFIX_TH_1_settings = {
    'N': 3,                    # Max number of atomic propositions
    'contingent': False,       # Allow non-contingent propositions
    'non_null': False,         # Allow the null state
    'non_empty': False,        # Allow empty verifier/falsifier sets
    'disjoint': False,         # Allow verifier/falsifier overlap
    'max_time': 10,            # Timeout in seconds
    'iterate': 1,              # Number of models to find
    'expectation': False,      # True = expect countermodel, False = expect theorem
}
PREFIX_TH_1_example = [
    PREFIX_TH_1_premises,
    PREFIX_TH_1_conclusions,
    PREFIX_TH_1_settings,
]

# ===== COLLECTIONS =====

# Organize examples by category
countermodel_examples = {
    "PREFIX_CM_1": PREFIX_CM_1_example,
}

theorem_examples = {
    "PREFIX_TH_1": PREFIX_TH_1_example,
}

# Combine for unit_tests (used by test framework)
unit_tests = {**countermodel_examples, **theorem_examples}

# The framework expects this to be named 'example_range'
example_range = {
    "PREFIX_CM_1": PREFIX_CM_1_example,
    "PREFIX_TH_1": PREFIX_TH_1_example,
}

# Optional: General settings for execution
general_settings = {
    "print_constraints": False,
    "print_impossible": False,
    "print_z3": False,
    "save_output": False,
    "maximize": False,  # Set to True to compare multiple theories
}

# Define semantic theories to use
semantic_theories = {
    "theory_name": theory_name,
}

# Make module executable
if __name__ == '__main__':
    import subprocess
    file_name = os.path.basename(__file__)
    subprocess.run(["model-checker", file_name], check=True, cwd=current_dir)
```

## Theory-Specific Considerations

### Logos Theory

Logos examples often span multiple subtheories:

```python
# Import registry for operator management
from model_checker.theory_lib.logos import LogosOperatorRegistry

# Create registry and load subtheories
registry = LogosOperatorRegistry()
registry.load_subtheories(['extensional', 'modal', 'counterfactual'])

# Use in theory definition
logos_theory = {
    "semantics": LogosSemantics,
    "proposition": LogosProposition,
    "model": LogosModelStructure,
    "operators": registry.get_operators(),
    "dictionary": {}
}
```

### Theory Comparison

For cross-theory comparison examples:

```python
# Import multiple theories
from model_checker.theory_lib import logos, imposition

# Load only the counterfactual subtheory of Logos for focused comparison
logos_cf_theory = logos.get_theory(['counterfactual'])
imposition_theory = imposition.get_theory()

# Define theories with translation dictionaries
semantic_theories = {
    "Logos-CF": logos_cf_theory,
    "Imposition": imposition_theory,
}

# Use general_settings to control comparison
general_settings = {
    "maximize": True,  # Compare maximum N each theory can handle
}
```

For comprehensive guidance on theory comparison, import patterns, avoiding circular dependencies, and advanced multi-theory setups, see **[Theory Comparison Guide](../../Docs/COMPARE_THEORIES.md)**.

## Validation Checklist

Before committing an examples.py file, verify:

### Structure Compliance

- [ ] Module docstring follows template format
- [ ] All required imports in correct order
- [ ] Theory definition includes all required keys
- [ ] Variables defined in correct order: unit_tests, example_range, general_settings, semantic_theories
- [ ] Main block included for executable support

### Naming Compliance

- [ ] All examples follow PREFIX_TYPE_NUMBER pattern
- [ ] Prefixes match theory abbreviations
- [ ] Type indicates whether the example is a theorem or countermodel
- [ ] Sequential numbering without gaps
- [ ] Variable names match pattern exactly

### Formula Compliance

- [ ] Binary operators have outer parentheses
- [ ] Unary operators have no outer parentheses
- [ ] LaTeX notation used throughout
- [ ] Only use Unicode only in comments

### Settings Compliance

- [ ] All core settings included with comments
- [ ] The 'expectation' explicitly set for each example
- [ ] Theory-specific settings documented
- [ ] Comments explain each setting's purpose

### Testing Compliance

- [ ] Include well-studied examples in `unit_tests`
- [ ] The `example_range` is defined with variable names
- [ ] File runs successfully with model-checker
- [ ] Examples produce expected results

### Documentation Compliance

- [ ] Descriptive comments for each example
- [ ] Clear categorization of countermodels vs theorems
- [ ] Usage instructions included
- [ ] No emojis anywhere in file

---

[← Back to Docs](README.md) | [Theory Library →](../src/model_checker/theory_lib/README.md) | [Development Guide →](../../Docs/DEVELOPMENT.md)
