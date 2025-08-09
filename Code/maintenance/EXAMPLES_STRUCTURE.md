# Examples.py Structure Standards

[← Formula Formatting](FORMULA_FORMATTING.md) | [Back to Maintenance](README.md) | [Code Organization →](CODE_ORGANIZATION.md)

## Overview

This document defines the required structure for all `examples.py` files in the ModelChecker codebase. For comprehensive details and templates, see [docs/EXAMPLES.md](../docs/EXAMPLES.md).

## Example Naming Convention

All examples must follow the **PREFIX_TYPE_NUMBER** pattern:

- **PREFIX**: Theory abbreviation (2-3 characters)
- **TYPE**: CM (countermodel) or TH (theorem)
- **NUMBER**: Sequential number starting from 1

```python
EXT_TH_1_example    # Extensional theorem 1
LOG_CM_3_example    # Logos countermodel 3
IMP_TH_2_example    # Imposition theorem 2
BIM_CM_1_example    # Bimodal countermodel 1
```

## Theory Prefix Reference

| Theory          | Prefix | Description                 |
|-----------------|--------|-----------------------------|
| Extensional     | EXT    | Basic extensional logic     |
| Modal           | MOD    | Modal operators (□, ◇)      |
| Counterfactual  | CF     | Counterfactual conditionals |
| Constitutive    | CON    | Identity and essence        |
| Relevance       | REL    | Relevance logic             |
| Logos (general) | LOG    | Hyperintensional logic      |
| Exclusion       | EX     | Unilateral semantics        |
| Imposition      | IMP    | Fine's counterfactuals      |
| Bimodal         | BIM    | Temporal-modal logic        |

## Required File Components

Every examples.py file must include these components in order:

1. **Module Docstring** - Describes the examples and their categories
2. **Standard Imports** - System imports and path setup
3. **Theory Imports** - Theory-specific semantic components
4. **Theory Definition** - Semantic theory configuration
5. **Example Definitions** - Individual examples following naming convention
6. **Collections** - Organized countermodel_examples and theorem_examples
7. **Required Variables** - unit_tests, example_range, semantic_theories
8. **Main Block** - Makes the module executable

## Required Variables

```python
# Organize examples by category
countermodel_examples = {
    "PREFIX_CM_1": PREFIX_CM_1_example,
    # ... all countermodel examples
}

theorem_examples = {
    "PREFIX_TH_1": PREFIX_TH_1_example,
    # ... all theorem examples
}

# Combine for unit_tests (used by test framework)
unit_tests = {**countermodel_examples, **theorem_examples}

# Examples to execute when run directly
example_range = {
    "PREFIX_CM_1": PREFIX_CM_1_example,
    # ... selected examples to run
}

# Semantic theories to use
semantic_theories = {
    "theory_name": theory_definition,
}

# Optional execution settings
general_settings = {
    "print_constraints": False,
    "print_impossible": False,
    "print_z3": False,
    "save_output": False,
}
```

## Settings Documentation Requirements

Every example must include core settings with inline comments:

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

**Important**: All settings dictionaries MUST include inline comments. This requirement applies to documentation examples and actual code.

## Theory Loading with -l Flag

The `-l` flag creates new projects from theory templates:

```bash
model-checker -l logos      # Hyperintensional truthmaker semantics
model-checker -l exclusion  # Unilateral semantics  
model-checker -l imposition # Fine's counterfactual semantics
model-checker -l bimodal    # Combined temporal-modal logic
```

This creates a complete project structure with properly formatted examples.py, theory components, documentation, and tests.

---

[← Formula Formatting](FORMULA_FORMATTING.md) | [Back to Maintenance](README.md) | [Code Organization →](CODE_ORGANIZATION.md)