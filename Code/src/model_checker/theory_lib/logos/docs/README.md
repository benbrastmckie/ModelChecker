# Logos Theory Documentation Hub

[← Back to Logos](../README.md) | [API Reference →](API_REFERENCE.md) | [Architecture →](ARCHITECTURE.md)

## Directory Structure
```
docs/
├── README.md              # This file - documentation navigation hub
├── API_REFERENCE.md       # Comprehensive API documentation
├── ARCHITECTURE.md        # System design and implementation details
├── USER_GUIDE.md          # Practical usage guide for researchers
├── ITERATE.md             # Model iteration and difference features
└── SETTINGS.md            # Configuration parameters and defaults
```

## Overview

The **Logos Theory Documentation** provides comprehensive guides for understanding and using the hyperintensional truthmaker semantics framework. This documentation serves researchers using the theory, developers extending it, and users exploring its capabilities.

The documentation covers the **20+ logical operators** across 5 subtheories, **architectural patterns** for modular organization, **practical usage examples**, and **theoretical foundations** from Fine's truthmaker semantics and Brast-McKie's work on identity and aboutness.

Each document follows a specific purpose: API documentation for technical reference, architecture guide for system understanding, user guide for practical application, and specialized guides for iteration and settings management.

## Quick Reference

### Theory Loading
```python
from model_checker.theory_lib import logos

# Load complete theory
theory = logos.get_theory()

# Load specific subtheories
modal_theory = logos.get_theory(['modal'])
constitutive_theory = logos.get_theory(['constitutive'])
```

### Operator Categories
- **Extensional**: Basic truthmaker logic (¬, ∧, ∨, →, ↔)
- **Modal**: Necessity and possibility (□, ◇)
- **Constitutive**: Identity and grounding (≡, ≤, ⊑, ⪯, ⟹)
- **Counterfactual**: Conditional reasoning (⥽, ⥽◇)
- **Relevance**: Bilateral relevance (⤙, ⟷)

### Common Usage Pattern
```python
from model_checker.theory_lib import logos
from model_checker.theory_lib.logos import LogosSemantics, LogosProposition, LogosModelStructure
from model_checker.theory_lib.logos import LogosOperatorRegistry

# Load theory
logos_registry = LogosOperatorRegistry()
logos_registry.load_subtheories(['modal', 'constitutive'])

# Define example using standard format
TEST_TH_1_premises = ["\\Box (P \\rightarrow Q)"]
TEST_TH_1_conclusions = ["(\\Box P \\rightarrow \\Box Q)"]
TEST_TH_1_settings = {
    'N' : 4,                    # Number of atomic states
    'contingent' : False,       # Allow non-contingent propositions
    'non_null' : False,         # Allow null state
    'non_empty' : False,        # Allow empty verifier/falsifier sets
    'disjoint' : False,         # Allow overlapping verifier/falsifier sets
    'max_time' : 1,             # Solver timeout (seconds)
    'iterate' : 3,              # Number of models to find
    'expectation' : False,      # Expected result (False = no countermodel)
}
TEST_TH_1_example = [
    TEST_TH_1_premises,
    TEST_TH_1_conclusions,
    TEST_TH_1_settings,
]

# Collect examples
countermodel_examples = {
    # Add countermodel examples here
}

theorem_examples = {
    'TEST_TH_1': TEST_TH_1_example,
}

# Combine for unit_tests (used by test framework)
unit_tests = {**countermodel_examples, **theorem_examples}

# Define semantic theories
semantic_theories = {
    "Logos": {
        "semantics": LogosSemantics,
        "proposition": LogosProposition,
        "model": LogosModelStructure,
        "operators": logos_registry.get_operators(),
        "dictionary": {}  # No translation needed
    }
}

# Define which examples to run
example_range = {
    'TEST_TH_1': TEST_TH_1_example,
}

# General settings for output control
general_settings = {
    "print_constraints": False,
    "print_impossible": False,
    "print_z3": False,
    "save_output": False,
    "maximize": False,
}

# Make the module executable
if __name__ == "__main__":
    pass
```

### Interactive Exploration
```python
from model_checker import ModelExplorer
explorer = ModelExplorer(theory='logos')
explorer.display()
```

## API Reference

### Core Functions
- `logos.get_theory(subtheories=None)` - Load theory with specified subtheories
- `logos.get_operator_class(op_name)` - Get specific operator implementation
- `logos.list_operators(subtheory=None)` - List available operators

### Theory Structure
```python
theory = {
    "semantics": LogosSemantics,
    "proposition": LogosProposition,
    "model": LogosModelStructure,
    "operators": operator_registry,
    "dictionary": {}
}
```

## Documentation

### For New Users
- **[User Guide](USER_GUIDE.md)** - Practical introduction with examples
- **[Settings Guide](SETTINGS.md)** - Understanding configuration options
- **[Interactive Notebooks](../notebooks/README.md)** - Hands-on tutorials

### For Researchers  
- **[Architecture Guide](ARCHITECTURE.md)** - Theoretical foundations and design
- **[API Reference](API_REFERENCE.md)** - Complete technical documentation
- **[Iteration Features](ITERATE.md)** - Advanced model exploration

### For Developers
- **[Subtheory Architecture](ARCHITECTURE.md#subtheory-patterns)** - Extension patterns
- **[Operator Implementation](API_REFERENCE.md#operator-reference)** - Adding new operators
- **[Testing Guide](../tests/README.md)** - Comprehensive test patterns

## Core Concepts

### Truthmaker Semantics
- States verify or falsify propositions
- Hyperintensional: distinguishes necessarily equivalent propositions
- Modular: subtheories can be loaded independently

### Operator Types
1. **Primitive**: Directly implemented with Z3 constraints
2. **Defined**: Implemented using other operators
3. **Convenience**: Alternative notations for usability

### Architectural Principles
- **Modular Loading**: Load only needed subtheories
- **Registry Pattern**: Dynamic operator management
- **Extensibility**: Easy to add new operators and subtheories

## Related Resources

- **[Logos Theory Overview](../README.md)** - Main theory documentation
- **[Subtheory Documentation](../subtheories/README.md)** - Individual subtheory guides
- **[Test Suite](../tests/README.md)** - Validation and examples
- **[Theory Library](../../README.md)** - Cross-theory comparison

---

[← Back to Logos](../README.md) | [User Guide →](USER_GUIDE.md) | [API Reference →](API_REFERENCE.md)