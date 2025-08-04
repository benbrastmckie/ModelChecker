# Logos Subtheories: Modular Hyperintensional Logic

[← Back to Logos Theory](../README.md) | [Extensional →](extensional/README.md) | [Modal →](modal/README.md)

## Directory Structure
```
subtheories/
├── README.md                # This file - subtheory coordination
├── __init__.py             # Public API for subtheory loading
├── extensional/            # Extensional operators (7 operators)
│   ├── README.md          # Extensional documentation
│   ├── __init__.py        # Public API exports
│   ├── operators.py       # Operator implementations
│   ├── examples.py        # Test examples (32 examples)
│   └── tests/             # Test suite
├── modal/                  # Necessity and possibility (4 operators)
│   ├── README.md          # Modal documentation
│   ├── __init__.py        # Public API exports
│   ├── operators.py       # Operator implementations
│   ├── examples.py        # Test examples (21 examples)
│   └── tests/             # Test suite
├── constitutive/           # Content relationships (5 operators)
│   ├── README.md          # Constitutive documentation
│   ├── __init__.py        # Public API exports
│   ├── operators.py       # Operator implementations
│   ├── examples.py        # Test examples (33 examples)
│   └── tests/             # Test suite
├── counterfactual/         # Counterfactual reasoning (2 operators)
│   ├── README.md          # Counterfactual documentation
│   ├── __init__.py        # Public API exports
│   ├── operators.py       # Operator implementations
│   ├── examples.py        # Test examples (2 examples)
│   └── tests/             # Test suite
└── relevance/              # Content-sensitive relevance (1 operator)
    ├── README.md          # Relevance documentation
    ├── __init__.py        # Public API exports
    ├── operators.py       # Operator implementations
    ├── examples.py        # Test examples (3 examples)
    └── tests/             # Test suite
```

## Overview

The **Logos Subtheories** implement a modular approach to hyperintensional logic, organizing 19 logical operators into 5 domain-specific modules. This architecture enables selective loading of logical capabilities, clean separation of concerns, and efficient memory usage while maintaining semantic coherence across all operators.

Each subtheory provides a self-contained logical system with its own operators, examples, and tests. Subtheories automatically resolve dependencies—requesting modal logic includes extensional operators, while relevance logic brings in the full constitutive framework. This modular design supports both theoretical exploration and practical applications.

The subtheory system exemplifies the Logos framework's commitment to **hyperintensional semantics**, where even necessarily equivalent formulas can have different content. By organizing operators into coherent modules, researchers can focus on specific logical phenomena while maintaining access to the full power of truthmaker semantics when needed.


## Subdirectories

### [extensional/](extensional/)
Foundation of extensional logic with 7 operators (¬, ∧, ∨, →, ↔, ⊤, ⊥). Implements bilateral truthmaker semantics where even basic operators distinguish content. Includes 32 comprehensive examples testing logical principles. Required by all other subtheories. See [extensional/README.md](extensional/README.md) for operator details.

### [modal/](modal/) 
Hyperintensional modal logic with 4 operators (□, ◇, CFBox, CFDiamond). Goes beyond S5 semantics to distinguish necessarily equivalent modal formulas. Includes 21 examples exploring modal axioms and hyperintensional phenomena. Depends on extensional subtheory. See [modal/README.md](modal/README.md) for modal semantics.

### [constitutive/](constitutive/)
Content relationship operators with 5 operators (≡, ≤, ⊑, ⪯, ⇒) for identity, ground, essence, relevance, and reduction. Enables fine-grained analysis of propositional content and dependencies. Includes 33 examples validating hyperintensional principles. See [constitutive/README.md](constitutive/README.md) for truth conditions.

### [counterfactual/](counterfactual/)
Counterfactual conditionals with 2 operators (□→, ◇→) implementing alternative world-state semantics. Validates key counterfactual principles while avoiding problematic inferences. Includes focused test examples. See [counterfactual/README.md](counterfactual/README.md) for counterfactual reasoning.

### [relevance/](relevance/)
Experimental relevance logic with 1 operator (⪯) imported from constitutive subtheory. Provides content-sensitive relevance without additional operators. Includes 3 test examples. See [relevance/README.md](relevance/README.md) for relevance semantics.

## Documentation

### For New Users
- **[Dependency Management](#dependency-management)** - How subtheories resolve dependencies
- **[Running Examples](#running-examples)** - Command-line testing of subtheories

### For Researchers
- **[Integration Patterns](#integration-patterns)** - Combining subtheories for complex reasoning
- **[API Reference](#api-reference)** - Complete function and class documentation
- **[Individual Testing](#individual-subtheory-testing)** - Testing specific logical systems

### For Developers
- **[Subtheory Structure](#subtheory-structure)** - Standard organization and requirements
- **[Adding New Subtheories](#adding-new-subtheories)** - How to extend the system
- **[Unit Testing](#unit-testing)** - Comprehensive test suite documentation

## Examples

### Dependency Management

Subtheories automatically resolve their dependencies.

#### Loading Operators

```python
from model_checker.theory_lib import logos

# Load only what you need - modal logic
theory = logos.get_theory(['extensional', 'modal'])

# Example: Modal K Axiom
# MOD_TH_5: MODAL K AXIOM
MOD_TH_5_premises = ["\\Box (A \\rightarrow B)", "\\Box A"]
MOD_TH_5_conclusions = ["\\Box B"]
MOD_TH_5_settings = {
    'N': 4,
    'contingent': False,
    'non_null': True,
    'non_empty': True,
    'disjoint': False,
    'max_time': 2,
    'iterate': 1,
    'expectation': False,
}
MOD_TH_5_example = [MOD_TH_5_premises, MOD_TH_5_conclusions, MOD_TH_5_settings]

# Hyperintensional content relationships
theory = logos.get_theory(['constitutive'])  # Auto-loads extensional

# Example: Grounding Anti-symmetry
# CON_TH_16: GROUNDING ANTI-SYMMETRY
CON_TH_16_premises = ["(A \\leq B)", "(B \\leq A)"]
CON_TH_16_conclusions = ["(A \\equiv B)"]
CON_TH_16_settings = {
    'N': 2,
    'contingent': False,
    'non_null': False,
    'non_empty': False,
    'disjoint': False,
    'max_time': 2,
    'iterate': 1,
    'expectation': False,
}
CON_TH_16_example = [CON_TH_16_premises, CON_TH_16_conclusions, CON_TH_16_settings]

# Full system with all core subtheories
theory = logos.get_theory()  # Loads extensional, modal, constitutive, counterfactual
```

#### Automatic Resolution

```python
# Requesting modal automatically includes extensional
theory = logos.get_theory(['modal'])
print(len(theory['operators'].operator_dictionary))  # 11 operators (7 + 4)

# Requesting relevance loads full dependency chain
theory = logos.get_theory(['relevance'])
# Loads: extensional → constitutive → relevance

# Dependency visualization:
# extensional (base - required by all)
#   ├── modal (needs negation for possibility)
#   ├── counterfactual (needs basic connectives)
#   └── constitutive (needs conjunction for reduction)
#       └── relevance (imports from constitutive)
```

### Running Examples

#### Command Line
```bash
# Run individual subtheory examples
./dev_cli.py src/model_checker/theory_lib/logos/subtheories/modal/examples.py

# With detailed output
./dev_cli.py -p -z src/model_checker/theory_lib/logos/subtheories/constitutive/examples.py

# Run all logos examples
./dev_cli.py src/model_checker/theory_lib/logos/examples.py
```

### Integration Patterns

#### Combining Modal and Constitutive Logic
```python
theory = logos.get_theory(['modal', 'constitutive'])

# Example: Modal and Constitutive Interaction
# MOD_CON_1: GROUNDING AND NECESSITY
MOD_CON_1_premises = ["(A \\leq B)", "\\Box A"]
MOD_CON_1_conclusions = ["\\Box B"]
MOD_CON_1_settings = {
    'N': 3,
    'contingent': False,
    'non_null': False,
    'non_empty': False,
    'disjoint': False,
    'max_time': 1,
    'iterate': 1,
    'expectation': False,
}
MOD_CON_1_example = [MOD_CON_1_premises, MOD_CON_1_conclusions, MOD_CON_1_settings]

# For complete implementation, see individual subtheory examples.py files.
```

#### Cross-Subtheory Reasoning
```python
# Counterfactual and modal interaction
theory = logos.get_theory(['modal', 'counterfactual'])

# Example: Modal and Counterfactual Interaction
# MOD_CF_1: NECESSITY AND COUNTERFACTUALS
MOD_CF_1_premises = ["\\Box A", "(A \\boxright B)"]
MOD_CF_1_conclusions = ["\\Box B"]
MOD_CF_1_settings = {
    'N': 3,
    'contingent': False,
    'non_null': False,
    'non_empty': False,
    'disjoint': False,
    'max_time': 1,
    'iterate': 1,
    'expectation': True,
}
MOD_CF_1_example = [MOD_CF_1_premises, MOD_CF_1_conclusions, MOD_CF_1_settings]

# For complete implementation, see individual subtheory examples.py files.
```

## API Reference

### Main Module Functions

```python
from model_checker.theory_lib.logos.subtheories import (
    AVAILABLE_SUBTHEORIES,      # List['extensional', 'modal', ...]
    SUBTHEORY_DESCRIPTIONS,     # Dict[str, str] - name to description
    get_subtheory_module,       # (name: str) -> ModuleType
    list_subtheories           # () -> Dict[str, str]
)
```

### Per-Subtheory API

Each subtheory exports a consistent API:

```python
# Core functions (from subtheory.__init__)
get_operators()  # Dict[str, Type[Operator]] - operator name to class
get_examples()   # Dict[str, List] - example collections

# Operator classes (from subtheory.__init__)
# Extensional: NegationOperator, AndOperator, OrOperator, ...
# Modal: NecessityOperator, PossibilityOperator, ...
# Constitutive: IdentityOperator, GroundOperator, ...
```

### Subtheory Structure

Each subtheory follows this standard structure:

```python
subtheory_name/
├── __init__.py        # Public API exports
├── README.md          # Documentation (comprehensive format)
├── operators.py       # Operator implementations
├── examples.py        # Test examples and demos
└── tests/            # Unit tests and validation
    ├── __init__.py
    ├── README.md      # Test documentation
    └── test_*.py      # Test implementations
```

## Testing and Validation

### Individual Subtheory Testing

Test specific subtheories from the project root:

```bash
# Developer mode with detailed output
./dev_cli.py src/model_checker/theory_lib/logos/subtheories/modal/examples.py
./dev_cli.py -p -z src/model_checker/theory_lib/logos/subtheories/constitutive/examples.py

# Using model-checker command
model-checker src/model_checker/theory_lib/logos/subtheories/extensional/examples.py
```

### Unit Testing

Run comprehensive test suites:

```bash
# Test all logos subtheories
python test_theories.py --theories logos

# Test specific subtheory
pytest src/model_checker/theory_lib/logos/subtheories/modal/tests/

# Test specific examples by name
pytest src/model_checker/theory_lib/logos/tests/ -k "MOD_TH_1"

# Verbose output for debugging
python test_theories.py --theories logos -v
```

### Test Categories

Each subtheory includes standardized test categories:

- **Countermodels (*_CM_*)**: Invalid arguments that should find countermodels
- **Theorems (*_TH_*)**: Valid arguments that should not find countermodels
- **Definitions (*_DEF_*)**: Operator interdefinability and equivalences

## Development

### Adding New Subtheories

1. Create directory structure:
   ```bash
   mkdir -p logos/subtheories/new_theory/tests
   ```

2. Implement required files:
   - `operators.py`: Operator classes extending `model_checker.syntactic.Operator`
   - `examples.py`: Test examples in standard format
   - `__init__.py`: Public API exports
   - `README.md`: Documentation following comprehensive format
   - `tests/test_*.py`: Unit tests

3. Update `AVAILABLE_SUBTHEORIES` in main `__init__.py`

4. Add dependency resolution if needed

5. Create comprehensive test coverage

### Modifying Existing Subtheories

1. Follow patterns in `operators.py` for consistency
2. Add examples using standard format in `examples.py`
3. Update `__init__.py` exports for new operators
4. Document changes in subtheory README
5. Add unit tests for new functionality

## References

### Implementation Documentation
- Individual subtheory READMEs contain detailed operator semantics and truth conditions
- Test documentation in each `tests/README.md` explains validation methodology

### Related Resources
- **[Logos Theory Documentation](../README.md)** - Complete framework overview
- **[Theory Library Documentation](../../README.md)** - All available theories
- **[ModelChecker Documentation](../../../../README.md)** - System documentation

---

[← Back to Logos Theory](../README.md) | [Extensional →](extensional/README.md) | [Modal →](modal/README.md)