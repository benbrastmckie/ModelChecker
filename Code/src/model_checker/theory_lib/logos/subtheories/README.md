# Logos Subtheories: Modular Operator Systems

This directory contains the implementation of the Logos theory's modular subtheory system. Each subtheory provides specialized logical operators organized by domain, enabling selective loading and clean separation of logical concerns.

## Available Subtheories

### Core Subtheories (Default Set)

| Subtheory | Operators | Description |
|-----------|-----------|-------------|
| **extensional** | 7 operators | Truth-functional operators (¬,∧,∨,→,↔,⊤,⊥) |
| **modal** | 4 operators | Necessity and possibility operators (□,◇,CFBox,CFDiamond) |
| **constitutive** | 5 operators | Content relations (≡,≤,⊑,≼,⇒) |
| **counterfactual** | 4 operators | Hypothetical reasoning (□→,◇→,◦,◯) |

### Experimental Subtheories

| Subtheory | Operators | Description |
|-----------|-----------|-------------|
| **relevance** | 1 operator | Content-sensitive relevance logic (≼) |

## Quick Start

### Loading Subtheories

```python
from model_checker.theory_lib import logos

# Load default set (excludes experimental relevance)
theory = logos.get_theory()

# Load specific subtheories
theory = logos.get_theory(['extensional', 'modal'])

# Load all including experimental
theory = logos.get_theory(['extensional', 'modal', 'constitutive', 'counterfactual', 'relevance'])

# Access operators
operators = theory['operators']
```

### Dependency Management

Subtheories automatically load their dependencies:

```
extensional (base - no dependencies)
    ↳ modal (depends on extensional)
    ↳ counterfactual (depends on extensional)
    ↳ constitutive (no dependencies beyond extensional)
        ↳ relevance (depends on constitutive)
```

### Direct Subtheory Access

```python
# Load individual subtheory
from model_checker.theory_lib.logos.subtheories import extensional

# Get operators from subtheory
operators = extensional.get_operators()
examples = extensional.get_examples()

# Access specific operator classes
from model_checker.theory_lib.logos.subtheories.extensional import NegationOperator
```

## Subtheory Structure

Each subtheory follows a consistent structure:

```
subtheory_name/
├── __init__.py        # Public API exports
├── README.md          # Documentation and examples
├── operators.py       # Operator implementations
├── examples.py        # Test examples and demos
└── tests/            # Unit tests and validation
    ├── __init__.py
    ├── README.md      # Testing documentation
    └── test_*.py      # Test implementations
```

### API Consistency

All subtheories provide:

```python
# Core functions (available from __init__.py)
get_operators()  # Returns {name: operator_class} mapping
get_examples()   # Returns example collections

# Direct imports (available from __init__.py)
# Individual operator classes for type checking
```

## Examples and Testing

### Running Examples

```bash
# Run all examples for a subtheory
./dev_cli.py src/model_checker/theory_lib/logos/subtheories/modal/examples.py

# Run with detailed output
./dev_cli.py -p -z src/model_checker/theory_lib/logos/subtheories/modal/examples.py
```

### Running Tests

```bash
# Test specific subtheory
pytest src/model_checker/theory_lib/logos/subtheories/modal/tests/

# Test all logos subtheories
python test_theories.py --theories logos

# Test specific examples
pytest src/model_checker/theory_lib/logos/subtheories/modal/tests/ -k "MOD_TH_1"
```

### Example Categories

Each subtheory includes comprehensive examples:

- **Countermodels** (*_CM_*): Invalid arguments that should find countermodels
- **Theorems** (*_TH_*): Valid arguments that should be proven
- **Definitions** (*_DEF_*): Definitional equivalences between operators

## Integration Patterns

### Combining Subtheories

```python
# Modal + Counterfactual interaction
theory = logos.get_theory(['modal', 'counterfactual'])
model = BuildExample("mixed_modal_cf", theory)

# Test interaction between necessity and counterfactuals
premises = ["\\Box p", "(p \\boxright q)"]
conclusion = "\\Box q"
result = model.check_validity(premises, [conclusion])
```

### Cross-Subtheory Dependencies

- **Modal** operators use **extensional** negation for possibility definitions
- **Relevance** operators build on **constitutive** relations
- **Counterfactual** operators combine with **modal** operators for complex reasoning

## Development

### Adding New Subtheories

1. Create directory: `mkdir logos/subtheories/new_subtheory`
2. Implement required files: `operators.py`, `examples.py`, `__init__.py`, `README.md`
3. Add to `AVAILABLE_SUBTHEORIES` in `__init__.py`
4. Update dependency chain if needed
5. Create comprehensive test suite

### Modifying Existing Subtheories

1. Follow existing patterns in `operators.py` for new operators
2. Add examples in `examples.py` using standard format
3. Update `__init__.py` exports for new operators
4. Document in subtheory's `README.md`
5. Add unit tests in `tests/`

## Individual Subtheory Testing

To test a specific subtheory, use these commands from the project root:

**Developer mode (using dev_cli.py):**
- `./dev_cli.py src/model_checker/theory_lib/logos/subtheories/counterfactual/examples.py`
- `./dev_cli.py src/model_checker/theory_lib/logos/subtheories/constitutive/examples.py`
- `./dev_cli.py src/model_checker/theory_lib/logos/subtheories/modal/examples.py`
- `./dev_cli.py src/model_checker/theory_lib/logos/subtheories/extensional/examples.py`
- `./dev_cli.py src/model_checker/theory_lib/logos/subtheories/relevance/examples.py`

**Using model-checker command:**
- `model-checker src/model_checker/theory_lib/logos/subtheories/counterfactual/examples.py`
- `model-checker src/model_checker/theory_lib/logos/subtheories/constitutive/examples.py`
- `model-checker src/model_checker/theory_lib/logos/subtheories/modal/examples.py`
- `model-checker src/model_checker/theory_lib/logos/subtheories/extensional/examples.py`
- `model-checker src/model_checker/theory_lib/logos/subtheories/relevance/examples.py`

### Complete Logos Theory Testing

To test the entire Logos theory including all subtheories:

**Developer mode:**
- `./dev_cli.py src/model_checker/theory_lib/logos/examples.py`

**Using model-checker command:**
- `model-checker src/model_checker/theory_lib/logos/examples.py`

## Unit Testing

**Unit test suite (includes all examples from all subtheories):**
- `python test_theories.py --theories logos`

**Run only the unified subtheory examples:**
- `python -m pytest src/model_checker/theory_lib/logos/tests/test_logos_examples.py -v`

**Run specific examples by name:**
- `python -m pytest src/model_checker/theory_lib/logos/tests/test_logos_examples.py -k "EXT_CM_1" -v`

### Debugging Test Failures

To see detailed information about test failures, use verbose mode:

**Verbose output:**
- `python test_theories.py --theories logos -v`

**Stop on first failure:**
- `python test_theories.py --theories logos -x`

**Direct pytest for more control:**
- `python -m pytest src/model_checker/theory_lib/logos/tests/ -v`
- `python -m pytest src/model_checker/theory_lib/logos/tests/test_logos.py::TestLogosSemantics::test_semantics_instantiation -v -s`

**With timeout for hanging tests:**
- `python -m pytest src/model_checker/theory_lib/logos/tests/ -v --timeout=30`

The `-v` flag shows verbose output including which specific test failed and why. The `-s` flag shows print statements and other output from tests. The `--timeout=30` flag kills tests that run longer than 30 seconds, useful for identifying hanging tests.

## API Reference

### Main Functions

```python
from model_checker.theory_lib.logos.subtheories import (
    AVAILABLE_SUBTHEORIES,     # List of all subtheory names
    SUBTHEORY_DESCRIPTIONS,    # Name -> description mapping
    get_subtheory_module,      # Load specific subtheory module
    list_subtheories          # Get descriptions dictionary
)
```

### Per-Subtheory APIs

Each subtheory exports:

```python
# Core API (all subtheories)
get_operators()    # {operator_name: operator_class}
get_examples()     # Example collections

# Operator classes (subtheory-specific)
# e.g., for extensional:
NegationOperator, AndOperator, OrOperator, ...

# e.g., for modal:  
NecessityOperator, PossibilityOperator, ...
```

---

For detailed documentation on individual subtheories, see their respective README files:

- [Extensional README](extensional/README.md) - Truth-functional operators
- [Modal README](modal/README.md) - Necessity and possibility 
- [Constitutive README](constitutive/README.md) - Content relations
- [Counterfactual README](counterfactual/README.md) - Hypothetical reasoning
- [Relevance README](relevance/README.md) - Relevance logic