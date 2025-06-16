# Logos Theory: Modular Hyperintensional Truthmaker Semantics

The **Logos Theory** is a modular implementation of hyperintensional truthmaker semantics that organizes logical operators by domain. It provides a clean, maintainable alternative to monolithic theory implementations by separating operators into focused subtheories.

## Overview

The Logos Theory implements **20 logical operators** across **4 main subtheories**:

- **Extensional**: Truth-functional operators (7 operators)
- **Modal**: Necessity and possibility operators (4 operators) 
- **Constitutive**: Ground, essence, and identity operators (5 operators)
- **Counterfactual**: Counterfactual conditional operators (4 operators)

This modular architecture enables:
- **Selective loading** of operator subsets
- **Clean separation** of logical domains
- **Easy extension** with new subtheories
- **Maintainable codebase** with focused modules

## Quick Start

### Basic Usage

```python
from model_checker.theory_lib import logos

# Load all subtheories (default)
theory = logos.get_theory()

# Load specific subtheories
theory = logos.get_theory(['extensional', 'modal'])

# Access operators
operators = theory['operators']
print(f"Loaded {len(operators.operator_dictionary)} operators")
```

### Creating Models

```python
from model_checker import BuildExample

# Create a model using logos theory
model = BuildExample("modal_example", theory)

# Check a formula
result = model.check_formula("\\Box p \\rightarrow p")
print(f"□p → p is {'valid' if result else 'invalid'}")
```

### Project Generation

```bash
# Generate a new logos-based project
./dev_cli.py -l logos

# Or interactively
model-checker -l logos
```

## Subtheory Reference

### Extensional Subtheory

Truth-functional operators following classical propositional logic.

| Operator | Symbol | Name | Arity | Description |
|----------|---------|------|-------|-------------|
| `\\neg` | ¬ | Negation | 1 | Logical negation |
| `\\wedge` | ∧ | Conjunction | 2 | Logical AND |
| `\\vee` | ∨ | Disjunction | 2 | Logical OR |
| `\\rightarrow` | → | Conditional | 2 | Material implication |
| `\\leftrightarrow` | ↔ | Biconditional | 2 | Logical equivalence |
| `\\top` | ⊤ | Top | 0 | Logical truth |
| `\\bot` | ⊥ | Bottom | 0 | Logical falsehood |

**Example Usage:**
```python
# Modus ponens
model.check_validity(["p", "p \\rightarrow q"], ["q"])  # → True

# Law of excluded middle  
model.check_validity([], ["p \\vee \\neg p"])  # → True
```

### Modal Subtheory

Operators for necessity and possibility with counterfactual variants.

| Operator | Symbol | Name | Arity | Description |
|----------|---------|------|-------|-------------|
| `\\Box` | □ | Necessity | 1 | Modal necessity |
| `\\Diamond` | ◇ | Possibility | 1 | Modal possibility |
| `\\CFBox` | CFBox | CF Necessity | 1 | Counterfactual necessity |
| `\\CFDiamond` | CFDiamond | CF Possibility | 1 | Counterfactual possibility |

**Dependencies**: Requires extensional operators for defined operators.

**Example Usage:**
```python
# Necessity implies truth
model.check_validity(["\\Box p"], ["p"])  # → True

# Possibility consistency
model.check_validity(["\\Diamond p"], ["\\neg \\Box \\neg p"])  # → True
```

### Constitutive Subtheory

Operators for ground, essence, identity, and reduction relationships.

| Operator | Symbol | Name | Arity | Description |
|----------|---------|------|-------|-------------|
| `\\equiv` | ≡ | Identity | 2 | Propositional identity |
| `\\leq` | ≤ | Ground | 2 | Grounding relation |
| `\\sqsubseteq` | ⊑ | Essence | 2 | Essence relation |
| `\\preceq` | ≼ | Relevance | 2 | Relevance relation |
| `\\reduction` | reduction | Reduction | 2 | Ground + essence |

**Example Usage:**
```python
# Identity is reflexive
model.check_validity([], ["p \\equiv p"])  # → True

# Ground relationship
model.check_validity(["p \\leq q", "p"], ["q"])  # → True
```

### Counterfactual Subtheory

Operators for counterfactual reasoning and imposition.

| Operator | Symbol | Name | Arity | Description |
|----------|---------|------|-------|-------------|
| `\\boxright` | □→ | Counterfactual | 2 | Would counterfactual |
| `\\diamondright` | ◇→ | Might CF | 2 | Might counterfactual |
| `\\imposition` | imposition | Imposition | 2 | Imposition relation |
| `\\could` | could | Might Imposition | 2 | Might imposition |

**Example Usage:**
```python
# Counterfactual reasoning
model.check_formula("(p \\boxright q) \\rightarrow (p \\diamondright q)")
```

## Architecture

### Core Components

The logos theory implements a **three-layer architecture**:

1. **Core Framework** (`semantic.py`, `operators.py`)
   - `LogosSemantics`: Shared semantic foundation
   - `LogosOperatorRegistry`: Dynamic operator loading
   - `LogosProposition`/`LogosModelStructure`: Model components

2. **Subtheory Layer** (`subtheories/`)
   - Individual operator implementations
   - Modular loading and dependency management
   - Isolated testing and validation

3. **Integration Layer** (`__init__.py`, `examples.py`)
   - Unified API for theory access
   - Example configurations and test cases
   - Documentation and usage guides

### Operator Registry

The `LogosOperatorRegistry` provides dynamic loading:

```python
registry = LogosOperatorRegistry()

# Load specific subtheories
registry.load_subtheories(['extensional', 'modal'])

# Access loaded operators
operators = registry.get_operators()
```

### Dependency Management

Subtheories can depend on others (e.g., modal depends on extensional):

```python
# Dependencies are automatically resolved
theory = logos.get_theory(['modal'])  # Also loads extensional
```

## Examples

### Complete Example Scripts

Each subtheory includes comprehensive examples in `subtheories/{name}/examples.py`:

- **Extensional examples**: Classical logic demonstrations
- **Modal examples**: Necessity/possibility relationships  
- **Constitutive examples**: Ground and essence principles
- **Counterfactual examples**: Hypothetical reasoning

### Interactive Examples

```python
from model_checker.theory_lib import logos

# Load theory with all subtheories
theory = logos.get_theory()

# Create example builder
from model_checker import BuildExample
model = BuildExample("logos_demo", theory)

# Test mixed logic
premises = ["\\Box (p \\equiv q)", "p \\wedge r"]
conclusion = "\\Box q \\wedge r"
result = model.check_validity(premises, [conclusion])
```

## Testing

The logos theory includes comprehensive test coverage:

### Running Tests

```bash
# All logos tests
python test_theories.py --theories logos

# Specific test categories
pytest src/model_checker/theory_lib/logos/tests/test_logos.py -v
pytest src/model_checker/theory_lib/logos/tests/test_subtheories.py -v
```

### Test Coverage

- **43 total tests** (27 main + 16 subtheory)
- **Theory loading and registration**
- **Individual subtheory isolation** 
- **Cross-subtheory integration**
- **Semantic framework validation**
- **Builder and CLI integration**

## API Reference

### Main API

```python
# Theory loading
theory = logos.get_theory(subtheories=None)
# Returns: dict with 'semantics', 'proposition', 'model', 'operators'

# Selective loading
theory = logos.get_theory(['extensional', 'modal'])

# Access components
semantics_class = theory['semantics']
operators = theory['operators']
```

### Subtheory APIs

Each subtheory provides:

```python
from model_checker.theory_lib.logos.subtheories import extensional

# Get operators
operators = extensional.get_operators()
# Returns: dict mapping operator names to classes
```

### Semantic Framework

```python
# Create semantics instance
semantics = LogosSemantics(combined_settings={'N': 8})

# Load subtheories
semantics.load_subtheories(['extensional', 'modal'])
```

## Advanced Usage

### Custom Subtheory Loading

```python
# Load minimal theory
basic_theory = logos.get_theory(['extensional'])

# Progressive loading
theory = logos.get_theory(['extensional'])
theory = logos.get_theory(['extensional', 'modal'])
```

### Integration with Jupyter

```python
# Interactive model checking
from model_checker.jupyter import check_formula

# Use logos theory
result = check_formula("\\Box p \\rightarrow p", theory='logos')
```

### Performance Considerations

- **Lazy loading**: Subtheories loaded on demand
- **Caching**: Operator registry caches loaded modules
- **Minimal overhead**: Only load needed operators

## Migration from Default Theory

The logos theory provides the same 20 operators as the default theory, organized modularly:

### Key Differences

1. **Modular structure** vs. monolithic file
2. **Selective loading** vs. all-or-nothing
3. **Clean separation** vs. mixed domains
4. **Easier maintenance** vs. complex interdependencies

### Migration Steps

1. Replace `default` with `logos` in theory loading
2. Optionally specify subtheories for selective loading
3. Update import statements to use modular structure
4. Test existing examples with new theory

## Contributing

### Adding New Subtheories

1. Create directory: `subtheories/new_subtheory/`
2. Implement required files:
   - `__init__.py`: API exports
   - `operators.py`: Operator implementations
   - `examples.py`: Usage examples
   - `README.md`: Documentation

3. Register in operator loading system
4. Add comprehensive tests
5. Update documentation

### Extending Existing Subtheories

1. Add new operators to appropriate `operators.py`
2. Update `get_operators()` function
3. Add examples and tests
4. Document new operators

## References

- **Truthmaker Semantics**: Fine (2017), "Truthmaker Semantics"
- **Hyperintensional Logic**: Berto & Restall (2019), "Hyperintensional Logics"
- **Ground Theory**: Correia & Schnieder (2012), "Metaphysical Grounding"

## License

The logos theory is part of the ModelChecker package and follows the same licensing terms. See `LICENSE.md` for details.