# LOGOS: A Unified Formal Language of Thought

The **Logos Semantic Theory** is a modular implementation of a bilateral hyperintensional semantics for the Logos, a formal language of thought that is both unified and extensible.
By restricting to finite models of a user-specified size, the semantics for the Logos provides a machine-checkable theory of logical consequence.
The semantics aims to assist efforts to axiomatize the operators included in the Logos by providing a principled way to explore logical reasoning within the Logos.

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
result = model.check_formula("(\\Box p \\rightarrow p)")
print(f"Box p -> p is {'valid' if result else 'invalid'}")  # ASCII output for clarity
```

### Project Generation

TODO: 
- explain the process of theory generation and development step-by-step
- link to a more detailed installation guide in /home/benjamin/Documents/Philosophy/Projects/ModelChecker/Docs/INSTALLATION.md

```bash
# Generate a new logos-based project
model-checker -l logos

# Develop a new logos-based that has been generated project
./dev_cli.py -l logos
```

## Subtheory Reference

### Extensional Subtheory

Truth-functional operators following classical propositional logic.

**Note**: Always use the ASCII LaTeX operators (left column) in code. Unicode symbols (middle column) are shown for reference only.

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
model.check_validity(["p", "(p \\rightarrow q)"], ["q"])  # Returns True

# Law of excluded middle  
model.check_validity([], ["(p \\vee \\neg p)"])  # Returns True
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
model.check_validity(["\\Box p"], ["p"])  # Returns True

# Possibility consistency
model.check_validity(["\\Diamond p"], ["(\\neg \\Box \\neg p)"])  # Returns True
```

### Constitutive Subtheory

Operators for ground, essence, identity, and reduction relationships.

| Operator | Symbol | Name | Arity | Description |
|----------|---------|------|-------|-------------|
| `\\equiv` | ≡ | Identity | 2 | Propositional identity |
| `\\leq` | ≤ | Ground | 2 | Grounding relation |
| `\\sqsubseteq` | ⊑ | Essence | 2 | Essence relation |
| `\\preceq` | ≼ | Relevance | 2 | Relevance relation |
| `\\Rightarrow` | ⇒ | Reduction | 2 | Ground + essence |

**Example Usage:**
```python
# Identity is reflexive
model.check_validity([], ["(p \\equiv p)"])  # Returns True

# Ground relationship
model.check_validity(["(p \\leq q)", "p"], ["q"])  # Returns True
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
model.check_formula("((p \\boxright q) \\rightarrow (p \\diamondright q))")
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
premises = ["\\Box (p \\equiv q)", "(p \\wedge r)"]
conclusion = "(\\Box q \\wedge r)"
result = model.check_validity(premises, [conclusion])
```

## Testing

The Logos theory implements a comprehensive testing framework covering both implementation-level unit tests and logical validation through examples.

### Test Organization

**Core Theory Tests** (in `tests/`):
- **Integration Tests**: Cross-subtheory examples and complete theory validation
- **Unit Tests**: Implementation testing of semantic methods, operators, and registry
- **[Detailed Documentation](tests/README.md)**

**Subtheory-Specific Tests**:
- **Extensional** (14 examples): Truth-functional logic validation → [tests/README.md](subtheories/extensional/tests/README.md)
- **Modal** (23 examples): Necessity/possibility reasoning → [tests/README.md](subtheories/modal/tests/README.md)
- **Constitutive** (33 examples): Content relationships and hyperintensional logic → [tests/README.md](subtheories/constitutive/tests/README.md)
- **Counterfactual** (33 examples): Hypothetical reasoning and counterfactuals → [tests/README.md](subtheories/counterfactual/tests/README.md)
- **Relevance** (20 examples): Relevance-sensitive logical principles → [tests/README.md](subtheories/relevance/tests/README.md)

### Running Tests

**All Logos Tests**:
```bash
# Run complete test suite
python test_theories.py --theories logos

# Examples only
python test_theories.py --theories logos --examples

# Unit tests only
python test_theories.py --theories logos --package
```

**Subtheory-Specific Testing**:
```bash
# All tests for specific subtheory
python test_theories.py --theories logos --constitutive

# Examples for specific subtheory
python test_theories.py --theories logos --modal --examples

# Direct pytest execution
pytest src/model_checker/theory_lib/logos/subtheories/constitutive/tests/
```

**For complete testing documentation, including debugging guides, test structure, and advanced usage, see:**
- **Core Theory Tests**: [tests/README.md](tests/README.md)
- **Unit Testing Policy**: [UNIT_TESTS.md](UNIT_TESTS.md)
- **Individual Subtheory Test Documentation**: Linked above

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
result = check_formula("(\\Box p \\rightarrow p)", theory='logos')
```

### Performance Considerations

- **Lazy loading**: Subtheories loaded on demand
- **Caching**: Operator registry caches loaded modules
- **Minimal overhead**: Only load needed operators

## Contributing

TODO: 
- provide more details while also linking to /home/benjamin/Documents/Philosophy/Projects/ModelChecker/Code/docs/DEVELOPMENT.md
- DEVELOPMENT has been moved to /home/benjamin/Documents/Philosophy/Projects/ModelChecker/Code/docs/DEVELOPMENT.md

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

TODO: include Fine's other papers and my papers

- **Truthmaker Semantics**: Fine (2017), "Truthmaker Semantics"

## License

TODO: add a licence and include a link here

The logos theory is part of the ModelChecker package and follows the same licensing terms. See `LICENSE.md` for details.
