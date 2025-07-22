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

The logos theory can be used as a foundation for developing custom semantic theories. Here's a step-by-step guide:

#### Step 1: Generate a New Project

```bash
# Generate a new logos-based project
model-checker -l logos
```

This command will:
1. Prompt you to create a new logos-based project
2. Ask for a project name (use snake_case)
3. Create a `project_<your_name>/` directory with:
   - Complete logos theory implementation
   - Example files demonstrating usage
   - Test infrastructure
   - Documentation templates

#### Step 2: Project Structure

Your generated project will have this structure:
```
project_<name>/
├── __init__.py          # Package initialization
├── semantic.py          # Core semantic implementation
├── operators.py         # Operator definitions
├── examples.py          # Example formulas and tests
├── subtheories/        # Modular operator implementations
│   ├── extensional/
│   ├── modal/
│   ├── constitutive/
│   ├── counterfactual/
│   └── relevance/
├── tests/              # Unit and integration tests
├── notebooks/          # Jupyter notebooks for exploration
├── README.md           # Project documentation
├── LICENSE.md          # GPL-3.0 license
└── CITATION.md         # Academic attribution

```

#### Step 3: Development Workflow

1. **Modify the theory**: Edit files in your project to customize the semantic theory
2. **Test your changes**: Run examples to verify your modifications work correctly
3. **Use development mode**: For iterative development, use:
   ```bash
   ./dev_cli.py project_<name>/examples.py
   ```

#### Step 4: Running Examples

```bash
# Run the default examples
model-checker project_<name>/examples.py

# Run with specific settings
model-checker project_<name>/examples.py -c -n -e

# Run tests
pytest project_<name>/tests/
```

For detailed installation instructions including Python setup and troubleshooting, see the [Installation Guide](../../../../docs/INSTALLATION.md).

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

The Logos theory includes comprehensive Jupyter notebook tutorials and demonstrations. See **[notebooks/README.md](notebooks/README.md)** for the complete interactive learning environment.

```python
# Interactive model checking
from model_checker.jupyter import check_formula

# Use logos theory
result = check_formula("(\\Box p \\rightarrow p)", theory='logos')
```

**Available Notebooks**:
- **[Main Theory Demo](notebooks/logos_demo.ipynb)**: Complete introduction with all 5 subtheories
- **[Modal Operators](notebooks/subtheories/modal_operators_demo.ipynb)**: Hyperintensional modal logic
- **[Extensional Operators](notebooks/subtheories/extensional_operators_demo.ipynb)**: Truthmaker semantics for classical logic

### Performance Considerations

The Logos theory is designed for optimal performance through modular architecture:

### Memory Management
- **Lazy loading**: Subtheories loaded on demand to minimize memory footprint
- **Operator caching**: Registry caches loaded modules to avoid repeated imports
- **Selective loading**: Only load needed operators (e.g., modal-only for basic necessity/possibility)
- **Memory footprint**: Base theory ~50KB, full theory ~200KB

### Computational Complexity
- **Model size scaling**: O(2^N) for N-bit models (typical N=3-5)
- **Formula complexity**: Linear in formula depth for most operators
- **Subtheory interactions**: Minimal overhead for cross-subtheory dependencies
- **Z3 solver performance**: Optimized constraint patterns for faster solving

### Performance Benchmarks
- **Small models (N=3)**: Sub-second evaluation for most formulas
- **Medium models (N=4)**: 1-5 seconds for complex multi-operator formulas
- **Large models (N=5)**: 10-30 seconds for extensive logical reasoning
- **Timeout settings**: Default 60 seconds, adjustable via settings

### Optimization Tips
```python
# Load only needed subtheories
theory = logos.get_theory(['extensional', 'modal'])  # Faster than full loading

# Use smaller model sizes when possible
settings = {'N': 3}  # Much faster than N=4 or N=5

# Cache theory instances for repeated use
cached_theory = logos.get_theory()  # Reuse for multiple examples
```

## Contributing

We welcome contributions to the Logos theory! Whether you're adding new operators, fixing bugs, or improving documentation, your contributions help advance this unified semantic framework.

For general development guidelines, coding standards, and the overall contribution process, see the [Development Guide](../../../DEVELOPMENT.md).

### Adding New Subtheories

Creating a new subtheory extends the Logos with additional logical operators. Here's a detailed guide:

#### 1. Create the Subtheory Structure

```bash
# Create directory structure
mkdir -p subtheories/new_subtheory/tests
```

#### 2. Implement Required Files

**`subtheories/new_subtheory/__init__.py`**:
```python
"""New subtheory for [description]."""

from .operators import get_operators

__all__ = ['get_operators']
```

**`subtheories/new_subtheory/operators.py`**:
```python
"""Operator implementations for new subtheory."""

from model_checker.syntactic import Operator, DefinedOperator

class NewOperator(Operator):
    """Implementation of new operator."""
    def __init__(self):
        super().__init__("\\new", 2)  # Name and arity
    
    def semantic_clause(self, sentence):
        # Implement semantic evaluation
        pass

def get_operators():
    """Return dictionary of operators."""
    return {
        '\\new': NewOperator,
    }
```

**`subtheories/new_subtheory/examples.py`**:
```python
"""Examples demonstrating the new operators."""

new_example = [
    ['premise1', 'premise2'],  # Premises
    ['conclusion'],            # Conclusions
    {'N': 3}                   # Settings
]

examples_list = [new_example]
```

**`subtheories/new_subtheory/README.md`**:
Document your subtheory including:
- Overview and motivation
- Operator descriptions and semantics
- Usage examples
- Academic references

#### 3. Register in Operator Loading System

Update `operators.py` in the main logos directory:

```python
# In SUBTHEORY_INFO, add:
'new_subtheory': {
    'module': 'new_subtheory',
    'dependencies': ['extensional'],  # If needed
}
```

#### 4. Add Comprehensive Tests

Create tests in `subtheories/new_subtheory/tests/`:
- `test_new_subtheory_examples.py`: Validate logical principles
- Include both valid inferences and expected countermodels
- Follow existing test patterns

#### 5. Update Documentation

- Add subtheory to this README's overview
- Update operator counts
- Add to the subtheory reference section
- Link test documentation

### Extending Existing Subtheories

To add new operators to existing subtheories:

#### 1. Add Operator Implementation

In the appropriate `subtheories/[name]/operators.py`:

```python
class NewOperator(Operator):
    """Docstring explaining the operator."""
    def __init__(self):
        super().__init__("\\newop", arity)
    
    def semantic_clause(self, sentence):
        # Implementation
        pass
```

#### 2. Update get_operators()

Add your operator to the returned dictionary:

```python
def get_operators():
    return {
        # Existing operators...
        '\\newop': NewOperator,
    }
```

#### 3. Add Examples and Tests

- Add examples to `examples.py` demonstrating the operator
- Create test cases validating its behavior
- Document any interactions with other operators

#### 4. Document the Operator

- Update the subtheory's README
- Add to operator tables with proper LaTeX/Unicode notation
- Include usage examples

### Code Quality Standards

- Follow PEP 8 style guidelines
- Include comprehensive docstrings
- Write clear, self-documenting code
- Add type hints where beneficial
- Ensure all tests pass before submitting

### Testing Requirements

Before submitting a PR:

```bash
# Run all logos tests
python test_theories.py --theories logos

# Run specific subtheory tests
pytest src/model_checker/theory_lib/logos/subtheories/your_subtheory/tests/

# Check code style
flake8 src/model_checker/theory_lib/logos/
```

### Pull Request Process

1. Fork the repository
2. Create a feature branch: `git checkout -b feature/new-operator`
3. Make your changes following the guidelines above
4. Ensure all tests pass
5. Update documentation
6. Submit a pull request with:
   - Clear description of changes
   - Motivation for additions
   - Any relevant academic references

For more details on the development process, testing philosophy, and project architecture, see the [Development Guide](../../../DEVELOPMENT.md).

## References

- Brast-McKie (2021) ["Identity and Aboutness"](https://link.springer.com/article/10.1007/s10992-021-09612-w), Journal of Philosophical Logic
- Brast-McKie (2025) ["Counterfactual Worlds"](https://link.springer.com/article/10.1007/s10992-025-09793-8), Journal of Philosophical Logic

This work builds on the truthmaker semantics developed by Kit Fine in the following papers:

- Fine (2017) ["Counterfactuals without Possible Worlds"](https://link.springer.com/article/10.1007/BF00248737), Journal of Philosophy
- Fine (2017) ["A Theory of Truthmaker Content I: Conjunction, Disjunction and Negation"](https://link.springer.com/article/10.1007/s10992-016-9413-y), Journal of Philosophical Logic
- Fine (2017) ["A Theory of Truthmaker Content II: Subject-Matter, Common Content, Remainder and Ground"](https://doi.org/10.1007/s10992-016-9419-5) Journal of Philosophical Logic
- Fine (2017) ["Truthmaker Semantics"](https://doi.org/10.1002/9781118972090.ch22), Wiley-Blackwell

## Implementation Details

### Semantic Framework

The Logos theory implements **hyperintensional truthmaker semantics** based on Kit Fine's work:

- **Bilateral propositions**: Each proposition has both verifiers and falsifiers
- **State-based models**: Finite models with 2^N possible states
- **Truthmaker relations**: States that make propositions true/false
- **Fusion operations**: Combining states through algebraic operations

### Core Data Structures

```python
class LogosProposition:
    """Bilateral proposition with verifiers and falsifiers."""
    def __init__(self, name: str, verifiers: Set[int], falsifiers: Set[int])
    
class LogosModelStructure:
    """Model structure with state space and relations."""
    def __init__(self, N: int, fusion_table: Dict, exclusion_relation: Set)
```

### Operator Implementation Pattern

```python
class LogosOperator(Operator):
    """Base class for logos operators."""
    def semantic_clause(self, sentence: Sentence) -> z3.BoolRef:
        """Generate Z3 constraints for semantic conditions."""
        
    def compute_verifiers(self, args: List, model: Model, eval_point: int) -> List[int]:
        """Compute states that verify the formula."""
        
    def compute_falsifiers(self, args: List, model: Model, eval_point: int) -> List[int]:
        """Compute states that falsify the formula."""
```

### Integration Architecture

The theory integrates with ModelChecker through standardized interfaces:

1. **Theory Registration**: Automatic discovery via `__init__.py`
2. **Operator Loading**: Dynamic registry with dependency resolution
3. **Example Processing**: Compatible with `dev_cli.py` and test runners
4. **Jupyter Integration**: Seamless notebook support via adapters

## Theoretical Background

### Hyperintensional Logic

The Logos implements hyperintensional logic that distinguishes logically equivalent but conceptually distinct propositions:

- **Beyond possible worlds**: Traditional modal logic equates all necessary truths
- **Content sensitivity**: Logos distinguishes "2+2=4" from "all bachelors are unmarried"
- **Fine-grained semantics**: Captures meaning differences invisible to classical logic

### Truthmaker Semantics

Following Fine's truthmaker framework:

- **Verifiers**: States of the world that make propositions true
- **Falsifiers**: States that make propositions false
- **Exact truthmakers**: Minimal states sufficient for truth
- **Fusion closure**: States can be combined to form more complex states

### Comparison with Other Logics

| Logic System | Intensionality | Operator Count | Key Features |
|--------------|----------------|----------------|-------------|
| **Classical Logic** | Extensional | 7 | Truth-functional, bivalent |
| **Modal Logic** | Intensional | 9 | Necessity/possibility, possible worlds |
| **Logos Theory** | Hyperintensional | 20+ | Content-sensitive, bilateral, modular |
| **Exclusion Theory** | Unilateral | 4 | Witness predicates, exclusion relations |

## Research Applications

### Academic Use Cases

- **Logic coursework**: Teaching hyperintensional semantics
- **Research validation**: Testing logical principles and axioms
- **Theory comparison**: Evaluating different semantic frameworks
- **Philosophical analysis**: Exploring content, ground, and essence

### Computational Applications

- **Automated reasoning**: Model checking for complex logical systems
- **Knowledge representation**: Expressing fine-grained conceptual distinctions
- **Formal verification**: Validating logical arguments and proofs
- **Educational tools**: Interactive exploration of logical concepts

## License

The logos theory is part of the ModelChecker package and follows the same licensing terms. See `LICENSE.md` for details.
