# Syntactic Package: Logical Formula Processing Framework

[← Back to ModelChecker](../README.md) | [Operators Guide →](operators.py) | [Theory Integration →](../theory_lib/README.md)

## Directory Structure

```
syntactic/
├── README.md               # This file - comprehensive syntactic documentation
├── __init__.py            # Package initialization and exports
├── atoms.py               # Z3 atomic propositions (AtomSort, AtomVal)
├── sentence.py            # Sentence class for formula representation
├── operators.py           # Operator and DefinedOperator base classes
├── collection.py          # OperatorCollection registry system
├── syntax.py              # Syntax processor for argument construction
└── tests/                 # Comprehensive test suite
    ├── __init__.py        # Test package initialization
    ├── test_atoms.py      # Tests for atomic propositions
    ├── test_sentence.py   # Tests for sentence processing
    ├── test_operators.py  # Tests for operator functionality
    ├── test_collection.py # Tests for operator collection
    └── test_syntax.py     # Tests for syntax processing
```

## Overview

The **syntactic package** provides the core logical formula processing framework for the ModelChecker system. It handles the transformation of user-input logical formulas into structured representations that can be evaluated by semantic components. This package is fundamental to all theory implementations, providing a uniform interface for operator definition, formula parsing, and syntactic analysis.

### Key Capabilities

1. **Formula Representation**: Convert between infix and prefix notation while maintaining all metadata needed for evaluation
2. **Operator Management**: Define and register both primitive and derived operators with proper validation
3. **Syntactic Analysis**: Parse complex logical formulas, validate operator usage, and detect circular definitions
4. **Z3 Integration**: Seamless integration with Z3 solver for atomic propositions and constraint handling
5. **Theory Independence**: Provides a neutral framework that all theories can build upon

### Integration Context

The syntactic package serves as the bridge between:
- **User Input**: Human-readable logical formulas in infix notation
- **Semantic Evaluation**: Machine-processable structures for model checking
- **Theory Implementations**: Custom operators and evaluation rules

## Core Components

### atoms.py - Z3 Atomic Propositions

Provides the foundation for atomic propositions using Z3's sort system:

```python
from model_checker.syntactic import AtomSort, AtomVal

# AtomSort is the Z3 sort for all atomic propositions
atom_p = AtomVal(0)  # Creates constant "AtomSort!val!0"
atom_q = AtomVal(1)  # Creates constant "AtomSort!val!1"

# These atoms can be used in Z3 constraints
from z3 import Solver, sat
s = Solver()
s.add(atom_p != atom_q)
assert s.check() == sat
```

### sentence.py - Formula Representation

The `Sentence` class represents logical formulas with comprehensive metadata:

```python
from model_checker.syntactic import Sentence

# Create sentences from infix notation
atomic = Sentence("p")
negation = Sentence("\\neg p")
conjunction = Sentence("(p \\wedge q)")
complex = Sentence("((p \\rightarrow q) \\wedge (q \\rightarrow r))")

# Access parsed structure
print(atomic.prefix_sentence)      # ['p']
print(conjunction.prefix_sentence) # ['\\wedge', ['p'], ['q']]
print(conjunction.complexity)      # 1 (nesting depth)

# Sentence lifecycle phases:
# 1. Creation: Stores infix and converts to prefix
# 2. Type Update: Links to operator classes
# 3. Object Update: Links to semantic operators
# 4. Proposition Update: Builds evaluation proposition
```

### operators.py - Operator Base Classes

Defines the foundation for all logical operators:

```python
from model_checker.syntactic import Operator, DefinedOperator

# Primitive operator example
class Negation(Operator):
    name = "\\neg"
    arity = 1
    
    def true_at(self, world, sentence):
        """Negation is true when the negated sentence is false."""
        return self.semantics.false_at(world, sentence.arguments[0])
    
    def false_at(self, world, sentence):
        """Negation is false when the negated sentence is true."""
        return self.semantics.true_at(world, sentence.arguments[0])

# Defined operator example (expressed via other operators)
class Implication(DefinedOperator):
    name = "\\rightarrow"
    arity = 2
    
    def derived_definition(self, p, q):
        """p → q is defined as ¬p ∨ q"""
        return [Disjunction, [Negation, p], q]
```

### collection.py - Operator Registry

Manages all available operators for a theory:

```python
from model_checker.syntactic import OperatorCollection

# Create collection and add operators
collection = OperatorCollection()
collection.add_operator(Negation)
collection.add_operator([Conjunction, Disjunction])
collection.add_operator(Implication)

# Apply operators to parsed sentences
parsed = collection.apply_operator(["\\rightarrow", ["p"], ["q"]])
# Result: [Implication, [Const("p", AtomSort)], [Const("q", AtomSort)]]

# Access operators by name
neg_op = collection["\\neg"]
```

### syntax.py - Argument Processing

Orchestrates the complete parsing and validation pipeline:

```python
from model_checker.syntactic import Syntax

# Process logical argument
syntax = Syntax(
    infix_premises=["(p \\rightarrow q)", "(q \\rightarrow r)"],
    infix_conclusions=["(p \\rightarrow r)"],
    operator_collection=collection
)

# Access processed results
print(len(syntax.all_sentences))    # Total unique sentences found
print(len(syntax.sentence_letters)) # Atomic propositions used
print(syntax.premises[0].operator)  # Linked operator instance

# Automatic validation includes:
# - Operator dependency checking
# - Circular definition detection
# - Sentence structure validation
```

## Usage Patterns

### Basic Theory Integration

```python
# 1. Define theory operators
class MyTheoryNegation(Operator):
    name = "\\neg"
    arity = 1
    # ... implementation ...

# 2. Build operator collection
operators = OperatorCollection([
    MyTheoryNegation,
    MyTheoryConjunction,
    MyTheoryImplication
])

# 3. Parse user input
syntax = Syntax(
    infix_premises=user_premises,
    infix_conclusions=user_conclusions,
    operator_collection=operators
)

# 4. Pass to semantic evaluation
model = ModelConstraints(syntax, semantics)
```

### Advanced Operator Definition

```python
# Multi-level defined operator
class Biconditional(DefinedOperator):
    name = "\\leftrightarrow"
    arity = 2
    
    def derived_definition(self, p, q):
        """p ↔ q is (p → q) ∧ (q → p)"""
        return [Conjunction,
                [Implication, p, q],
                [Implication, q, p]]

# Operator with custom printing
class Modal(Operator):
    name = "\\Box"
    arity = 1
    
    def print_method(self, sentence, world, indent, colors):
        """Custom visualization for modal evaluation."""
        self.print_over_worlds(
            sentence, world, 
            self.get_accessible_worlds(world),
            indent, colors
        )
```

### Formula Analysis

```python
# Analyze formula structure
def analyze_formula(formula_str):
    sent = Sentence(formula_str)
    
    print(f"Formula: {sent.name}")
    print(f"Complexity: {sent.complexity}")
    print(f"Prefix form: {sent.prefix_sentence}")
    
    # Recursively analyze subformulas
    if sent.original_arguments:
        for arg in sent.original_arguments:
            analyze_formula(arg)

# Extract all operators used
def get_operators_used(syntax):
    operators = set()
    for sentence in syntax.all_sentences.values():
        if sentence.operator:
            operators.add(sentence.operator.name)
    return operators
```

## Technical Architecture

### Design Patterns

1. **Lifecycle Pattern**: Sentences progress through well-defined update phases
2. **Registry Pattern**: OperatorCollection provides centralized operator management
3. **Visitor Pattern**: Operators implement methods called during evaluation
4. **Factory Pattern**: Operator classes instantiated with semantics injection

### Key Design Decisions

1. **Prefix Notation Internal Representation**:
   - Simplifies recursive processing
   - Eliminates precedence ambiguity
   - Natural for tree-based evaluation

2. **Separate Type and Object Phases**:
   - Type phase links to operator classes
   - Object phase links to operator instances
   - Enables late binding of semantics

3. **Defined Operator Validation**:
   - Arity checking ensures consistency
   - Dependency tracking prevents circular definitions
   - Compile-time validation reduces runtime errors

### Performance Considerations

- **Sentence Caching**: Identical subformulas share sentence objects
- **Lazy Evaluation**: Propositions built only when needed
- **Efficient Parsing**: Single-pass tokenization and parsing
- **Z3 Integration**: Direct use of Z3 sorts avoids conversions

## Extension Guidelines

### Adding New Operators

1. **Primitive Operators**: Inherit from `Operator` and implement semantic methods
2. **Defined Operators**: Inherit from `DefinedOperator` and provide `derived_definition`
3. **Register with Collection**: Add to theory's operator collection
4. **Test Thoroughly**: Ensure parsing, evaluation, and printing work correctly

### Custom Sentence Processing

```python
# Extend Sentence for special handling
class TheorySentence(Sentence):
    def __init__(self, infix_sentence, theory_context):
        super().__init__(infix_sentence)
        self.theory_context = theory_context
    
    def update_theory_specific(self):
        """Add theory-specific processing."""
        # Custom logic here
```

### Validation Extensions

```python
# Add custom validation to Syntax
class TheorySyntax(Syntax):
    def theory_validation(self):
        """Perform theory-specific validation."""
        super().circularity_check(self.operator_collection)
        # Add custom checks
        self.validate_modal_depth()
        self.check_operator_compatibility()
```

## Integration with Theories

Each theory builds upon the syntactic package:

1. **Define Custom Operators**: Create operator classes with theory-specific semantics
2. **Build Operator Collection**: Register all operators for the theory
3. **Process Arguments**: Use Syntax to parse and validate formulas
4. **Evaluate Models**: Pass processed syntax to semantic components

Example theory integration:

```python
# In theory's operators.py
from model_checker.syntactic import Operator, OperatorCollection

class TheoryNegation(Operator):
    name = "\\neg"
    arity = 1
    # Theory-specific implementation

# In theory's main module
def create_operator_collection():
    return OperatorCollection([
        TheoryNegation,
        TheoryConjunction,
        # ... other operators
    ])
```

## Testing

The syntactic package includes comprehensive tests:

```bash
# Run all syntactic tests
pytest src/model_checker/syntactic/tests/ -v

# Run specific test modules
pytest src/model_checker/syntactic/tests/test_sentence.py -v
pytest src/model_checker/syntactic/tests/test_operators.py -v

# Test integration with theories
for theory in logos bimodal exclusion imposition; do
    pytest src/model_checker/theory_lib/$theory/tests/test_*operators*.py -v
done
```

### Test Coverage

- **atoms.py**: Z3 sort creation, atom uniqueness, constraint integration
- **sentence.py**: Parsing, prefix/infix conversion, update phases
- **operators.py**: Base class functionality, arity validation, printing methods
- **collection.py**: Registration, lookup, operator application
- **syntax.py**: Full pipeline, circular dependency detection, validation

## References

### Academic Background

The syntactic framework draws from:
- **Formal Logic**: Standard notation and operator definitions
- **Programming Language Theory**: Parser design and AST construction
- **Model Checking**: Formula representation for verification

### Related Documentation

- [Theory Library](../theory_lib/README.md) - How theories use the syntactic package
- [Model Package](../models/README.md) - Semantic evaluation of parsed formulas
- [Utils Package](../utils/README.md) - Supporting utilities for parsing

### Implementation Notes

- Uses Z3 4.8+ for atomic proposition handling
- Supports Unicode mathematical symbols (∧, ∨, ¬, →, ↔, □, ◇)
- Thread-safe for concurrent theory evaluation
- No external dependencies beyond Z3

---

[← Back to ModelChecker](../README.md) | [Operators Guide →](operators.py) | [Theory Integration →](../theory_lib/README.md)