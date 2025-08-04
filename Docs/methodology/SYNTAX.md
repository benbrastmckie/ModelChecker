# Syntax: Language-Agnostic AST Conversion

[← Builder Pattern](BUILDER.md) | [Back to Methodology](README.md) | [Semantics Pipeline →](SEMANTICS.md)

## Table of Contents

1. [Introduction](#introduction)
2. [Parsing Overview](#parsing-overview)
   - [Language-Agnostic Design](#language-agnostic-design)
   - [Operator Conventions](#operator-conventions)
   - [LaTeX Standards](#latex-standards)
3. [String to AST Conversion](#string-to-ast-conversion)
   - [Tokenization Process](#tokenization-process)
   - [Prefix Notation Conversion](#prefix-notation-conversion)
   - [Complexity Calculation](#complexity-calculation)
   - [Error Handling](#error-handling)
4. [Sentence Class Structure](#sentence-class-structure)
   - [Sentence Attributes](#sentence-attributes)
   - [Lifecycle Phases](#lifecycle-phases)
   - [Recursive Building](#recursive-building)
   - [Dictionary Management](#dictionary-management)
5. [Operator Collection System](#operator-collection-system)
   - [OperatorCollection Class](#operatorcollection-class)
   - [Operator Registration](#operator-registration)
   - [Type Resolution](#type-resolution)
   - [Primitive vs Defined](#primitive-vs-defined)
6. [Syntax Class Orchestration](#syntax-class-orchestration)
   - [Sentence Dictionary Building](#sentence-dictionary-building)
   - [Circularity Checking](#circularity-checking)
   - [Atomic Letter Extraction](#atomic-letter-extraction)
   - [Performance Considerations](#performance-considerations)
7. [Code Examples](#code-examples)
8. [References](#references)

## Introduction

The syntax module provides the foundation for converting logical formulas from human-readable infix notation to machine-processable Abstract Syntax Trees (ASTs) using list-based prefix notation. This conversion is language-agnostic, meaning it works without prior knowledge of specific operators, allowing the framework to support arbitrary logical languages and operator definitions.

The parsing pipeline transforms strings like `"(A \\wedge B)"` into structured representations like `["\\wedge", "A", "B"]`, enabling systematic processing by the semantic evaluation engine. This approach separates syntactic structure from semantic interpretation, allowing the same parsing logic to work across different logical theories.

## Parsing Overview

### Language-Agnostic Design

The parser operates without a predefined operator dictionary, discovering operators during parsing through structural analysis:

Parser recognizes three token types:
1. Atomic sentences: `isalnum()` → "A", "B", "p1"
2. LaTeX operators: `startswith("\\")` → "\\wedge", "\\Box", "\\rightarrow"  
3. Parentheses: "(" and ")" for grouping binary operators

This design allows theories to define custom operators without modifying the parser, supporting extensibility and theory-specific languages.

### Operator Conventions

The framework follows consistent conventions for operator representation:

```python
# Binary operators require parentheses
"(A \\wedge B)"     # Conjunction
"(p \\rightarrow q)" # Implication
"(\\Box A \\vee B)"  # Mixed modal and propositional

# Unary operators use prefix notation without parentheses
"\\neg A"           # Negation
"\\Box p"           # Necessity
"\\Diamond (A \\wedge B)" # Possibility of conjunction

# Nullary operators (constants)
"\\top"             # Tautology
"\\bot"             # Contradiction
```

### LaTeX Standards

All operators use LaTeX notation with double backslashes in code:

```python
# Standard logical operators
"\\wedge"     # ∧ (conjunction)
"\\vee"       # ∨ (disjunction)  
"\\neg"       # ¬ (negation)
"\\rightarrow" # → (implication)
"\\leftrightarrow" # ↔ (biconditional)

# Modal operators
"\\Box"       # □ (necessity)
"\\Diamond"   # ◇ (possibility)

# Theory-specific operators
"\\boxright"  # ⊞→ (might counterfactual)
"\\constitutes" # ⊜ (constitution)
```

## String to AST Conversion

### Tokenization Process

The `parse_expression()` function in `utils.py` handles the core parsing logic:

```python
def parse_expression(tokens):
    """Parses tokens into prefix notation with complexity tracking."""
    if not tokens:
        raise ValueError("Empty token list")
    
    token = tokens.pop(0)
    
    # Binary operator case (parentheses)
    if token == "(":
        closing = tokens.pop()
        if closing != ")":
            raise SyntaxError("Missing closing parenthesis")
        operator, left, right = op_left_right(tokens)
        left_arg, left_comp = parse_expression(left)
        right_arg, right_comp = parse_expression(right)
        complexity = left_comp + right_comp + 1
        return [operator, left_arg, right_arg], complexity
    
    # Atomic sentence
    if token.isalnum():
        return [token], 0
    
    # LaTeX operator (including nullary like \top, \bot)
    elif token.startswith("\\"):
        if token in {"\\top", "\\bot"}:
            return [token], 0
        arg, comp = parse_expression(tokens)
        return [token, arg], comp + 1
```

### Prefix Notation Conversion

The conversion process transforms infix expressions to prefix notation:

```python
# Tokenization splits on whitespace with parenthesis handling
# "(A \\wedge B)" → ["(", "A", "\\wedge", "B", ")"]

# op_left_right extracts components
# ["A", "\\wedge", "B"] → operator="\\wedge", left=["A"], right=["B"]

# Recursive parsing builds prefix tree
# left=["A"] → ["A"], complexity=0
# right=["B"] → ["B"], complexity=0
# result → ["\\wedge", ["A"], ["B"]], complexity=1
```

### Complexity Calculation

Complexity measures the nesting depth of formulas:

Atomic sentences have complexity 0:
- `"A"` → complexity = 0

Each operator adds 1 to maximum argument complexity:
- `"\\neg A"` → complexity = 0 + 1 = 1
- `"(A \\wedge B)"` → complexity = max(0, 0) + 1 = 1
- `"\\Box (A \\wedge B)"` → complexity = 1 + 1 = 2
- `"((A \\wedge B) \\rightarrow \\neg C)"` → complexity = max(1, 1) + 1 = 2

### Error Handling

The parser provides detailed error messages for common issues:

```python
# Empty tokens
# parse_expression([]) → ValueError("Empty token list")

# Unbalanced parentheses
# "(A \\wedge B" → SyntaxError("Missing closing parenthesis")
# "A \\wedge B)" → ValueError("Unbalanced parentheses")

# Missing arguments
# "\\wedge B" → ValueError("Empty token list after operator \\wedge")
# "(A \\wedge )" → ValueError("Expected argument after operator \\wedge")

# Invalid operators
# "A & B" → Operator "&" not found in collection (later stage)
```

## Sentence Class Structure

### Sentence Attributes

The Sentence class encapsulates all information about a logical formula:

```python
class Sentence:
    def __init__(self, infix_sentence):
        # Original and parsed representations
        self.name = infix_sentence              # "(A \\wedge B)"
        self.prefix_sentence = ...              # ["\\wedge", "A", "B"]
        self.complexity = ...                   # 1
        
        # Operator and argument tracking (before type update)
        self.original_operator = ...            # "\\wedge" (string)
        self.original_arguments = ...           # [Sentence("A"), Sentence("B")]
        
        # After type update (in Syntax)
        self.operator = ...                     # AndOperator class
        self.arguments = ...                    # Updated sentence objects
        self.sentence_letter = ...              # Const("A", AtomSort) if atomic
        
        # After proposition update (in ModelStructure)
        self.proposition = ...                  # LogosProposition instance
```

### Lifecycle Phases

Sentences undergo four update phases during processing:

```python
# Phase 1: Creation (in __init__)
sentence = Sentence("(A \\wedge B)")
# Creates prefix notation and extracts structure

# Phase 2: Type Update (in Syntax.initialize_sentences)
sentence.update_types(operator_collection)
# Links operator strings to operator classes
# Handles defined operator derivation

# Phase 3: Object Update (in ModelConstraints.__init__)
sentence.update_objects(model_constraints)
# Links operator classes to semantic instances

# Phase 4: Proposition Update (in ModelStructure.interpret)
sentence.update_proposition(model_structure)
# Creates proposition for evaluation
```

### Recursive Building

Complex sentences are built recursively from their components:

Building "(A \\wedge B) \\rightarrow C":
1. Create `Sentence("(A \\wedge B) \\rightarrow C")`
2. Parse to `["\\rightarrow", ["\\wedge", "A", "B"], "C"]`
3. Recursively create:
   - `Sentence("(A \\wedge B)")`
     - `Sentence("A")`
     - `Sentence("B")`
   - `Sentence("C")`
4. Store in `all_sentences` dictionary

### Dictionary Management

The Syntax class maintains a dictionary of all unique sentences:

```python
# all_sentences prevents duplicate sentence objects
all_sentences = {
    "A": Sentence("A"),
    "B": Sentence("B"),
    "C": Sentence("C"),
    "(A \\wedge B)": Sentence("(A \\wedge B)"),
    "(A \\wedge B) \\rightarrow C": Sentence("(A \\wedge B) \\rightarrow C")
}

# Enables efficient reuse of sentence objects
if infix_sentence in all_sentences:
    return all_sentences[infix_sentence]
```

## Operator Collection System

### OperatorCollection Class

OperatorCollection serves as a registry for all available operators:

```python
class OperatorCollection:
    def __init__(self, *operators):
        self.operator_dictionary = {}  # Maps names to classes
        
    def add_operator(self, operator):
        """Add operator class to collection."""
        if operator.name in self.operator_dictionary:
            return  # Skip duplicates
        self.operator_dictionary[operator.name] = operator
```

### Operator Registration

Operators are registered by their LaTeX names:

```python
# Create collection
operators = OperatorCollection()

# Add individual operators
operators.add_operator(AndOperator)      # name = "\\wedge"
operators.add_operator(NegationOperator) # name = "\\neg"

# Add multiple operators
operators.add_operator([
    BoxOperator,        # name = "\\Box"
    DiamondOperator,    # name = "\\Diamond"
    ImpliesOperator     # name = "\\rightarrow"
])

# Merge collections
modal_operators = OperatorCollection(BoxOperator, DiamondOperator)
operators.add_operator(modal_operators)
```

### Type Resolution

The `apply_operator()` method converts parsed sentences to typed representations:

```python
def apply_operator(self, prefix_sentence):
    """Convert string operators to operator classes."""
    if len(prefix_sentence) == 1:
        atom = prefix_sentence[0]
        if atom in {"\\top", "\\bot"}:
            return [self[atom]]  # Extremal operator class
        if atom.isalnum():
            return [Const(atom, AtomSort)]  # Z3 constant
            
    op, arguments = prefix_sentence[0], prefix_sentence[1:]
    activated = [self.apply_operator(arg) for arg in arguments]
    activated.insert(0, self[op])  # Operator class at front
    return activated

# Example transformation
["\\wedge", "A", "B"] → [AndOperator, Const("A", AtomSort), Const("B", AtomSort)]
```

### Primitive vs Defined

Operators can be primitive or defined in terms of others:

```python
# Primitive operator
class BoxOperator(Operator):
    name = "\\Box"
    arity = 1
    primitive = True
    
    def true_at(self, world, sentence, model):
        # Direct semantic implementation
        ...

# Defined operator
class DiamondOperator(DefinedOperator):
    name = "\\Diamond"
    arity = 1
    primitive = False
    
    def derived_definition(self, arg):
        # ◇A ≡ ¬□¬A
        return ["\\neg", ["\\Box", ["\\neg", arg]]]
```

## Syntax Class Orchestration

### Sentence Dictionary Building

The Syntax class builds a comprehensive dictionary of all sentences:

```python
class Syntax:
    def initialize_sentences(self, infix_sentences):
        """Build dictionary of all sentences and subsentences."""
        
        def build_sentence(infix_sentence):
            # Check cache first
            if infix_sentence in self.all_sentences:
                return self.all_sentences[infix_sentence]
                
            # Create new sentence
            sentence = Sentence(infix_sentence)
            self.all_sentences[sentence.name] = sentence
            
            # Process atomic sentences
            if sentence.original_arguments is None:
                if sentence.name.isalnum():
                    self.sentence_letters.append(sentence)
                return sentence
                
            # Recursively build arguments
            for infix_arg in sentence.original_arguments:
                sentence_arg = build_sentence(infix_arg)
                sentence_arguments.append(sentence_arg)
```

### Circularity Checking

Syntax validates that defined operators don't have circular dependencies:

```python
def circularity_check(self, operator_collection):
    """Detect circular dependencies in operator definitions."""
    dependency_graph = {}
    
    # Build dependency graph
    for operator_class in operator_collection.values():
        if not operator_class.primitive:
            # Get dependencies from derived_definition
            dummy_args = [None] * operator_class.arity
            definition = operator_class.derived_definition(*dummy_args)
            dependencies = extract_operators(definition)
            dependency_graph[operator_class] = dependencies
    
    # Depth-first search for cycles
    def dfs(current):
        if current in recursion_stack:
            cycle = " -> ".join(op.name for op in recursion_stack)
            raise RecursionError(f"Circular definition: {cycle}")
        recursion_stack.append(current)
        for dependent in dependency_graph.get(current, set()):
            dfs(dependent)
        recursion_stack.remove(current)
```

### Atomic Letter Extraction

Syntax identifies all atomic sentence letters for model construction:

```python
# During sentence building
if sentence.name.isalnum():
    self.sentence_letters.append(sentence)

# Results in list of atomic sentences
sentence_letters = [
    Sentence("A"),
    Sentence("B"), 
    Sentence("C"),
    Sentence("p1"),
    Sentence("q")
]

# Used for Z3 variable creation
for letter in sentence_letters:
    letter.sentence_letter = Const(letter.name, AtomSort)
```

### Performance Considerations

The syntax module optimizes performance through caching and early validation:

```python
# Sentence caching prevents exponential blowup
# "(A \\wedge B) \\vee (A \\wedge B)" creates only one "(A \\wedge B)" object

# Complexity tracking enables optimization
# High complexity → potential timeout → increase N cautiously

# Early syntax validation prevents wasted computation
# Invalid syntax caught before expensive Z3 operations

# Operator collection validates arity matches
# Prevents runtime errors during evaluation
```

## Code Examples

### Complete Tokenization Example

```python
from model_checker.utils import parse_expression

# Input string
infix = "(A \\wedge B) \\rightarrow C"

# Tokenization
tokens = infix.replace("(", " ( ").replace(")", " ) ").split()
# Result: ["(", "A", "\\wedge", "B", ")", "\\rightarrow", "C"]

# Parse to prefix
prefix, complexity = parse_expression(tokens)
# Result: ["\\rightarrow", ["\\wedge", "A", "B"], "C"], complexity=2
```

### Type Application Example

```python
from model_checker.syntactic import OperatorCollection, Sentence

# Create operator collection
operators = OperatorCollection()
operators.add_operator(AndOperator)
operators.add_operator(ImpliesOperator)

# Create sentence
sentence = Sentence("(A \\wedge B) \\rightarrow C")

# Update types
sentence.update_types(operators)

# Results
sentence.operator           # ImpliesOperator class
sentence.arguments[0]       # Sentence("(A \\wedge B)")
sentence.arguments[0].operator  # AndOperator class
```

### Defined Operator Resolution

```python
# Define material conditional as ¬A ∨ B
class MaterialConditional(DefinedOperator):
    name = "\\implies"
    arity = 2
    primitive = False
    
    def derived_definition(self, A, B):
        return ["\\vee", ["\\neg", A], B]

# Parse "A \\implies B"
sentence = Sentence("A \\implies B")
sentence.update_types(operators)

# Original operator is MaterialConditional
# Derived operator chain: OrOperator(NegationOperator(A), B)
```

### Error Handling Examples

```python
# Missing closing parenthesis
try:
    tokens = ["(", "A", "\\wedge", "B"]
    parse_expression(tokens)
except SyntaxError as e:
    print(e)  # "The sentence ['A', '\\wedge', 'B'] is missing a closing parenthesis."

# Empty argument
try:
    tokens = ["\\neg", ")"]
    parse_expression(tokens)
except ValueError as e:
    print(e)  # "Empty token list after operator \\neg"

# Unbalanced parentheses
try:
    tokens = ["A", "\\wedge", "B", ")"]
    parse_expression(tokens)
except ValueError as e:
    print(e)  # "Unbalanced parentheses for the tokens..."
```

### Complete Syntax Pipeline

```python
from model_checker.syntactic import Syntax, OperatorCollection
from model_checker.theory_lib.logos import LogosOperatorRegistry

# Setup
registry = LogosOperatorRegistry()
registry.load_subtheories(['modal'])
operators = registry.operators

# Define logical argument
premises = ["\\Box (A \\wedge B)"]
conclusions = ["\\Box A \\wedge \\Box B"]

# Create syntax object
syntax = Syntax(premises, conclusions, operators)

# Results
print(f"All sentences: {len(syntax.all_sentences)}")  # 7 unique sentences
print(f"Atomic letters: {[s.name for s in syntax.sentence_letters]}")  # ["A", "B"]
print(f"Premise complexity: {syntax.premises[0].complexity}")  # 2
```

## References

### Implementation Files
- `model_checker/utils.py` - Contains `parse_expression()` function
- `model_checker/syntactic.py` - Sentence, Operator, and Syntax classes
- `model_checker/theory_lib/*/operators.py` - Theory-specific operators

### Related Documentation
- [Builder Pattern](BUILDER_PATTERN.md) - How syntax fits in the pipeline
- [Semantics Pipeline](SEMANTICS.md) - How parsed sentences become constraints
- [API Reference](../../Code/docs/API_REFERENCE.md) - Detailed class documentation

---

[← Builder Pattern](BUILDER.md) | [Back to Methodology](README.md) | [Semantics Pipeline →](SEMANTICS.md)