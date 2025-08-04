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

Key insights this design provides:
- **Theory Independence**: Parse any formula without knowing its operators beforehand
- **Structural Preservation**: Prefix notation maintains formula structure for semantic evaluation
- **Error Prevention**: Early syntax validation catches mistakes before expensive constraint generation
- **Performance Optimization**: Sentence caching prevents exponential blowup in complex formulas

For the complete pipeline context, see [Builder Pattern](BUILDER.md#complete-pipeline). For semantic interpretation of parsed formulas, see [Semantics Pipeline](SEMANTICS.md).

## Parsing Overview

### Language-Agnostic Design

The parser operates without a predefined operator dictionary, discovering operators during parsing through structural analysis:

The parser discovers operators through structural analysis:

```
┌───────────────────┐      ┌──────────────────┐      ┌──────────────────┐
│ Token Stream      │      │ Token Type       │      │ Parser Action    │
│ • "(A \\wedge B)" │ ───▶ │ • "(" → Binary   │ ───▶ │ • Extract op     │
│                   │      │ • "A" → Atomic   │      │ • Parse args     │
│                   │      │ • "\\wedge" → Op │      │ • Build AST      │
└───────────────────┘      └──────────────────┘      └──────────────────┘
```

Parser recognizes three token types:

1. **Atomic sentences**: `isalnum()` → "A", "B", "p1"
2. **LaTeX operators**: `startswith("\\")` → "\\wedge", "\\Box", "\\rightarrow"
3. **Parentheses**: "(" and ")" for grouping binary operators

This design allows theories to define custom operators without modifying the parser, supporting extensibility and theory-specific languages. The parser doesn't need an operator dictionary - it identifies operators by their LaTeX notation pattern.

### Operator Conventions

The framework follows consistent conventions for operator representation:

```python
# Binary operators require parentheses
"(A \\wedge B)"     # Conjunction - both A and B must be true
"(A \\rightarrow B)" # Implication - if A then B
"(\\Box A \\vee B)"  # Mixed modal and propositional

# Unary operators use prefix notation without parentheses
"\\neg A"           # Negation - not A
"\\Box A"           # Necessity - A is necessary
"\\Diamond (A \\wedge B)" # Possibility of conjunction

# Nullary operators (constants)
"\\top"             # Tautology - always true
"\\bot"             # Contradiction - always false
```

The parenthesis requirement for binary operators eliminates ambiguity: `A \\wedge B \\vee C` is invalid syntax, forcing explicit grouping as either `(A \\wedge B) \\vee C` or `A \\wedge (B \\vee C)`. This design choice trades convenience for clarity, preventing subtle precedence errors in complex formulas.

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

The double backslash convention ensures proper escaping in Python strings while maintaining compatibility with LaTeX documentation. Custom operators can use any valid LaTeX command - the parser treats all `\\name` patterns uniformly, enabling theory-specific vocabularies without framework modifications.

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

*Full implementation: [`model_checker/utils.py`](../../Code/src/model_checker/utils.py)*

This recursive algorithm elegantly handles arbitrary formula nesting. The key insight is that parentheses indicate binary operators (which consume the entire contents between them), while LaTeX operators are either unary (consuming the next expression) or nullary (consuming nothing). The complexity tracking happens naturally during recursion - each operator adds 1 to its arguments' maximum complexity, giving us a measure of formula depth for performance estimation.

### Prefix Notation Conversion

During prefix notation conversion, complex sentences in infix notation are decomposed recursively into their components:

**Example: Converting "(A ∧ B) → C" to prefix notation**

Infix input: `"((A \\wedge B) \\rightarrow C)"`
Prefix output: `["\\rightarrow", ["\\wedge", "A", "B"], "C"]`

```
Decomosing "((A \\wedge B) \\rightarrow C)":

┌─────────────────────────────────────────────────────────────────────────┐
│ Root: "((A \\wedge B) \\rightarrow C)"                                  │
│ • Infix: "((A \\wedge B) \\rightarrow C)"                               │
│ • Prefix: ["\\rightarrow", ["\\wedge", "A", "B"], "C"]                  │
│ • Main operator: \\rightarrow                                           │
│ • Complexity: 2                                                         │
└────────────┬────────────────────────────────────────────────────────────┘
             │ parse_expression() identifies binary operation
             │
    ┌────────┴──────────────────────────────────┬─────────────────────────┐
    ▼                                           ▼                         │
┌────────────────────────────────┐   ┌──────────────────────┐             │
│ Left arg: "(A \\wedge B)"      │   │ Right arg: "C"       │             │
│ • Prefix: ["\\wedge", "A", "B"]│   │ • Prefix: ["C"]      │             │
│ • Main operator: \\wedge       │   │ • Type: Atomic       │             │
│ • Complexity: 1                │   │ • Complexity: 0      │             │
└──────────┬─────────────────────┘   └──────────────────────┘             │
           │ parse_expression()                                           │
           │ sees parentheses                                             │
           │                                                              │
    ┌──────┴─────┬─────────┐                                              │
    ▼            ▼         │                                              │
┌─────────┐  ┌─────────┐   │ Sentence Creation Order:                     │
│ "A"     │  │ "B"     │   │ 1. Sentence("A")                             │
│ Atomic  │  │ Atomic  │   │ 2. Sentence("B")                             │
│ Comp: 0 │  │ Comp: 0 │   │ 3. Sentence("C")                             │
└─────────┘  └─────────┘   │ 4. Sentence("(A \\wedge B)")                 │
                           │ 5. Sentence("((A \\wedge B) \\rightarrow C)")│
                           └──────────────────────────────────────────────┘
```

The parsing process demonstrates the framework's language-agnostic design: the parser doesn't need to know what `\\wedge` or `\\rightarrow` mean semantically - it simply recognizes them as LaTeX operators and builds the appropriate tree structure. This separation allows the same parsing logic to handle classical propositional logic, modal logic, temporal logic, or any custom logical language you define. The prefix notation output directly maps to function application: `["\\rightarrow", ["\\wedge", "A", "B"], "C"]` represents `implies(and(A, B), C)`, making semantic evaluation straightforward.

This approach ensures each unique formula is created exactly once, preventing memory explosion in formulas with repeated subformulas like `((A \\wedge B) \\vee (A \\wedge B))`.

### Complexity Calculation

Complexity measures the maximum nesting depth of operators in a formula, helping predict solver performance.

```python
def calculate_complexity(prefix_sentence):
    """Recursively calculate formula complexity."""
    if len(prefix_sentence) == 1:
        # Atomic sentences and constants have complexity 0
        return 0
    
    operator = prefix_sentence[0]
    arguments = prefix_sentence[1:]
    
    # Calculate complexity of each argument
    arg_complexities = [calculate_complexity(arg) for arg in arguments]
    
    # Add 1 to the maximum argument complexity
    return max(arg_complexities) + 1

# Example: ["\\rightarrow", ["\\wedge", "A", "B"], ["\\neg", "C"]]
# Left arg: ["\\wedge", "A", "B"] → max(0, 0) + 1 = 1
# Right arg: ["\\neg", "C"] → 0 + 1 = 1
# Total: max(1, 1) + 1 = 2

# Examples with increasing complexity:
# "A" → 0 (atomic)
# "\\neg A" → 1 (one operator)
# "(A \\wedge B)" → 1 (one operator)
# "\\Box (A \\wedge B)" → 2 (nested operators)
# "((A \\wedge B) \\rightarrow \\neg C)" → 2 (max depth is 2)
# "\\Box \\Diamond (A \\wedge B)" → 3 (three nested operators)
```

The calculated complexity value is stored in `sentence.complexity` during initialization and used by the framework to estimate solving difficulty. Formulas with complexity > 5 typically require reduced state space (smaller N) or increased timeout settings. The recursive calculation mirrors the formula structure - each operator adds exactly 1 to its deepest argument's complexity, making the metric predictable and meaningful for performance tuning.

*See also: [`model_checker/syntactic.py#Sentence.__init__`](../../Code/src/model_checker/syntactic.py) for complexity calculation during parsing*

### Error Handling

The parser provides detailed error messages for common issues:

```python
# Empty tokens
parse_expression([])  # → ValueError("Empty token list")

# Unbalanced parentheses
"(A \\wedge B"  # → SyntaxError("Missing closing parenthesis")
"A \\wedge B)"  # → ValueError("Unbalanced parentheses")

# Missing arguments
"\\wedge B"     # → ValueError("Empty token list after operator \\wedge")
"(A \\wedge )"  # → ValueError("Expected argument after operator \\wedge")

# Invalid operators (caught later in type resolution)
"A & B"        # → Operator "&" not in collection and missing parentheses
```

Early syntax validation prevents wasted computation - it's better to fail fast with a clear error than to generate invalid constraints that produce confusing Z3 errors. The parser distinguishes between structural errors (parentheses) and semantic errors (unknown operators), handling each at the appropriate stage.

## Sentence Class Structure

### Sentence Attributes

The Sentence class encapsulates all information about a logical formula:

```python
class Sentence:
    def __init__(self, infix_sentence):
        # Original and parsed representations
        self.name = infix_sentence              # "(A \\wedge B)" - unique ID
        self.prefix_sentence = ...              # ["\\wedge", "A", "B"]
        self.complexity = ...                   # 1 - nesting depth

        # Operator and argument tracking (before type update)
        self.original_operator = ...            # "\\wedge" (string)
        self.original_arguments = ...           # ["A", "B"] (strings)

        # After type update (in Syntax)
        self.operator = ...                     # AndOperator class
        self.arguments = ...                    # [Sentence("A"), Sentence("B")]
        self.sentence_letter = ...              # Const("A", AtomSort) if atomic

        # After proposition update (in ModelStructure)
        self.proposition = ...                  # LogosProposition instance
```

*Full implementation: [`model_checker/syntactic.py`](../../Code/src/model_checker/syntactic.py)*

The Sentence class serves as a bridge between syntactic representation and semantic evaluation. Each phase adds the information needed by subsequent stages, maintaining clean separation between parsing, type resolution, and semantic interpretation.

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

Each phase progressively transforms the sentence from a string to a fully evaluable logical object. The separation allows different components to operate at their appropriate abstraction level: parsing knows nothing about semantics, type resolution knows nothing about specific theories, and proposition creation happens only when needed for evaluation. This staged approach enables the framework to support arbitrary logical theories without modifying the core parsing infrastructure.

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
    return all_sentences[infix_sentence]  # Reuse existing object
else:
    new_sentence = Sentence(infix_sentence)  # Create only if new
    all_sentences[infix_sentence] = new_sentence
```

Dictionary management provides two key benefits: memory efficiency (shared subformulas use the same object) and semantic consistency (identical formulas always map to the same sentence object, simplifying equality checking and constraint generation).

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

*Full implementation: [`model_checker/syntactic.py`](../../Code/src/model_checker/syntactic.py)*

OperatorCollection acts as a registry mapping LaTeX operator names to their implementation classes. The duplicate checking ensures consistent behavior - if multiple theories define the same operator, the first definition wins. This design allows theories to share common operators (like `\\wedge`) while defining their own specialized operators (like `\\boxright` for counterfactuals).

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

Operator registration supports flexible composition: individual operators can be added one at a time, in bulk via lists, or by merging entire collections. This pattern enables modular theory construction - base operators in one collection, modal extensions in another, theory-specific operators in a third. The framework automatically handles operator dependencies during semantic evaluation.

### Type Resolution

The `apply_operator()` method converts parsed sentences to typed representations:

```python
def apply_operator(self, prefix_sentence):
    """Convert string operators to operator classes."""
    if len(prefix_sentence) == 1:
        atom = prefix_sentence[0]
        if atom in {"\\top", "\\bot"}:  # Constants
            return [self[atom]]  # TopOperator or BotOperator
        if atom.isalnum():  # Atomic sentences
            return [Const(atom, AtomSort)]  # Z3 constant

    op, arguments = prefix_sentence[0], prefix_sentence[1:]
    activated = [self.apply_operator(arg) for arg in arguments]  # Recursive
    activated.insert(0, self[op])  # Operator class at position 0
    return activated

# Example transformation
["\\wedge", "A", "B"] → [AndOperator, Const("A", AtomSort), Const("B", AtomSort)]
```

Type resolution bridges the gap between syntactic strings and semantic classes. The Z3 constants created here (`Const("A", AtomSort)`) become the atomic building blocks for constraint generation - each represents a proposition that can be true or false at different evaluation points.

### Primitive vs Defined

Operators can be primitive or defined in terms of others:

```python
# Primitive operator - has direct semantic implementation
class BoxOperator(Operator):
    name = "\\Box"
    arity = 1
    primitive = True

    def true_at(self, world, sentence, model):
        # Direct semantic implementation
        # □A is true at w iff A is true at all accessible worlds
        return ForAll([v], Implies(R(w,v), sentence.true_at(v)))

# Defined operator - reduces to other operators
class DiamondOperator(DefinedOperator):
    name = "\\Diamond"
    arity = 1
    primitive = False

    def derived_definition(self, arg):
        # ◇A ≡ ¬□¬A (possible = not necessarily not)
        return ["\\neg", ["\\Box", ["\\neg", arg]]]
```

*See also: [`model_checker/syntactic.py`](../../Code/src/model_checker/syntactic.py) for base Operator classes*

The distinction matters for extensibility: new theories can add defined operators without modifying the core constraint generation engine. During type resolution, defined operators are expanded to their primitive constituents, ensuring all constraints ultimately reduce to primitive semantic operations.

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
                sentence_arg = build_sentence(infix_arg)  # Recursive call
                sentence_arguments.append(sentence_arg)
```

*Full implementation: [`model_checker/syntactic.py`](../../Code/src/model_checker/syntactic.py)*

The `build_sentence` function implements a memoized recursive descent through the formula structure. By checking the cache first (`all_sentences` dictionary), it ensures each unique subformula is processed exactly once. This optimization is crucial for formulas with repeated patterns - without memoization, a formula like `(P \\wedge Q) \\vee (P \\wedge Q) \\vee (P \\wedge Q)` would create multiple identical sentence objects, wasting memory and computation.

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
            dummy_args = [None] * operator_class.arity  # Placeholder args
            definition = operator_class.derived_definition(*dummy_args)
            dependencies = extract_operators(definition)  # Find operators used
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

Circularity checking prevents infinite loops during operator expansion. For example, if `\\Diamond` were defined as `\\neg \\Box \\neg` and `\\Box` as `\\neg \\Diamond \\neg`, the expansion would never terminate. This validation ensures all defined operators eventually reduce to primitives.

### Atomic Letter Extraction

Syntax identifies all atomic sentence letters for model construction:

```python
# During sentence building
if sentence.name.isalnum():
    self.sentence_letters.append(sentence)  # Collect atoms

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
    letter.sentence_letter = Const(letter.name, AtomSort)  # Z3 constant
```

Atomic letter extraction serves two purposes: it determines the propositional vocabulary for the model (what can be true/false) and creates the Z3 constants that anchor all constraints. These atoms become the foundation for evaluating complex formulas - every formula's truth ultimately reduces to the truth of its atomic constituents.

### Performance Considerations

The syntax module optimizes performance through caching and early validation:

```python
# 1. Sentence caching implementation
def build_sentence(self, infix_sentence):
    """Build or retrieve cached sentence object."""
    # Check cache first - O(1) lookup
    if infix_sentence in self.all_sentences:
        return self.all_sentences[infix_sentence]  # Reuse existing
    
    # Create new sentence only if needed
    sentence = Sentence(infix_sentence)
    self.all_sentences[sentence.name] = sentence
    return sentence

# Example impact: "((A \\wedge B) \\vee (A \\wedge B))" 
# Without cache: creates A, B, (A \\wedge B), A, B, (A \\wedge B), ((A \\wedge B) \\vee (A \\wedge B)) = 7 objects
# With cache: creates A, B, (A \\wedge B), ((A \\wedge B) \\vee (A \\wedge B)) = 4 objects

# 2. Early validation during parsing
def parse_expression(tokens):
    """Parse with immediate error detection."""
    if not tokens:
        raise ValueError("Empty token list")  # Fail fast
    
    token = tokens.pop(0)
    if token == "(":
        # Validate parentheses immediately
        if ")" not in tokens:
            raise SyntaxError("Missing closing parenthesis")
        # Continue parsing...

# 3. Complexity-based performance warnings
if sentence.complexity > 5:
    if settings.get('verbose'):
        print(f"Warning: Complexity {sentence.complexity} may be slow")
        print(f"Consider reducing N from {settings['N']} to 3")

# 4. Operator arity validation
def update_types(self, operator_collection):
    """Validate operator usage during type resolution."""
    operator_class = operator_collection[self.original_operator]
    expected_args = operator_class.arity
    actual_args = len(self.original_arguments)
    
    if expected_args != actual_args:
        raise ArityError(
            f"Operator {self.original_operator} expects {expected_args} "
            f"arguments, got {actual_args}"
        )
```

These optimizations compound: caching reduces memory usage, which speeds up Z3's internal operations, while early validation prevents the framework from building elaborate constraint systems for malformed inputs. The result is a system that handles complex formulas efficiently while failing fast on errors.

*Full implementation: [`model_checker/syntactic.py#Syntax`](../../Code/src/model_checker/syntactic.py)*

## Code Examples

### Complete Tokenization Example

```python
from model_checker.utils import parse_expression

# Input string
infix = "(A \\wedge B) \\rightarrow C"  # If A and B, then C

# Tokenization (add spaces around parentheses)
tokens = infix.replace("(", " ( ").replace(")", " ) ").split()
# Result: ["(", "A", "\\wedge", "B", ")", "\\rightarrow", "C"]

# Parse to prefix notation
prefix, complexity = parse_expression(tokens)
# Result: ["\\rightarrow", ["\\wedge", "A", "B"], "C"], complexity=2
# Structure: implication(conjunction(A, B), C)
```

The transformation from infix to prefix notation creates a structure that directly maps to semantic evaluation. The prefix form `["\\rightarrow", ["\\wedge", "A", "B"], "C"]` can be read as a function call: the implication operator applied to the conjunction of A and B as antecedent and C as consequent.

### Type Application Example

```python
from model_checker.syntactic import OperatorCollection, Sentence

# Create operator collection
operators = OperatorCollection()
operators.add_operator(AndOperator)      # name = "\\wedge"
operators.add_operator(ImpliesOperator)  # name = "\\rightarrow"

# Create sentence
sentence = Sentence("(A \\wedge B) \\rightarrow C")
# Before type update: operators are strings

# Update types - link strings to classes
sentence.update_types(operators)
# After: operators are class references

# Results show hierarchical structure
sentence.operator                # ImpliesOperator class (not string)
sentence.arguments[0]            # Sentence("(A \\wedge B)")
sentence.arguments[0].operator   # AndOperator class
sentence.arguments[1]            # Sentence("C")
```

Type resolution transforms the parse tree from a purely syntactic structure to a semantically-aware one. Each operator string is replaced with its corresponding class, enabling the operator to later generate its specific constraints through methods like `true_at()` and `extended_verify()`.

### Defined Operator Resolution

```python
# Define material conditional as ¬A ∨ B
class MaterialConditional(DefinedOperator):
    name = "\\implies"
    arity = 2
    primitive = False

    def derived_definition(self, A, B):
        # A ⊃ B ≡ ¬A ∨ B (false only when A true, B false)
        return ["\\vee", ["\\neg", A], B]

# Parse "A \\implies B"
sentence = Sentence("A \\implies B")
sentence.update_types(operators)

# Resolution process:
# 1. Parser sees "\\implies" operator
# 2. Type update finds MaterialConditional class
# 3. Since primitive=False, expands using derived_definition
# 4. Creates: OrOperator(NegationOperator(A), B)
# 5. All constraints generated from primitive operators
```

Defined operators provide a powerful abstraction mechanism. New logical connectives can be added without touching the constraint generation engine - they simply specify their definition in terms of existing operators. This enables rapid prototyping of new logical systems.

### Error Handling Examples

```python
# Missing closing parenthesis
try:
    tokens = ["(", "A", "\\wedge", "B"]  # Started with ( but no )
    parse_expression(tokens)
except SyntaxError as e:
    print(e)  # "The sentence ['A', '\\wedge', 'B'] is missing a closing parenthesis."

# Empty argument
try:
    tokens = ["\\neg", ")"]  # Negation needs an argument
    parse_expression(tokens)
except ValueError as e:
    print(e)  # "Empty token list after operator \\neg"

# Unbalanced parentheses  
try:
    tokens = ["A", "\\wedge", "B", ")"]  # Extra closing parenthesis
    parse_expression(tokens)
except ValueError as e:
    print(e)  # "Unbalanced parentheses for the tokens..."

# Wrong arity (caught during type resolution)
try:
    sentence = Sentence("\\Box A B")  # Box is unary, not binary
    sentence.update_types(operators)
except ArityError as e:
    print(e)  # "Operator \\Box expects 1 argument, got 2"
```

Robust error handling guides users to fix syntax errors quickly. The parser distinguishes between different error types: structural errors (parentheses), operator errors (wrong arity), and semantic errors (unknown operators). Each error includes enough context to identify and fix the problem.

### Complete Syntax Pipeline

```python
from model_checker.syntactic import Syntax, OperatorCollection
from model_checker.theory_lib.logos import LogosOperatorRegistry

# Setup
registry = LogosOperatorRegistry()
registry.load_subtheories(['modal'])  # Load only modal operators
operators = registry.operators  # Dict: name -> operator class

# Define logical argument (testing distributivity)
premises = ["\\Box (A \\wedge B)"]  # Necessarily (A and B)
conclusions = ["\\Box A \\wedge \\Box B"]  # (Necessarily A) and (Necessarily B)

# Create syntax object
syntax = Syntax(premises, conclusions, operators)
# At this point:
# - All formulas parsed to prefix notation
# - Sentence objects created and cached
# - Types resolved (operators linked to classes)
# - Ready for semantic constraint generation

# Results
print(f"All sentences: {len(syntax.all_sentences)}")  # 7 unique sentences
print(f"Atomic letters: {[s.name for s in syntax.sentence_letters]}")  # ["A", "B"]
print(f"Premise complexity: {syntax.premises[0].complexity}")  # 2
```

This pipeline demonstrates the complete syntax processing flow. The resulting `syntax` object contains all the structured information needed by the semantic engine to generate constraints. The separation ensures that syntax processing knows nothing about specific semantic theories - the same parsing works for classical logic, modal logic, or any custom theory.

## References

### Implementation Files

**Core Parsing and Syntax:**
- [`model_checker/utils.py`](../../Code/src/model_checker/utils.py) - Contains `parse_expression()` function and tokenization utilities
- [`model_checker/syntactic.py`](../../Code/src/model_checker/syntactic.py) - Sentence, Operator, OperatorCollection, and Syntax classes

**Theory-Specific Operators:**
- [`logos/subtheories/extensional/operators.py`](../../Code/src/model_checker/theory_lib/logos/subtheories/extensional/operators.py) - Basic logical operators (∧, ∨, ¬, →)
- [`logos/subtheories/modal/operators.py`](../../Code/src/model_checker/theory_lib/logos/subtheories/modal/operators.py) - Modal operators (□, ◇)
- [`logos/registry.py`](../../Code/src/model_checker/theory_lib/logos/registry.py) - LogosOperatorRegistry for dynamic loading

### Related Documentation

- [Builder Pattern](BUILDER.md) - How syntax fits in the pipeline
- [Semantics Pipeline](SEMANTICS.md) - How parsed sentences become constraints
- [API Reference](../../Code/docs/API_REFERENCE.md) - Detailed class documentation

---

[← Builder Pattern](BUILDER.md) | [Back to Methodology](README.md) | [Semantics Pipeline →](SEMANTICS.md)
