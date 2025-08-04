# Formula Formatting Standards

[← Back to Maintenance](README.md) | [Examples Structure →](EXAMPLES_STRUCTURE.md)

## Overview

This document specifies the required formatting for logical formulas throughout the ModelChecker codebase. Consistent formula formatting ensures parser compatibility and code readability.

## Capital Letters for Variables

Always use capital letters (A, B, C) instead of lowercase (p, q, r) for propositional variables.

```python
# CORRECT
premises = ["A", "(A \\rightarrow B)"]

# INCORRECT
premises = ["p", "(p \\rightarrow q)"]
```

## Binary Operator Parentheses

Formulas with binary main operators MUST have outer parentheses.

```python
# CORRECT - All binary operators need parentheses
formulas = [
    "(A \\wedge B)",          # Conjunction
    "(A \\vee B)",            # Disjunction
    "(A \\rightarrow B)",     # Implication
    "(A \\leftrightarrow B)", # Biconditional
    "(A \\boxright B)",       # Counterfactual
]

# INCORRECT - Missing parentheses
formula = "A \\rightarrow B"  # WRONG: Must be "(A \\rightarrow B)"
```

## Unary Operator Formatting

Formulas with unary main operators MUST NOT have outer parentheses.

```python
# CORRECT - Unary operators without outer parentheses
formulas = [
    "\\neg A",        # Negation
    "\\Box A",        # Necessity
    "\\Diamond A",    # Possibility
    "\\neg \\Box A",  # Complex unary
]

# INCORRECT - Unnecessary parentheses
formula = "(\\neg A)"  # WRONG: Should be "\\neg A"
```

## Nested Formula Rules

Apply parentheses based on the main operator at each level of nesting.

```python
# CORRECT - Proper nesting
formulas = [
    "\\neg (A \\wedge B)",                    # Negation of conjunction
    "(\\neg A \\vee \\neg B)",                # Disjunction of negations
    "\\Box (A \\rightarrow B)",               # Necessity of implication
    "(\\Box A \\rightarrow \\Box B)",         # Implication of necessities
    "\\neg \\Box \\neg A",                    # No parentheses for unary chain
]
```

## LaTeX Notation Requirements

Always use LaTeX notation in code, never Unicode characters.

```python
# CORRECT - LaTeX notation
operators = ["\\wedge", "\\vee", "\\neg", "\\Box", "\\Diamond"]

# INCORRECT - Unicode characters
operators = ["∧", "∨", "¬", "□", "◇"]  # WRONG: Parser expects LaTeX
```

## Common Formatting Errors

1. **Missing binary parentheses**: `A \\wedge B` should be `(A \\wedge B)`
2. **Extra unary parentheses**: `(\\neg A)` should be `\\neg A`
3. **Unicode in formulas**: `A ∧ B` should be `(A \\wedge B)`
4. **Lowercase variables**: `p \\rightarrow q` should be `(P \\rightarrow Q)` or `(A \\rightarrow B)`
5. **Inconsistent spacing**: Maintain consistent spacing around operators

## Parser Compatibility

The ModelChecker parser relies on these formatting rules. Deviations will cause parsing errors or unexpected behavior.

---

[← Back to Maintenance](README.md) | [Examples Structure →](EXAMPLES_STRUCTURE.md)