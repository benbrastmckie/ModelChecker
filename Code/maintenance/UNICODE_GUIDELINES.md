# Unicode Guidelines for Code

[← Version Control](VERSION_CONTROL.md) | [Back to Maintenance](README.md) | [Code Standards →](CODE_STANDARDS.md)

## Overview

This document defines Unicode character usage standards for **code files** in the ModelChecker framework. Unicode characters (∧, ∨, ¬, □, ◇, →, ↔, etc.) are **NEVER** permitted in code that the ModelChecker parser processes.

For Unicode usage in documentation, see [Docs/maintenance/UNICODE_GUIDELINES.md](../../Docs/maintenance/UNICODE_GUIDELINES.md).

## Critical Parser Requirements

The ModelChecker parser expects **LaTeX notation exclusively**. Unicode characters in formulas, operator definitions, or any parsed code will cause parsing errors.

```python
# CORRECT - LaTeX in code, Unicode only in comments
class Negation(Operator):
    """Negation operator (¬) for logical negation."""
    def __init__(self):
        super().__init__("\\neg", 1)  # LaTeX for parser

# INCORRECT - Unicode in operator definition
class Negation(Operator):
    def __init__(self):
        super().__init__("¬", 1)  # WRONG: Parser cannot read this
```

## Formula Notation in Code

### Always Use LaTeX

```python
# CORRECT - LaTeX notation in all formulas
MODAL_TH_1_premises = ["\\Box (A \\rightarrow B)", "\\Box A"]
MODAL_TH_1_conclusions = ["\\Box B"]

# INCORRECT - Unicode in formulas  
bad_premises = ["□ (A → B)", "□ A"]  # WRONG: Parser expects LaTeX
```

### Common LaTeX Commands

| Operator | LaTeX Code | Usage in Code |
|----------|------------|---------------|
| Negation | `\\neg` | `"\\neg A"` |
| Conjunction | `\\wedge` | `"(A \\wedge B)"` |
| Disjunction | `\\vee` | `"(A \\vee B)"` |
| Implication | `\\rightarrow` | `"(A \\rightarrow B)"` |
| Biconditional | `\\leftrightarrow` | `"(A \\leftrightarrow B)"` |
| Necessity | `\\Box` | `"\\Box A"` |
| Possibility | `\\Diamond` | `"\\Diamond A"` |

## Unicode in Comments and Docstrings

Unicode is **permitted only** in:
- Python comments
- Docstrings
- Non-parsed text

```python
def validate_formula(formula: str) -> bool:
    """
    Validate a logical formula.
    
    Supports operators: ∧ (and), ∨ (or), ¬ (not), → (implies)
    
    Args:
        formula: LaTeX-formatted formula like "\\neg (A \\wedge B)"
    """
    # Check for valid LaTeX operators (not Unicode like ∧)
    return all(op in formula for op in ["\\wedge", "\\vee", "\\neg"])
```

## Code File Encoding Standards

### UTF-8 Requirements

```python
# -*- coding: utf-8 -*-
# All Python files must use UTF-8 encoding

# CORRECT - UTF-8 with LaTeX in code
formula = "\\Box (A \\rightarrow B)"  # Box (A → B)

# INCORRECT - Unicode in parsed strings
formula = "□ (A → B)"  # Parser will fail
```

### File Validation

```bash
# Verify UTF-8 encoding
file -i *.py  # Should show: charset=utf-8

# Check for Unicode in code (not comments)
# This should find NO matches in formula strings
grep -n '[□◇∧∨¬→↔]' *.py | grep -v '#'
```

## Common Mistakes to Avoid

### 1. Copy-Paste from Documentation

```python
# WRONG - Copied from README with Unicode
operators = {
    'and': '∧',      # NO! Use "\\wedge"
    'or': '∨',       # NO! Use "\\vee"  
    'not': '¬'       # NO! Use "\\neg"
}

# CORRECT - LaTeX for parser
operators = {
    'and': '\\wedge',
    'or': '\\vee',
    'not': '\\neg'
}
```

### 2. IDE Auto-Conversion

Some IDEs convert LaTeX to Unicode. Always verify:

```python
# IDE might convert this:
formula = "\\Box A"

# To this (WRONG):
formula = "□ A"

# Always check before committing!
```

### 3. String Formatting

```python
# WRONG - Unicode in f-string
error_msg = f"Invalid operator: {op} (should be →)"

# CORRECT - LaTeX in code, Unicode in message
error_msg = f"Invalid operator: {op} (should be \\rightarrow)"
# Or if displaying to user:
display_msg = f"Invalid operator: {op} (should be →)"  # OK in output
```

## Theory-Specific LaTeX

### Constitutive Logic

```python
# CORRECT - LaTeX notation
IDENTITY = "\\equiv"
ESSENCE = "\\sqsubseteq"  
GROUND = "\\leq"
RELEVANCE = "\\preceq"

# INCORRECT - Unicode
IDENTITY = "≡"  # WRONG for parser
```

### Custom Operators

When defining new operators:

```python
class CounterfactualOperator(Operator):
    def __init__(self):
        # CORRECT - LaTeX command
        super().__init__("\\boxright", 2)
        
        # NOT: super().__init__("⥽", 2)  # Unicode fails
```

## Quality Assurance Checklist

Before committing code:

1. **No Unicode in Formulas**: Search for Unicode characters in formula strings
2. **LaTeX Double Backslashes**: Ensure all LaTeX uses `\\` not single `\`
3. **Parser Testing**: Run examples through parser to verify
4. **Encoding Check**: Verify UTF-8 encoding without BOM

```bash
# Quick validation script
echo "Checking for Unicode in code..."
grep -n '[□◇∧∨¬→↔≡≤⊑⪯⟹]' *.py | grep -v '#' | grep -v '"""'

echo "Checking file encoding..."
file -i *.py | grep -v "charset=utf-8"
```

## Migration from Unicode

If you find Unicode in existing code:

```python
# Replace systematically
replacements = {
    '¬': '\\neg',
    '∧': '\\wedge',
    '∨': '\\vee',
    '→': '\\rightarrow',
    '↔': '\\leftrightarrow',
    '□': '\\Box',
    '◇': '\\Diamond'
}

# Apply to all formula strings
# But NOT to comments or docstrings
```

---

[← Version Control](VERSION_CONTROL.md) | [Back to Maintenance](README.md) | [Code Standards →](CODE_STANDARDS.md)