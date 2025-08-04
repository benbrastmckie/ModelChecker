# Unicode Character Guidelines

[← Examples Structure](EXAMPLES_STRUCTURE.md) | [Back to Maintenance](README.md) | [Documentation Standards →](DOCUMENTATION_STANDARDS.md)

## Overview

Unicode characters (∧, ∨, ¬, □, ◇, →, ↔, etc.) are **ONLY** permitted in comments and documentation. They must **NEVER** be used in code that the ModelChecker parser processes.

## Parser Requirements

The ModelChecker parser expects LaTeX notation exclusively. Unicode characters in formulas or operator definitions will cause parsing errors.

```python
# CORRECT - LaTeX in code, Unicode in comments
class Negation(Operator):
    """Negation operator (¬) for logical negation."""
    def __init__(self):
        super().__init__("\\neg", 1)  # LaTeX for parser

# INCORRECT - Unicode in operator definition
class Negation(Operator):
    def __init__(self):
        super().__init__("¬", 1)  # WRONG: Parser cannot read this
```

## Formula Notation

```python
# CORRECT - LaTeX notation in formulas
formula = "(A \\wedge B)"

# INCORRECT - Unicode in formulas  
formula = "A ∧ B"  # WRONG: Parser expects LaTeX
```

## Documentation Symbol Standards

When documenting operators in README files, show both LaTeX command and Unicode display:

Format: `\\equiv` (displayed as ≡)

### Preferred Unicode Symbols

- Double arrows: Use ⟹ (U+27F9) not ⇒ (U+21D2)
- Less-than-or-equal: Use ≤ (U+2264)
- Square subset: Use ⊑ (U+2291)

### Constitutive Logic Symbols

| LaTeX | Unicode | Name | Usage |
|-------|---------|------|-------|
| `\\equiv` | ≡ | IDENTICAL TO | Identity operator |
| `\\leq` | ≤ | LESS-THAN OR EQUAL TO | Ground operator |
| `\\sqsubseteq` | ⊑ | SQUARE IMAGE OF OR EQUAL TO | Essence operator |
| `\\preceq` | ⪯ | PRECEDES ABOVE SINGLE-LINE EQUALS SIGN | Relevance operator |
| `\\Rightarrow` | ⟹ | LONG RIGHTWARDS DOUBLE ARROW | Reduction operator |

## LaTeX Notation Reference

| Operator      | Unicode (docs only) | LaTeX (code)             | Description          |
|---------------|---------------------|--------------------------|----------------------|
| Negation      | ¬                   | `\\neg`                  | Logical NOT          |
| Conjunction   | ∧                   | `\\wedge`                | Logical AND          |
| Disjunction   | ∨                   | `\\vee`                  | Logical OR           |
| Implication   | →                   | `\\rightarrow`           | Material conditional |
| Biconditional | ↔                   | `\\leftrightarrow`       | If and only if       |
| Necessity     | □                   | `\\Box`                  | Modal necessity      |
| Possibility   | ◇                   | `\\Diamond`              | Modal possibility    |
| Counterfactual| ⥽                   | `\\boxright`             | Counterfactual       |
| Future        | ⏵                   | `\\future`               | Temporal future      |
| Past          | ⏴                   | `\\past`                 | Temporal past        |
| Top           | ⊤                   | `\\top`                  | Logical truth        |
| Bottom        | ⊥                   | `\\bot`                  | Logical falsehood    |

## File Encoding Requirements

- **UTF-8 ENCODING**: All files must use UTF-8 encoding without BOM
- **NO CONTROL CHARACTERS**: Exclude non-printable control characters
- **UNICODE VALIDATION**: Verify symbols display correctly before finalizing

## Quality Assurance

```bash
# Check for non-printable characters
grep -n '[^[:print:][:space:]]' filename

# Verify UTF-8 encoding
file -i filename  # Should show: charset=utf-8
```

---

[← Examples Structure](EXAMPLES_STRUCTURE.md) | [Back to Maintenance](README.md) | [Documentation Standards →](DOCUMENTATION_STANDARDS.md)