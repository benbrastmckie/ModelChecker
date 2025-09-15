# Unicode Guidelines for Documentation

[← Version Control](VERSION_CONTROL.md) | [Back to Maintenance](README.md) | [Documentation Standards →](DOCUMENTATION_STANDARDS.md)

## Overview

This document defines Unicode character usage standards for **documentation files** in the ModelChecker project. Unicode mathematical symbols (∧, ∨, ¬, □, ◇, →, ↔, etc.) are **encouraged** in documentation for clarity and readability.

For Unicode restrictions in code files, see [Code/maintenance/UNICODE_GUIDELINES.md](../../Code/maintenance/UNICODE_GUIDELINES.md).

## Documentation Symbol Standards

### When to Use Unicode

Unicode symbols should be used in documentation to:
- Improve readability for mathematical expressions
- Create clear visual distinction between operators
- Align with standard mathematical notation
- Enhance accessibility for non-programmers

```markdown
# RECOMMENDED - Unicode in documentation
The formula A ∧ B represents the conjunction of propositions A and B.
Modal necessity is expressed as □P (necessarily P).

# ALSO GOOD - Explaining both notations
The Box operator □ (written as `\Box` in code) represents necessity.
```

### Mathematical Symbol Reference

| Symbol | Unicode | Name | Usage in Documentation |
|--------|---------|------|------------------------|
| ∧ | U+2227 | Logical AND | Conjunction |
| ∨ | U+2228 | Logical OR | Disjunction |
| ¬ | U+00AC | NOT SIGN | Negation |
| → | U+2192 | RIGHTWARDS ARROW | Implication |
| ↔ | U+2194 | LEFT RIGHT ARROW | Biconditional |
| □ | U+25A1 | WHITE SQUARE | Modal necessity |
| ◇ | U+25C7 | WHITE DIAMOND | Modal possibility |
| ⊨ | U+22A8 | TRUE | Semantic entailment |
| ⊭ | U+22AD | NOT TRUE | Non-entailment |
| ∀ | U+2200 | FOR ALL | Universal quantifier |
| ∃ | U+2203 | THERE EXISTS | Existential quantifier |
| □→ | U+25A1 U+2192 | BOX ARROW | Would counterfactual |
| ◇→ | U+25C7 U+2192 | DIAMOND ARROW | Could counterfactual |
| ⊩⁺ | U+22A9 U+207A | VERIFY | Verification |
| ⊩⁻ | U+22A9 U+207B | FALSIFY | Falsification |

### Counterfactual Operators

For counterfactual conditionals, use these standardized symbols:

| Symbol | Unicode | Name | Usage |
|--------|---------|------|-------|
| □→ | U+25A1 U+2192 | Would counterfactual | "If it were the case that P, it would be that Q" |
| ◇→ | U+25C7 U+2192 | Could counterfactual | "If it were the case that P, it could be that Q" |

**Note**: Always use "would" and "could" terminology (not "must" and "might").

### Verification Operators

| Symbol | Unicode | Name | Usage |
|--------|---------|------|-------|
| ⊩⁺ | U+22A9 U+207A | Verify | Positive verification |
| ⊩⁻ | U+22A9 U+207B | Falsify | Negative verification/falsification |

### Constitutive Logic Symbols

For specialized theories, use these preferred symbols:

| Symbol | Unicode | LaTeX | Meaning |
|--------|---------|-------|---------|
| ≡ | U+2261 | `\equiv` | Identity |
| ≤ | U+2264 | `\leq` | Ground |
| ⊑ | U+2291 | `\sqsubseteq` | Essence |
| ⪯ | U+2AAF | `\preceq` | Relevance |
| ⟹ | U+27F9 | `\Rightarrow` | Reduction |

## Documentation Patterns

### Explaining Formulas

When documenting logical formulas:

```markdown
## Example: Modus Ponens

The inference rule can be expressed as:

**Premises:**
1. P → Q (if P then Q)
2. P (P is true)

**Conclusion:**
- Q (therefore Q)

In ModelChecker syntax, this would be written as:
```python
premises = ["(P \\rightarrow Q)", "P"]
conclusions = ["Q"]
```
```

### Operator Documentation

When documenting operators:

```markdown
## Necessity Operator (□)

The necessity operator □ (Box) expresses that a formula holds in all 
accessible possible worlds.

**Syntax**: `\Box` followed by a formula
**Example**: □P reads as "necessarily P"
**Code**: `"\\Box P"`

### Common Modal Axioms

- **K**: □(P → Q) → (□P → □Q)
- **T**: □P → P  
- **4**: □P → □□P
- **5**: ◇P → □◇P
```

### Theory Comparisons

Use Unicode for clear visual comparisons:

```markdown
## Theory Feature Comparison

| Theory | Conjunction | Implication | Modal Operators |
|--------|-------------|-------------|-----------------|
| Classical | A ∧ B | A → B | Not supported |
| Modal | A ∧ B | A → B | □A, ◇A |
| Relevance | A ∧ B | A → B (relevant) | Limited support |
```

## Code Example Documentation

When showing code examples in documentation, include both notations:

```markdown
## Creating a Modal Formula

To express "If P is necessary, then P is true" (axiom T):

**Mathematical notation**: □P → P

**ModelChecker code**:
```python
formula = "(\\Box P \\rightarrow P)"
```

**Explanation**: The `\Box` represents □ (necessity) in the code.
```

## File Encoding for Documentation

### UTF-8 Requirements

All documentation files must use UTF-8 encoding:

```bash
# Check encoding
file -i README.md  # Should show: charset=utf-8

# Convert if needed
iconv -f ISO-8859-1 -t UTF-8 input.md -o output.md
```

### Quality Assurance

```bash
# Verify Unicode symbols display correctly
grep -r "[∧∨¬□◇→↔]" docs/

# Check for proper encoding
find docs -name "*.md" -exec file -i {} \; | grep -v utf-8
```

## Accessibility Considerations

### Screen Reader Compatibility

When using Unicode, provide context:

```markdown
# GOOD - Provides pronunciation guide
The conjunction operator ∧ (pronounced "and") connects two formulas.

# BETTER - Multiple representations  
The formula A ∧ B (A and B) is true when both A and B are true.
```

### Alternative Representations

For maximum accessibility:

```markdown
## Logical Operators

- Conjunction: ∧ (AND, wedge)
- Disjunction: ∨ (OR, vee)  
- Negation: ¬ (NOT, negation sign)
- Implication: → (IF-THEN, arrow)
```

## Cross-Reference Standards

When linking between code and documentation:

```markdown
## Implementation Details

For the code implementation of modal operators, see 
[modal.py](../../Code/src/model_checker/theory_lib/modal/semantic.py).

Note: In code, operators must use LaTeX notation:
- Documentation: □ (Box operator)
- Code: `\Box`
```

## Common Pitfalls

### Don't Mix in Code Blocks

```markdown
# WRONG - Unicode in code example
```python
formula = "□P → P"  # This won't parse!
```

# CORRECT - LaTeX in code, Unicode in explanation
The axiom T states that □P → P (what is necessary is true).

```python
formula = "(\\Box P \\rightarrow P)"
```
```

### Consistent Symbol Choice

```markdown
# INCONSISTENT - Mixing arrows
Sometimes using → and sometimes using ⟹

# CONSISTENT - Clear distinction
- Material implication: →
- Logical entailment: ⟹
```

## Documentation Templates

### Formula Documentation Template

```markdown
## [Formula Name]

**Informal reading**: [Natural language description]

**Formal notation**: [Unicode formula]

**ModelChecker syntax**:
```python
formula = "[LaTeX formula string]"
```

**Example**:
- Input: [Example values]
- Output: [Expected result]

**Related formulas**: [Links to similar formulas]
```

### Operator Documentation Template

```markdown
## [Operator Name] ([Unicode Symbol])

**LaTeX notation**: `\command`
**Pronunciation**: [How to read aloud]
**Type**: Unary/Binary/Other

### Semantics
[Formal semantic description]

### Usage
[When and how to use this operator]

### Examples
1. [Unicode example] - [Explanation]
   - Code: `"[LaTeX version]"`
```

---

[← Version Control](VERSION_CONTROL.md) | [Back to Maintenance](README.md) | [Documentation Standards →](DOCUMENTATION_STANDARDS.md)