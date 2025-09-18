# Formula Representation and Examples Standards

[← Back to Maintenance](../README.md) | [Iterator Standards →](ITERATOR.md)

## Overview

This document provides unified standards for formula representation and examples throughout the ModelChecker codebase. These standards ensure parser compatibility, code readability, and consistent example organization.

## Formula Formatting Standards

### Capital Letters for Variables

Always use capital letters (A, B, C) instead of lowercase (p, q, r) for propositional variables.

```python
# CORRECT
premises = ["A", "(A \\rightarrow B)"]

# INCORRECT
premises = ["p", "(p \\rightarrow q)"]
```

### Binary Operator Parentheses

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

### Unary Operator Formatting

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

### Nested Formula Rules

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

### Always Use LaTeX in Code

Unicode characters are NEVER permitted in code that the ModelChecker parser processes. Always use LaTeX notation.

```python
# CORRECT - LaTeX notation
operators = ["\\wedge", "\\vee", "\\neg", "\\Box", "\\Diamond"]
formula = "\\Box (A \\rightarrow B)"

# INCORRECT - Unicode characters
operators = ["∧", "∨", "¬", "□", "◇"]  # WRONG: Parser expects LaTeX
formula = "□(A → B)"  # WRONG: Parser will fail
```

### Standard LaTeX Commands

| Operator | LaTeX Code | Usage in Code | Unicode Display |
|----------|------------|---------------|-----------------|
| Negation | `\\neg` | `"\\neg A"` | ¬ |
| Conjunction | `\\wedge` | `"(A \\wedge B)"` | ∧ |
| Disjunction | `\\vee` | `"(A \\vee B)"` | ∨ |
| Implication | `\\rightarrow` | `"(A \\rightarrow B)"` | → |
| Biconditional | `\\leftrightarrow` | `"(A \\leftrightarrow B)"` | ↔ |
| Necessity | `\\Box` | `"\\Box A"` | □ |
| Possibility | `\\Diamond` | `"\\Diamond A"` | ◇ |
| Box-right | `\\boxright` | `"(A \\boxright B)"` | □→ |
| Diamond-right | `\\diamondright` | `"(A \\diamondright B)"` | ◇→ |

### Theory-Specific LaTeX

For specialized theories, use appropriate LaTeX commands:

```python
# Constitutive Logic
IDENTITY = "\\equiv"
ESSENCE = "\\sqsubseteq"  
GROUND = "\\leq"
RELEVANCE = "\\preceq"

# Custom Operators
class CounterfactualOperator(Operator):
    def __init__(self):
        super().__init__("\\boxright", 2)  # LaTeX command
```

## Operator Precedence Rules

When combining operators, follow standard logical precedence:

1. **Negation** (`\\neg`) - Highest precedence
2. **Modal operators** (`\\Box`, `\\Diamond`)
3. **Conjunction** (`\\wedge`)
4. **Disjunction** (`\\vee`)
5. **Implication** (`\\rightarrow`)
6. **Biconditional** (`\\leftrightarrow`) - Lowest precedence

```python
# Examples showing precedence
formulas = [
    "\\neg A \\wedge B",              # Parsed as: (\\neg A) \\wedge B
    "A \\wedge B \\vee C",            # Requires explicit parentheses
    "(A \\wedge B) \\vee C",          # Clear precedence
    "A \\vee (B \\wedge C)",          # Clear precedence
]
```

## Parenthesization Rules

### Explicit Parentheses Required

Always use explicit parentheses when precedence is ambiguous:

```python
# CORRECT - Clear precedence
formulas = [
    "(A \\wedge B) \\vee C",
    "A \\wedge (B \\vee C)",
    "(A \\rightarrow B) \\wedge (C \\rightarrow D)",
]

# AVOID - Ambiguous precedence
formula = "A \\wedge B \\vee C"  # Unclear precedence
```

### Minimal Parentheses Principle

Use the minimum parentheses necessary for clarity:

```python
# CORRECT - Minimal but clear
formulas = [
    "\\neg (A \\wedge B)",        # Negation scope clear
    "\\Box A \\rightarrow B",     # Modal operator has high precedence
    "(\\Box A \\rightarrow \\Box B)",  # Binary main operator
]

# EXCESSIVE - Too many parentheses
formula = "((\\neg (A)) \\wedge (B))"  # Overly parenthesized
```

## Unicode Guidelines for Display

### Documentation Usage

Unicode characters are encouraged in documentation for clarity:

```markdown
The formula `\\Box A` displays as □A
The implication `(A \\rightarrow B)` displays as (A → B)
```

### Comments and Docstrings

Unicode is permitted in comments and docstrings:

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

### Output Display

Unicode can be used in output for user readability:

```python
# Input processing uses LaTeX
input_formula = "\\Box (A \\rightarrow B)"

# Output display can use Unicode
print(f"Input: {input_formula}")
print(f"Display: □(A → B)")  # Unicode in output only
```

## Examples.py File Structure

### File Organization

Every examples.py file must include these components in order:

1. **Module Docstring** - Describes the examples and their categories
2. **Standard Imports** - System imports and path setup
3. **Theory Imports** - Theory-specific semantic components
4. **Theory Definition** - Semantic theory configuration
5. **Example Definitions** - Individual examples following naming convention
6. **Collections** - Organized countermodel_examples and theorem_examples
7. **Required Variables** - unit_tests, example_range, semantic_theories
8. **Main Block** - Makes the module executable

### Example Naming Convention

All examples must follow the **PREFIX_TYPE_NUMBER** pattern:

- **PREFIX**: Theory abbreviation (2-3 characters)
- **TYPE**: CM (countermodel) or TH (theorem)
- **NUMBER**: Sequential number starting from 1

```python
EXT_TH_1_example    # Extensional theorem 1
LOG_CM_3_example    # Logos countermodel 3
IMP_TH_2_example    # Imposition theorem 2
BIM_CM_1_example    # Bimodal countermodel 1
```

### Theory Prefix Reference

| Theory          | Prefix | Description                 |
|-----------------|--------|-----------------------------|
| Extensional     | EXT    | Basic extensional logic     |
| Modal           | MOD    | Modal operators (□, ◇)      |
| Counterfactual  | CF     | Counterfactual conditionals |
| Constitutive    | CON    | Identity and essence        |
| Relevance       | REL    | Relevance logic             |
| Logos (general) | LOG    | Hyperintensional logic      |
| Exclusion       | EX     | Unilateral semantics        |
| Imposition      | IMP    | Fine's counterfactuals      |
| Bimodal         | BIM    | Temporal-modal logic        |

### Required Variables Template

```python
# Organize examples by category
countermodel_examples = {
    "PREFIX_CM_1": PREFIX_CM_1_example,
    "PREFIX_CM_2": PREFIX_CM_2_example,
    # ... all countermodel examples
}

theorem_examples = {
    "PREFIX_TH_1": PREFIX_TH_1_example,
    "PREFIX_TH_2": PREFIX_TH_2_example,
    # ... all theorem examples
}

# Combine for unit_tests (used by test framework)
unit_tests = {**countermodel_examples, **theorem_examples}

# Examples to execute when run directly
example_range = {
    "PREFIX_CM_1": PREFIX_CM_1_example,
    "PREFIX_TH_1": PREFIX_TH_1_example,
    # ... selected examples to run
}

# Semantic theories to use
semantic_theories = {
    "theory_name": theory_definition,
}

# Optional execution settings
general_settings = {
    "print_constraints": False,
    "print_impossible": False,
    "print_z3": False,
    "save_output": False,
}
```

## Settings Documentation Requirements

### Mandatory Inline Comments

Every example settings dictionary MUST include inline comments:

```python
settings = {
    'N': 3,                    # Max number of atomic propositions
    'contingent': False,       # Allow non-contingent propositions
    'non_null': False,         # Allow the null state
    'non_empty': False,        # Allow empty verifier/falsifier sets
    'disjoint': False,         # Allow verifier/falsifier overlap
    'max_time': 10,            # Timeout in seconds
    'iterate': 1,              # Number of models to find
    'expectation': False,      # True = expect countermodel, False = expect theorem
}
```

### Example Definition Template

```python
PREFIX_TH_1_example = {
    'name': 'PREFIX_TH_1',
    'description': 'Brief description of the logical principle being tested',
    'premises': [
        "\\Box (A \\rightarrow B)",    # LaTeX notation required
        "\\Box A"
    ],
    'conclusions': ["\\Box B"],
    'settings': {
        'N': 3,                        # Max number of atomic propositions
        'contingent': False,           # Allow non-contingent propositions
        'non_null': False,             # Allow the null state
        'non_empty': False,            # Allow empty verifier/falsifier sets
        'disjoint': False,             # Allow verifier/falsifier overlap
        'max_time': 10,                # Timeout in seconds
        'iterate': 1,                  # Number of models to find
        'expectation': False,          # True = expect countermodel, False = expect theorem
    }
}
```

## Test Case Organization

### Unit Test Integration

Examples are automatically included in unit tests via the `unit_tests` dictionary:

```python
# This structure enables automatic test discovery
unit_tests = {**countermodel_examples, **theorem_examples}

# Test framework accesses examples like:
for name, example in unit_tests.items():
    test_result = run_example(example)
    assert test_result.matches_expectation()
```

### Test Categories

Organize examples by logical categories:

```python
# Theorem examples (should prove valid)
theorem_examples = {
    "PREFIX_TH_1": basic_inference_example,
    "PREFIX_TH_2": modal_reasoning_example,
    "PREFIX_TH_3": complex_derivation_example,
}

# Countermodel examples (should find countermodels)
countermodel_examples = {
    "PREFIX_CM_1": invalid_inference_example,
    "PREFIX_CM_2": modal_fallacy_example,
    "PREFIX_CM_3": boundary_case_example,
}
```

### Execution Control

Use `example_range` to control which examples run by default:

```python
# Run representative examples
example_range = {
    "PREFIX_TH_1": PREFIX_TH_1_example,  # Basic valid case
    "PREFIX_CM_1": PREFIX_CM_1_example,  # Basic invalid case
    # Include edge cases and important examples
}
```

## Validation Guidance

### Formula Validation Checklist

Before committing, verify:

1. **LaTeX Notation**: All formulas use `\\` notation
2. **Parentheses**: Binary operators have outer parentheses, unary operators do not
3. **Variable Names**: Use capital letters (A, B, C)
4. **No Unicode**: No Unicode characters in formula strings
5. **Consistent Spacing**: Maintain consistent spacing around operators

### Automated Validation

```bash
# Check for Unicode in code (should find no matches)
grep -n '[□◇∧∨¬→↔]' *.py | grep -v '#' | grep -v '"""'

# Verify UTF-8 encoding
file -i *.py | grep -v "charset=utf-8"

# Check formula formatting
python -c "
import ast
import re

def check_formulas(file_path):
    with open(file_path) as f:
        content = f.read()
    
    # Find formula strings
    formula_pattern = r'[\"\'](.*?\\\\[a-zA-Z]+.*?)[\"\']'
    formulas = re.findall(formula_pattern, content)
    
    for formula in formulas:
        # Check for binary operator parentheses
        binary_ops = ['\\\\wedge', '\\\\vee', '\\\\rightarrow', '\\\\leftrightarrow', '\\\\boxright']
        for op in binary_ops:
            if op in formula and not (formula.startswith('(') and formula.endswith(')')):
                print(f'Missing parentheses: {formula}')
        
        # Check for unary operator parentheses
        unary_ops = ['\\\\neg', '\\\\Box', '\\\\Diamond']
        for op in unary_ops:
            if formula.startswith('(') and formula.endswith(')') and formula.startswith(f'({op}'):
                print(f'Unnecessary parentheses: {formula}')

check_formulas('examples.py')
"
```

### Parser Testing

Test formulas through the parser to ensure compatibility:

```python
def test_formula_parsing():
    """Test that all formulas parse correctly."""
    from model_checker.syntactic.parser import Parser
    
    parser = Parser()
    test_formulas = [
        "\\neg A",
        "(A \\wedge B)",
        "\\Box (A \\rightarrow B)",
        "(\\Box A \\rightarrow \\Box B)",
    ]
    
    for formula in test_formulas:
        try:
            parsed = parser.parse(formula)
            assert parsed is not None
        except Exception as e:
            print(f"Parse error in {formula}: {e}")
```

## Good and Bad Examples

### Good Formula Examples

```python
# Well-formatted formulas
good_examples = [
    "A",                           # Simple atomic
    "\\neg A",                     # Unary negation
    "(A \\wedge B)",               # Binary conjunction
    "\\Box (A \\rightarrow B)",    # Modal with implication
    "(\\Box A \\rightarrow \\Box B)",  # Complex binary
    "\\neg \\Box \\neg A",         # Unary chain
]
```

### Bad Formula Examples

```python
# Incorrectly formatted formulas
bad_examples = [
    "(\\neg A)",                   # Unnecessary parentheses on unary
    "A \\wedge B",                 # Missing parentheses on binary
    "□(A → B)",                    # Unicode instead of LaTeX
    "(p \\rightarrow q)",          # Lowercase variables
    "A\\wedgeB",                   # Missing spaces
]
```

### Settings Examples

```python
# CORRECT - All settings documented
good_settings = {
    'N': 3,                    # Max number of atomic propositions
    'contingent': False,       # Allow non-contingent propositions
    'non_null': False,         # Allow the null state
    'non_empty': False,        # Allow empty verifier/falsifier sets
    'disjoint': False,         # Allow verifier/falsifier overlap
    'max_time': 10,            # Timeout in seconds
    'iterate': 1,              # Number of models to find
    'expectation': False,      # True = expect countermodel, False = expect theorem
}

# INCORRECT - Missing comments
bad_settings = {
    'N': 3,
    'contingent': False,
    'non_null': False,
    'non_empty': False,
    'disjoint': False,
    'max_time': 10,
    'iterate': 1,
    'expectation': False,
}
```

## Success Metrics for Formula Clarity

### Readability Metrics

A well-formatted formula should:

1. **Parse correctly** through the ModelChecker parser
2. **Display clearly** when converted to Unicode for output
3. **Follow precedence rules** without ambiguity
4. **Use minimal parentheses** while maintaining clarity
5. **Have consistent spacing** around operators

### Quality Indicators

- **Parser Success Rate**: 100% of formulas should parse without errors
- **Precedence Clarity**: No ambiguous operator combinations
- **Naming Consistency**: All variables use capital letters
- **Documentation Completeness**: All settings have inline comments
- **Test Coverage**: All examples included in unit_tests dictionary

### Performance Metrics

- **Parse Time**: Formulas should parse in < 10ms
- **Memory Usage**: Minimal memory overhead for formula storage
- **Error Recovery**: Clear error messages for malformed formulas

## Common Formatting Errors

### Frequent Mistakes

1. **Missing binary parentheses**: `A \\wedge B` should be `(A \\wedge B)`
2. **Extra unary parentheses**: `(\\neg A)` should be `\\neg A`
3. **Unicode in formulas**: `A ∧ B` should be `(A \\wedge B)`
4. **Lowercase variables**: `p \\rightarrow q` should be `(P \\rightarrow Q)` or `(A \\rightarrow B)`
5. **Inconsistent spacing**: Maintain consistent spacing around operators
6. **Missing settings comments**: All settings dictionaries need inline comments

### Migration Guidelines

When updating existing code:

```python
# Replace Unicode systematically
unicode_to_latex = {
    '¬': '\\neg',
    '∧': '\\wedge',
    '∨': '\\vee',
    '→': '\\rightarrow',
    '↔': '\\leftrightarrow',
    '□': '\\Box',
    '◇': '\\Diamond',
    '□→': '\\boxright',
    '◇→': '\\diamondright'
}

# Apply to formula strings only (not comments)
for unicode_char, latex_cmd in unicode_to_latex.items():
    formula = formula.replace(unicode_char, latex_cmd)
```

## Theory Loading with -l Flag

The `-l` flag creates new projects from theory templates with properly formatted examples:

```bash
model-checker -l logos      # Hyperintensional truthmaker semantics
model-checker -l exclusion  # Unilateral semantics  
model-checker -l imposition # Fine's counterfactual semantics
model-checker -l bimodal    # Combined temporal-modal logic
```

This creates a complete project structure with:
- Properly formatted examples.py file
- Theory-specific semantic components
- Documentation following standards
- Unit tests with correct naming conventions

---

[← Back to Maintenance](../README.md) | [Iterator Standards →](ITERATOR.md)