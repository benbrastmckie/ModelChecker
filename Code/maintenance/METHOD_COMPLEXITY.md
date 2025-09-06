# Method Complexity Guidelines

[← Refactoring Methodology](REFACTORING_METHODOLOGY.md) | [Back to Maintenance](README.md) | [Architectural Patterns →](ARCHITECTURAL_PATTERNS.md)

## Overview

This document provides **flexible guidelines for assessing method complexity** in the ModelChecker codebase. Rather than enforcing rigid rules, these standards help identify opportunities for improvement while respecting the domain complexity inherent in logical reasoning systems.

**Philosophy:** Method complexity should be **appropriate for the problem domain**. Simple operations should be simple; complex algorithms may legitimately require substantial code.

## Context-Aware Complexity Guidelines

### Method Length Targets (Soft Guidelines)

Based on analysis of the current codebase and successful refactoring patterns:

#### **Utility and Helper Methods: 20-40 lines**
*These handle focused, well-defined tasks*

```python
# Example: Clean, focused utility
def format_formula_display(formula: str, use_unicode: bool = False) -> str:
    """Format a formula for display with optional Unicode conversion.
    
    Args:
        formula: LaTeX-notation formula to format
        use_unicode: Whether to convert to Unicode symbols
        
    Returns:
        Formatted formula string
    """
    if not formula.strip():
        return ""
        
    # Handle basic LaTeX to Unicode conversion
    if use_unicode:
        replacements = {
            '\\wedge': '∧',
            '\\vee': '∨', 
            '\\neg': '¬',
            '\\rightarrow': '→'
        }
        for latex, unicode_char in replacements.items():
            formula = formula.replace(latex, unicode_char)
    
    # Ensure proper spacing around operators
    formula = re.sub(r'(\w)\s*(\\\w+|\W)\s*(\w)', r'\1 \2 \3', formula)
    
    return formula.strip()
```

#### **Business Logic Methods: 40-75 lines**
*Core functionality with moderate complexity*

```python
# Example: Appropriate business logic complexity
def validate_example_case(self, example_data: List, theory_name: str) -> ValidationResult:
    """Validate an example case against theory requirements.
    
    This method handles the core validation logic that needs to check
    multiple aspects of example data structure and content.
    """
    if not example_data or len(example_data) != 3:
        return ValidationResult.error("Example must have exactly 3 components")
    
    assumptions, formulas, settings = example_data
    
    # Validate assumptions structure
    if not isinstance(assumptions, list):
        return ValidationResult.error("Assumptions must be a list")
    
    for i, assumption in enumerate(assumptions):
        if not self._is_valid_formula(assumption):
            return ValidationResult.error(f"Invalid assumption at index {i}: {assumption}")
    
    # Validate formulas structure  
    if not isinstance(formulas, list) or not formulas:
        return ValidationResult.error("Formulas must be a non-empty list")
        
    for i, formula in enumerate(formulas):
        if not self._is_valid_formula(formula):
            return ValidationResult.error(f"Invalid formula at index {i}: {formula}")
    
    # Validate settings against theory requirements
    theory_defaults = self._get_theory_defaults(theory_name)
    validation_result = self._validate_settings(settings, theory_defaults)
    
    if validation_result.has_errors():
        return validation_result
        
    return ValidationResult.success()
```

#### **Complex Domain Methods: 75+ lines**
*Legitimate complexity for algorithms, parsing, iteration logic*

Current examples in the codebase that appropriately use this length:
- `iterate/core.py`: `iterate_generator()` (330 lines) - Complex model iteration algorithm
- `theory_lib/logos/semantic.py`: `proposition_constraints()` (148 lines) - Semantic constraint generation
- `__main__.py`: `_create_parser()` (126 lines) - CLI argument parsing configuration

These methods handle **inherently complex domain problems** that don't decompose naturally into smaller pieces without losing cohesion.

### Complexity Assessment Criteria

Rather than just counting lines, consider these factors:

#### **Functional Cohesion**
```python
# High cohesion - method does one clear thing
def generate_bitvector_constraints(self, n_atoms: int, state_vars: List) -> List:
    """Generate all necessary bitvector constraints for n atomic propositions."""
    # All code focuses on bitvector constraint generation
    
# Low cohesion - method does multiple unrelated things  
def process_and_save_and_validate(self, data):  # Consider splitting
    # validation logic...
    # processing logic...  
    # file saving logic...
```

#### **Nesting Depth**
```python
# Reasonable nesting (2-3 levels)
def process_examples(self, examples):
    for example in examples:
        if self._should_process(example):
            result = self._process_single_example(example)
            
# Excessive nesting (4+ levels) - consider extraction
def complex_nested_processing(self, data):
    for item in data:
        if condition1:
            for sub_item in item.children:
                if condition2:
                    for detail in sub_item.details:  # Getting deep...
                        if condition3:
                            # This logic might benefit from extraction
```

#### **Cyclomatic Complexity**
Rough guidelines for decision points (if/for/while/try/except):
- **Simple methods:** 1-5 decision points
- **Moderate methods:** 6-10 decision points
- **Complex methods:** 10+ decision points (may indicate need for decomposition)

### When to Consider Method Extraction

#### **Clear Extraction Opportunities**
```python
# Original: Mixed responsibilities
def process_formula_validation(self, formula, theory):
    # Input parsing (could be extracted)
    parsed_tokens = []
    for char in formula:
        if char.isalpha():
            parsed_tokens.append(Token('ATOM', char))
        elif char in ['(', ')', '\\']:
            # Complex parsing logic...
            
    # Semantic validation (could be extracted)  
    for token in parsed_tokens:
        if token.type == 'OPERATOR':
            # Complex validation logic...
            
    # Theory-specific checks (could be extracted)
    theory_constraints = theory.get_constraints()
    # More complex logic...

# After extraction: Clear responsibilities
def process_formula_validation(self, formula, theory):
    """Coordinate formula validation process."""
    tokens = self._parse_formula_tokens(formula)
    self._validate_semantic_structure(tokens)
    self._validate_theory_constraints(tokens, theory)
    return ValidationResult.success()
```

#### **Repeated Patterns**
Look for similar code blocks that could be parameterized:

```python
# Before: Repetitive validation
def validate_settings(self, settings):
    if 'N' in settings:
        if not isinstance(settings['N'], int) or settings['N'] < 1:
            raise ValueError("N must be positive integer")
    if 'max_time' in settings:
        if not isinstance(settings['max_time'], int) or settings['max_time'] < 1:
            raise ValueError("max_time must be positive integer")
    # More similar validation...

# After: Extracted common pattern  
def validate_settings(self, settings):
    self._validate_positive_int(settings, 'N', required=True)
    self._validate_positive_int(settings, 'max_time', required=False)
    # Clear and DRY
```

## Quality Assessment Tools

### Simple Complexity Checks
```bash
# Count lines in methods (rough indicator)
grep -n "def " src/module.py | wc -l

# Find long methods (adjust line count as needed)
awk '/def /{f=NR; next} /^def |^class |^$/{if(f && NR-f>75) print FILENAME":"f":"NR-f" lines"; f=0}' src/module.py
```

### Manual Assessment Questions

When reviewing a method, ask:

1. **Purpose clarity:** Can I explain what this method does in one sentence?
2. **Testing difficulty:** How hard would it be to write comprehensive tests?
3. **Change frequency:** How often does this method need modification?
4. **Cognitive load:** How much context do I need to understand this method?

## Gradual Improvement Strategies

### Opportunistic Refactoring
```python
# When fixing bugs or adding features, consider improvements:

# Original bug fix location
def process_example(self, example):
    # 80 lines of mixed logic
    # Bug was in line 45...
    
# Consider: Extract the problematic section
def process_example(self, example):
    validation_result = self._validate_example_structure(example)  # Extracted
    if not validation_result.is_valid():
        return validation_result
    # Remaining focused logic...

def _validate_example_structure(self, example):
    """Focused validation logic - easier to test and debug."""
    # Previously problematic logic, now isolated and testable
```

### Progressive Decomposition
```python
# Don't try to perfect everything at once
# Phase 1: Extract the most complex or problematic section
# Phase 2: Further refine if needed
# Phase 3: Consider additional improvements

# Start with the biggest pain point, not the entire method
```

## Integration with Existing Codebase

### Respect Existing Patterns
The ModelChecker codebase has **legitimate complexity** in several areas:

- **Semantic constraint generation:** Complex logical rules need substantial code
- **Model iteration algorithms:** Mathematical algorithms don't always decompose cleanly
- **CLI parsing:** Comprehensive argument handling requires extensive configuration

**Don't force decomposition** where it would harm clarity or create artificial boundaries.

### Work with Domain Complexity
```python
# Appropriate domain complexity
def generate_modal_constraints(self, modal_operators, world_relations):
    """Generate constraints for modal logic semantics.
    
    This method handles the inherent complexity of modal logic
    constraint generation, which legitimately requires substantial
    code to handle all the semantic relationships properly.
    """
    # 100+ lines might be appropriate here because:
    # - Modal semantics are inherently complex
    # - Breaking this apart might lose semantic coherence
    # - The algorithm needs to consider multiple interrelated constraints
```

## Success Patterns

### From Builder Refactor
The successful builder/ refactor showed:

**What worked well:**
- Extracting **mixed responsibilities** into focused methods
- Moving **repeated patterns** into utilities  
- Creating **clear coordination methods** that delegate to specialists
- Preserving **domain-appropriate complexity** in semantic logic

**What to avoid:**
- Arbitrary line-count targets that ignore domain complexity
- Over-decomposition that scatters related logic
- Premature optimization of working, well-tested code

## Conclusion

Method complexity should serve **maintainability and clarity**, not arbitrary metrics. Use these guidelines to identify improvement opportunities, but always consider:

- **Does this change make the code clearer?**
- **Will this help with testing and debugging?**  
- **Am I preserving appropriate domain complexity?**
- **Is the effort justified by the maintenance benefit?**

The goal is **sustainable, readable code** that matches the complexity of the problems it solves.

---

[← Refactoring Methodology](REFACTORING_METHODOLOGY.md) | [Back to Maintenance](README.md) | [Architectural Patterns →](ARCHITECTURAL_PATTERNS.md)