# Research Report: Task #20

**Task**: 20 - add_parser_well_formedness_checking
**Started**: 2026-03-02T00:00:00Z
**Completed**: 2026-03-02T01:00:00Z
**Effort**: Medium
**Dependencies**: Task #19 (completed)
**Sources/Inputs**: Codebase analysis of syntactic layer and task 19 implementation
**Artifacts**: This research report
**Standards**: report-format.md, subagent-return.md

## Executive Summary

- **Well-formedness criteria identified**: A sentence is well-formed if and only if it has a propositional operator or sentence letter at its root. Bare variables, constants, and function applications are terms (denoting individuals), not sentences (expressing propositions).

- **Optimal insertion point**: The check should be added in `Sentence.__init__()` (sentence.py) immediately after parsing completes (line 67). This is the single entry point where all sentences are constructed, ensuring fail-fast behavior.

- **Task 19's workaround to remove**: `_is_nonpropositional_sentence()` method and the guard in `interpret()` in structure.py (lines 315-379) should be removed once parser-level rejection is implemented.

- **Error message design**: Use `ParseError` with formula context and clear guidance for users to understand what went wrong and how to fix it.

## Context & Scope

Task 19 fixed first-order theorem failures by adding a workaround that silently skips term-only sentences during `interpret()`. While this prevented crashes, it violates the fail-fast principle - users may not realize their input is syntactically ill-formed until they see unexpected behavior. Task 20 aims to reject ill-formed input earlier, at parse time, with clear error messages.

### What is a Well-Formed Sentence?

In the ModelChecker's first-order logic extension:

| Syntactic Category | Examples | Is Sentence? | Explanation |
|-------------------|----------|--------------|-------------|
| Propositional operators | `(A \wedge B)`, `\neg P[]` | YES | Has operator at root |
| Sentence letters | `P[]`, `A` | YES | Zero-arity predicates |
| Predicates with args | `F[v_x]`, `R[v_x, v_y]` | YES | Propositional, have truth values |
| Quantified formulas | `\forall v_x. P[v_x]` | YES | Quantifiers are propositional |
| Lambda abstractions | `\lambda v_x. P[v_x]` | NO | Denote functions, not propositions |
| Variables | `v_x` | NO | Denote individuals |
| Constants | `a<>`, `sam` | NO | Denote individuals |
| Function applications | `f<v_x>` | NO | Denote individuals |

## Findings

### 1. Parsing Pipeline Architecture

The parsing pipeline has three distinct phases:

```
Phase 1: Tokenization (parsing.py)
  tokenize_first_order() / manual split()
         ↓
Phase 2: Prefix Conversion (parsing.py)
  parse_first_order_expression() / parse_expression()
         ↓
Phase 3: Sentence Construction (sentence.py)
  Sentence.__init__()
```

**Key insight**: Sentence construction happens AFTER prefix conversion. The prefix representation already contains the structural information needed to determine well-formedness.

### 2. Current Sentence Construction Flow

In `Sentence.__init__()` (sentence.py lines 48-108):

```python
def __init__(self, infix_sentence: FormulaString) -> None:
    # ... validation ...
    self.name = infix_sentence
    self.prefix_sentence, self.complexity = self.prefix(infix_sentence)  # Line 67

    # Complexity-based classification
    if self.complexity > 0:
        # Complex sentence with operator
        self.original_arguments = [...]
        self.original_operator = first_op
    else:
        # Atomic case
        self.original_arguments = None
        if isinstance(first_elem, str) and first_elem in {'\\top', '\\bot'}:
            self.original_operator = first_elem
        elif isinstance(first_elem, Variable):
            self.original_operator = None  # <-- This is where term-only sneaks through
        else:
            self.original_operator = None
```

**Finding**: The constructor already distinguishes between:
- Complex sentences (complexity > 0)
- Extremal operators (`\top`, `\bot`)
- Variables (identified but not rejected)
- Other atomic cases (strings = sentence letters)

The check point is **line 67-100** where the decision about `original_operator` is made.

### 3. Task 19's Workaround Location

In `structure.py` (lines 315-379):

```python
def _is_nonpropositional_sentence(self, sent_obj: 'Sentence') -> bool:
    """Check if sentence cannot have a proposition.

    Non-propositional sentences include:
    1. Term-only sentences (variables, constants) which denote individuals
    2. Lambda abstractions which denote functions, not propositions
    """
    # Lambda check
    if (sent_obj.operator is not None and
        hasattr(sent_obj.operator, 'name') and
        sent_obj.operator.name == '\\lambda'):
        return True

    # Term check
    if sent_obj.operator is not None or sent_obj.sentence_letter is not None:
        return False

    prefix = sent_obj.prefix_sentence
    if isinstance(prefix, list) and len(prefix) == 1:
        from model_checker.syntactic.terms import Term
        if isinstance(prefix[0], Term):
            return True

    return False

def interpret(self, sentences: List['Sentence']) -> None:
    # ...
    for sent_obj in sentences:
        if sent_obj.arguments:
            self.interpret(sent_obj.arguments)

        # Skip non-propositional sentences (terms, lambda abstractions)
        if self._is_nonpropositional_sentence(sent_obj):
            continue

        sent_obj.update_proposition(self)
```

**What needs removal**: The `_is_nonpropositional_sentence()` method and the guard in `interpret()` that calls it.

**Note on lambda handling**: Lambda abstractions ARE processed by the parser correctly and ARE used inside quantifiers. The issue is when they appear as TOP-LEVEL sentences (not inside ForAll/Exists). The parser-level check should NOT reject lambdas inside quantifiers.

### 4. Term Detection Patterns

From `terms.py`, the Term class hierarchy:

```python
class Term(ABC):  # Abstract base
class Variable(Term):  # v_x, v_1
class Constant(Term):  # a<>, sam
class FunctionApplication(Term):  # f<t1, t2>
```

Detection pattern (from task 19's implementation):
```python
from model_checker.syntactic.terms import Term

def is_term_only(prefix_sentence):
    """Check if prefix_sentence represents a term, not a proposition."""
    if isinstance(prefix_sentence, list) and len(prefix_sentence) == 1:
        if isinstance(prefix_sentence[0], Term):
            return True
    return False
```

### 5. Lambda as Top-Level Detection

Lambda abstractions denote functions (type `e -> t` or similar), not propositions (type `t`). When appearing as a top-level sentence, they are ill-formed.

Detection pattern:
```python
def is_lambda_at_root(prefix_sentence):
    """Check if this is a bare lambda abstraction."""
    if (isinstance(prefix_sentence, list) and
        len(prefix_sentence) >= 1 and
        prefix_sentence[0] == "\\lambda"):
        return True
    return False
```

**Important**: This check should only apply at the TOP level. Lambdas inside quantifiers are well-formed:
- `\forall v_x. P[v_x]` parses to `["\forall", ["\lambda", v_x, [P, v_x]]]` - the lambda is NOT at root
- `\lambda v_x. P[v_x]` as a standalone sentence IS at root and should be rejected

### 6. Error Handling Patterns

The syntactic layer has established error classes in `errors.py`:

```python
class ParseError(SyntacticError):
    """Raised when formula parsing fails."""
    pass

class InvalidFormulaError(ValidationError):
    """Raised when formula structure is invalid."""
    pass
```

**Recommendation**: Use `ParseError` for consistency with parsing-related failures. Include:
- The offending formula
- A clear explanation of why it's invalid
- Suggestion for correction

Example error messages:
```python
raise ParseError(
    f"'{infix_sentence}' is not a well-formed sentence. "
    f"Variables like '{prefix_sentence[0]}' denote individuals, not propositions. "
    f"Did you mean to use a predicate like 'P[{prefix_sentence[0]}]'?",
    formula=infix_sentence,
    context={'type': 'term_only', 'term': str(prefix_sentence[0])}
)
```

### 7. Existing Validation Points

The `Syntax` class already performs validation after sentence construction:
- Arity consistency validation (`_validate_arity_consistency`)
- Circular definition checking (`circularity_check`)
- Vocabulary collection

**Integration point**: Well-formedness checking in `Sentence.__init__()` will occur BEFORE these checks, which is appropriate since vocabulary collection depends on having valid sentences.

## Architecture Analysis

### Proposed Check Location

```
Sentence.__init__()
  ↓
self.prefix_sentence, self.complexity = self.prefix(infix_sentence)  # Line 67
  ↓
*** INSERT WELL-FORMEDNESS CHECK HERE ***  # New code
  ↓
if self.complexity > 0:
    # Process complex sentence
else:
    # Process atomic case
```

### Check Logic

```python
# After line 67, before complexity-based branching:
self._validate_well_formedness()

def _validate_well_formedness(self) -> None:
    """Validate that this represents a well-formed sentence, not a bare term.

    Raises:
        ParseError: If the formula is a term-only expression (variable, constant,
                   function application) or a bare lambda abstraction.
    """
    from .terms import Term

    # Check for term-only sentence (bare variable, constant, or function application)
    if isinstance(self.prefix_sentence, list) and len(self.prefix_sentence) == 1:
        atom = self.prefix_sentence[0]
        if isinstance(atom, Term):
            raise ParseError(
                f"'{self.name}' is not a well-formed sentence. "
                f"Terms like '{atom}' denote individuals, not propositions. "
                f"To make a sentence, use a predicate: e.g., 'P[{atom}]' or wrap in a propositional context.",
                formula=self.name,
                context={'type': 'term_only', 'term': str(atom)}
            )

    # Check for bare lambda abstraction at root
    if (isinstance(self.prefix_sentence, list) and
        len(self.prefix_sentence) >= 1 and
        self.prefix_sentence[0] == "\\lambda"):
        raise ParseError(
            f"'{self.name}' is not a well-formed sentence. "
            f"Lambda abstractions denote functions, not propositions. "
            f"Did you mean to use a quantifier like '\\forall' or '\\exists'?",
            formula=self.name,
            context={'type': 'bare_lambda'}
        )
```

## Recommendations

### Implementation Strategy

1. **Add well-formedness check to Sentence.__init__()** (sentence.py)
   - Place after `self.prefix(infix_sentence)` call (line 67)
   - Check for term-only sentences
   - Check for bare lambda abstractions
   - Raise `ParseError` with helpful message

2. **Write tests FIRST** (TDD)
   - Test that term-only inputs raise ParseError
   - Test that lambda-at-root raises ParseError
   - Test that valid sentences still parse correctly
   - Test that lambdas inside quantifiers are accepted

3. **Remove task 19's workaround** (structure.py)
   - Delete `_is_nonpropositional_sentence()` method
   - Remove the guard in `interpret()` that calls it
   - This should be done AFTER parser-level check is working

4. **Update error messages to be user-friendly**
   - Explain what went wrong
   - Explain why it's wrong (terms vs propositions)
   - Suggest how to fix it

### Test Cases

```python
# Should raise ParseError
def test_bare_variable_rejected():
    with pytest.raises(ParseError, match="not a well-formed sentence"):
        Sentence("v_x")

def test_bare_constant_rejected():
    with pytest.raises(ParseError, match="not a well-formed sentence"):
        Sentence("sam<>")

def test_function_application_rejected():
    with pytest.raises(ParseError, match="not a well-formed sentence"):
        Sentence("f<v_x>")

def test_bare_lambda_rejected():
    with pytest.raises(ParseError, match="not a well-formed sentence"):
        Sentence("\\lambda v_x. P[v_x]")

# Should NOT raise (valid sentences)
def test_predicate_accepted():
    s = Sentence("P[v_x]")  # No error

def test_quantified_formula_accepted():
    s = Sentence("\\forall v_x. P[v_x]")  # No error - lambda inside is OK

def test_propositional_formula_accepted():
    s = Sentence("(A \\wedge B)")  # No error
```

## Risks & Mitigations

| Risk | Impact | Mitigation |
|------|--------|------------|
| Breaking valid first-order formulas | High | Comprehensive test coverage, especially for quantifiers with lambdas |
| Missing edge cases in term detection | Medium | Rely on existing Term class hierarchy, test all subclasses |
| Error messages confusing users | Medium | Include specific suggestions, test with real users |
| Regression in propositional parsing | Low | Full test suite run after changes |

## Appendix

### Key Files

1. **sentence.py** - Primary location for well-formedness check
   - `Sentence.__init__()` - Insert check after line 67

2. **structure.py** - Task 19's workaround to remove
   - `_is_nonpropositional_sentence()` - Delete
   - `interpret()` guard - Remove

3. **errors.py** - Error class to use
   - `ParseError` - Use for well-formedness errors

4. **terms.py** - Term class hierarchy
   - `Term`, `Variable`, `Constant`, `FunctionApplication`

### Test Commands

```bash
# Run parser tests
PYTHONPATH=code/src pytest code/src/model_checker/utils/tests/unit/test_parsing.py -v

# Run first-order tests
PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/logos/subtheories/first-order/tests/ -v

# Run all syntactic tests
PYTHONPATH=code/src pytest code/src/model_checker/syntactic/ -v

# Run full test suite for regression
PYTHONPATH=code/src pytest code/tests/ -v
```

### Related Work

- Task 18: Fixed predicate handling and constant registration
- Task 19: Added workaround for term-only sentences in interpret()
- This task: Replaces workaround with proper fail-fast validation
