# Research Report: Task #20 (Revised)

**Task**: 20 - add_parser_well_formedness_checking
**Started**: 2026-03-02T00:00:00Z
**Completed**: 2026-03-02T14:00:00Z
**Effort**: Medium
**Dependencies**: Task #19 (completed)
**Sources/Inputs**: Logos Theory manual (chapters 02-constitutive, 03-dynamics), ModelChecker codebase
**Artifacts**: This research report (supersedes research-001.md)
**Standards**: report-format.md, subagent-return.md

## Executive Summary

This research report corrects the definition of well-formed sentences from research-001.md. The previous report incorrectly stated that well-formedness is simply about having a propositional operator at the root. The actual definition from the Logos Theory manual is more nuanced and involves:

1. **Syntactic well-formedness**: Matching the grammar for well-formed formulas (WFF)
2. **Sentence vs formula distinction**: A sentence is a CLOSED formula (FV(phi) = emptyset)
3. **Lambda handling**: Bare lambdas are NOT in the WFF grammar, but lambda applications ARE

The key complexity arises from variables and binding operators.

## Context & Scope

### Authoritative Definition from Logos Theory Manual

The manual (chapter 02-constitutive.typ) provides these definitions:

**Definition: Well-Formed Formulas** (def-wff, lines 76-89):
```
phi, psi ::=
    F(t1, ..., tn) |           # Predicate application
    (lambda v.phi)(t) |        # Lambda APPLICATION (not bare lambda!)
    forall phi |               # Universal quantification
    top | bot |                # Extremal constants
    not phi |                  # Negation
    phi and psi |              # Conjunction
    phi or psi |               # Disjunction
    phi equiv psi              # Propositional identity
```

**Definition: Free Variables of Formulas** (def-fv-formula, lines 94-104):
```
FV(F(t1,...,tn)) = Union(FV(ti))
FV((lambda v.phi)(t)) = (FV(phi) \ {v}) union FV(t)
FV(forall phi) = FV(phi)
FV(top) = FV(bot) = emptyset
FV(not phi) = FV(phi)
FV(phi and psi) = FV(phi) union FV(psi)
FV(phi or psi) = FV(phi) union FV(psi)
FV(phi equiv psi) = FV(phi) union FV(psi)
```

**Definition: Open and Closed Formulas** (def-open-closed, lines 107-113):
- A formula phi is **open** if FV(phi) is non-empty
- A formula phi is **closed** (a **sentence**) if FV(phi) = emptyset

**Derived Operators** (def-derived-operators, lines 139-149):
```
forall v.phi := forall(lambda v.phi)    # Universal quantification
exists v.phi := not forall v. not phi   # Existential quantification
```

### Key Insights

1. **The WFF grammar does NOT include bare lambda abstractions `lambda v.phi`**
   - Only lambda APPLICATIONS `(lambda v.phi)(t)` are well-formed formulas
   - Lambdas appear inside quantifiers: `forall v.phi` desugars to `forall(lambda v.phi)`
   - This is a Church-style encoding where quantifiers take properties (lambdas) as arguments

2. **Terms are NOT formulas**
   - Variables `v_x` are terms
   - Constants `a<>` are terms
   - Function applications `f<t1, t2>` are terms
   - Terms denote individuals; formulas express propositions

3. **A sentence is specifically a CLOSED formula**
   - Open formulas (with free variables) are well-formed formulas but NOT sentences
   - Only closed formulas can be evaluated for truth without an assignment
   - Example: `P[v_x]` is a WFF but not a sentence (FV = {v_x})
   - Example: `forall v_x. P[v_x]` IS a sentence (FV = emptyset)

### Correction to Previous Research

The previous research (research-001.md) stated:
> "A sentence is well-formed if and only if it has a propositional operator or sentence letter at its root."

This is **incomplete**. The correct criteria are:

| Input | WFF? | Sentence? | Reason |
|-------|------|-----------|--------|
| `P[]` | Yes | Yes | Zero-arity predicate, FV = {} |
| `P[v_x]` | Yes | **No** | Unary predicate, but FV = {v_x} |
| `forall v_x. P[v_x]` | Yes | Yes | Quantifier binds v_x, FV = {} |
| `v_x` | **No** | No | Variable is a term, not a formula |
| `a<>` | **No** | No | Constant is a term, not a formula |
| `f<v_x>` | **No** | No | Function application is a term |
| `lambda v_x. P[v_x]` | **No** | No | Bare lambda not in WFF grammar |
| `(lambda v_x. P[v_x])(a<>)` | Yes | Yes | Lambda application, FV = {} |
| `(A \wedge B)` | Yes | Yes | Conjunction of sentence letters |

## Findings

### 1. Two-Level Validation Needed

Well-formedness checking requires TWO levels of validation:

**Level 1: Syntactic Category Check (WFF Grammar)**
- Is the parsed structure a formula according to the grammar?
- Terms (variables, constants, functions) are NOT formulas
- Bare lambdas are NOT formulas

**Level 2: Closedness Check (Sentence Definition)**
- Does the formula have free variables?
- If FV(phi) != {}, it's an open formula, not a sentence
- This requires computing free variables across the formula structure

### 2. Free Variable Computation for Formulas

The `terms.py` module already implements `free_variables()` for terms:
- `Variable.free_variables()` returns `{self}`
- `Constant.free_variables()` returns `{}`
- `FunctionApplication.free_variables()` returns union of args' free vars

**Missing**: Free variable computation for FORMULAS. The parsing result (prefix lists) needs a way to compute FV. This could be:

1. A standalone function `compute_free_variables(prefix_sentence)`
2. Or performed during sentence construction

Example implementation:
```python
def compute_formula_free_variables(prefix) -> FrozenSet[Variable]:
    """Compute free variables of a formula in prefix notation."""
    from model_checker.syntactic.terms import Term, Variable

    if isinstance(prefix, Term):
        return prefix.free_variables()

    if not isinstance(prefix, list) or len(prefix) == 0:
        return frozenset()

    head = prefix[0]

    # Atomic formulas: F[t1, ..., tn]
    if isinstance(head, str) and not head.startswith('\\'):
        # Predicate name, arguments are terms
        result = set()
        for arg in prefix[1:]:
            if isinstance(arg, Term):
                result.update(arg.free_variables())
        return frozenset(result)

    # Extremal constants
    if head in {'\\top', '\\bot'}:
        return frozenset()

    # Negation
    if head == '\\neg':
        return compute_formula_free_variables(prefix[1])

    # Binary connectives
    if head in {'\\wedge', '\\vee', '\\rightarrow', '\\leftrightarrow', '\\equiv'}:
        left_fv = compute_formula_free_variables(prefix[1])
        right_fv = compute_formula_free_variables(prefix[2])
        return left_fv | right_fv

    # Lambda application: ['\lambdaApp', var, body, arg]
    if head == '\\lambdaApp':
        var = prefix[1]
        body = prefix[2]
        arg = prefix[3]
        body_fv = compute_formula_free_variables(body)
        arg_fv = (compute_formula_free_variables(arg)
                  if isinstance(arg, list)
                  else arg.free_variables() if isinstance(arg, Term)
                  else frozenset())
        return (body_fv - {var}) | arg_fv

    # Quantifier: ['\forall', ['\lambda', var, body]]
    if head in {'\\forall', '\\exists'}:
        lambda_term = prefix[1]
        if isinstance(lambda_term, list) and lambda_term[0] == '\\lambda':
            var = lambda_term[1]
            body = lambda_term[2]
            body_fv = compute_formula_free_variables(body)
            return body_fv - {var}
        return frozenset()

    # Bare lambda (not a WFF, but compute anyway for error reporting)
    if head == '\\lambda':
        var = prefix[1]
        body = prefix[2]
        body_fv = compute_formula_free_variables(body)
        return body_fv - {var}

    return frozenset()
```

### 3. Parser Structure Analysis

The current parsing produces:

| Input | Parsed Prefix | Head Type |
|-------|---------------|-----------|
| `v_x` | `[Variable('v_x')]` | Variable (Term) |
| `a<>` | `[Constant('a')]` | Constant (Term) |
| `f<v_x>` | `[FunctionApplication('f', (v_x,))]` | FunctionApplication (Term) |
| `P[]` | `['P']` | str (predicate name) |
| `P[v_x]` | `['P', Variable('v_x')]` | str + Terms |
| `\lambda v_x. P[v_x]` | `['\\lambda', Variable('v_x'), ['P', Variable('v_x')]]` | str '\\lambda' |
| `\forall v_x. P[v_x]` | `['\\forall', ['\\lambda', Variable('v_x'), ['P', Variable('v_x')]]]` | str '\\forall' |

**Detection logic**:

```python
def is_syntactically_wff(prefix) -> Tuple[bool, str]:
    """Check if prefix represents a well-formed formula.

    Returns (is_wff, reason) tuple.
    """
    from model_checker.syntactic.terms import Term, Variable

    if not isinstance(prefix, list) or len(prefix) == 0:
        return False, "Empty or non-list prefix"

    head = prefix[0]

    # REJECT: Bare term
    if len(prefix) == 1 and isinstance(head, Term):
        return False, f"'{head}' is a term (denotes an individual), not a formula"

    # REJECT: Bare lambda
    if head == '\\lambda':
        return False, "Lambda abstraction is not a formula; use inside quantifier or apply to argument"

    # ACCEPT: Extremal constants
    if head in {'\\top', '\\bot'}:
        return True, ""

    # ACCEPT: Predicate (string head, possibly with term args)
    if isinstance(head, str) and not head.startswith('\\'):
        return True, ""  # Valid predicate application

    # ACCEPT: Unary operators (including quantifiers)
    if head in {'\\neg', '\\forall', '\\exists'}:
        return True, ""

    # ACCEPT: Binary operators
    if head in {'\\wedge', '\\vee', '\\rightarrow', '\\leftrightarrow', '\\equiv'}:
        return True, ""

    # ACCEPT: Lambda application
    if head == '\\lambdaApp':
        return True, ""

    return False, f"Unrecognized formula structure with head: {head}"
```

### 4. Where to Place Validation

**Option A: In Sentence.__init__() (Recommended)**

Place both checks in sequence:
1. Check syntactic well-formedness (is it a formula?)
2. Check closedness (does it have free variables?)

```python
def __init__(self, infix_sentence: FormulaString) -> None:
    # ... existing parsing ...
    self.prefix_sentence, self.complexity = self.prefix(infix_sentence)

    # NEW: Well-formedness validation
    self._validate_well_formedness()
```

**Advantages**:
- Single entry point for all sentence construction
- Fail-fast behavior
- Clear error messages

**Disadvantages**:
- May complicate internal operations that construct sentences programmatically

**Option B: In Syntax class during collection**

Check during `initialize_sentences()` after all sentences are collected.

**Disadvantages**:
- Delayed error detection
- Harder to associate error with specific input

### 5. Handling Open Formulas

The question arises: should open formulas be rejected outright, or allowed with a warning?

**Strict approach** (recommended for user-facing input):
- Reject formulas with free variables as invalid sentences
- Clear error: "Formula 'P[v_x]' has free variable v_x. Did you mean to quantify it?"

**Permissive approach** (for internal use):
- Allow open formulas but mark them
- Useful for building up formulas programmatically

**Recommendation**: Strict for user input, permissive internally. The `Sentence` class could have a flag `allow_open=False` that controls this.

### 6. Impact on Task 19's Workaround

The workaround in `structure.py` (`_is_nonpropositional_sentence`) can be removed once proper validation is in place. However, it should be done carefully:

1. First implement the validation in `Sentence.__init__()`
2. Verify all tests pass
3. Then remove the workaround
4. Verify tests still pass

## Recommendations

### Implementation Strategy

**Phase 1: Add free variable computation for formulas**
- Create function `compute_formula_free_variables(prefix) -> FrozenSet[Variable]`
- Add to `syntactic/` module (could be in `terms.py` or new `formulas.py`)
- Unit test with various formula structures

**Phase 2: Add well-formedness validation**
- Create helper `is_syntactically_wff(prefix) -> Tuple[bool, str]`
- Add `_validate_well_formedness()` method to Sentence class
- Call after parsing in `__init__()`
- Raise ParseError with helpful messages

**Phase 3: Add closedness checking**
- Compute free variables of parsed formula
- For sentences: require FV = {}
- For formulas that need assignment: could allow but warn (optional)

**Phase 4: Remove task 19 workaround**
- Delete `_is_nonpropositional_sentence()` method
- Remove guard in `interpret()`
- Verify all tests pass

### Test Cases

```python
# Should raise ParseError (not a WFF)
def test_bare_variable_rejected():
    with pytest.raises(ParseError, match="term.*not a formula"):
        Sentence("v_x")

def test_bare_constant_rejected():
    with pytest.raises(ParseError, match="term.*not a formula"):
        Sentence("sam<>")

def test_function_application_rejected():
    with pytest.raises(ParseError, match="term.*not a formula"):
        Sentence("f<v_x>")

def test_bare_lambda_rejected():
    with pytest.raises(ParseError, match="Lambda abstraction is not a formula"):
        Sentence("\\lambda v_x. P[v_x]")

# Should raise ParseError (WFF but not sentence - has free variables)
def test_open_formula_rejected():
    with pytest.raises(ParseError, match="free variable"):
        Sentence("P[v_x]")  # Has free variable v_x

# Should NOT raise (valid closed sentences)
def test_sentence_letter_accepted():
    s = Sentence("P[]")  # Zero-arity predicate, no free vars

def test_quantified_formula_accepted():
    s = Sentence("\\forall v_x. P[v_x]")  # Variable bound

def test_lambda_application_accepted():
    s = Sentence("(\\lambda v_x. P[v_x])(a<>)")  # Application closes the variable

def test_propositional_formula_accepted():
    s = Sentence("(A[] \\wedge B[])")  # Closed
```

## Decisions

1. **Implement two-level validation**: syntactic WFF check + closedness check
2. **Place validation in Sentence.__init__()**: fail-fast at construction time
3. **Compute free variables during validation**: needed for closedness check
4. **Strict mode for user input**: reject open formulas as invalid sentences
5. **Remove task 19 workaround after validation works**: clean architecture

## Risks & Mitigations

| Risk | Impact | Mitigation |
|------|--------|------------|
| Breaking internal formula construction | High | Add `allow_open` flag for internal use |
| Complex free variable computation | Medium | Thoroughly test with all formula forms |
| Missing edge cases in WFF check | Medium | Comprehensive test coverage |
| Performance impact of free var computation | Low | Lazy computation, cache result |

## Appendix

### Key Files

1. **terms.py** - Existing free_variables() for terms
2. **sentence.py** - Add validation and free_variables for formulas
3. **parsing.py** - Understand prefix structure produced
4. **structure.py** - Task 19 workaround to remove

### Logos Theory Manual References

- `02-constitutive.typ` lines 76-89: WFF grammar (def-wff)
- `02-constitutive.typ` lines 94-104: Free variables of formulas (def-fv-formula)
- `02-constitutive.typ` lines 107-113: Open vs closed formulas (def-open-closed)
- `02-constitutive.typ` lines 139-149: Derived operators (def-derived-operators)
- `03-dynamics.typ` lines 47-57: Extended WFF grammar with dynamical operators

### Test Commands

```bash
# Run syntactic tests
PYTHONPATH=code/src pytest code/src/model_checker/syntactic/tests/ -v

# Run first-order tests
PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/logos/subtheories/first-order/tests/ -v

# Run full test suite for regression
PYTHONPATH=code/src pytest code/tests/ -v
```
