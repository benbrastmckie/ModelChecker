# Implementation Plan: Task #20

- **Task**: 20 - add_parser_well_formedness_checking
- **Status**: [COMPLETED]
- **Effort**: 4 hours
- **Dependencies**: Task #19 (completed)
- **Research Inputs**: specs/020_add_parser_well_formedness_checking/reports/research-002.md
- **Artifacts**: plans/implementation-001.md (this file)
- **Standards**:
  - .claude/context/core/standards/plan.md
  - .claude/context/core/standards/status-markers.md
  - .claude/context/core/system/artifact-management.md
  - .claude/context/core/standards/tasks.md
- **Type**: python
- **Lean Intent**: false

## Overview

Add well-formedness checking to the parser to reject term-only sentences and other syntactically ill-formed inputs at parse time. The implementation follows a two-level validation approach from the Logos Theory manual: (1) syntactic category check verifying the input is a formula according to the WFF grammar, and (2) closedness check verifying the formula has no free variables. Validation will be placed in `Sentence.__init__()` for fail-fast behavior. After validation is working, the task 19 workaround in `structure.py` will be removed.

### Research Integration

The corrected research (research-002.md) identifies the proper definition of well-formedness:
- **WFF Grammar**: Bare terms and bare lambdas are NOT formulas; only lambda applications are
- **Sentence Definition**: A sentence is a CLOSED formula (FV(phi) = empty set)
- **Implementation Location**: `Sentence.__init__()` for fail-fast behavior

## Goals & Non-Goals

**Goals**:
- Reject term-only inputs (variables, constants, function applications) with clear error messages
- Reject bare lambda abstractions (not in WFF grammar) with helpful suggestions
- Reject open formulas (with free variables) as invalid sentences
- Accept valid closed formulas (zero-arity predicates, quantified formulas, lambda applications)
- Remove task 19 workaround from structure.py after validation works
- Maintain backward compatibility for all valid existing formulas

**Non-Goals**:
- Support for open formulas (formulas with free variables) - these are not sentences
- Internal "permissive mode" for programmatic formula construction - keep simple
- Changes to parsing infrastructure (tokenizer, parser) - validation is post-parse

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Breaking existing valid formulas | High | Low | Comprehensive test coverage with existing test suite |
| Complex free variable computation | Medium | Medium | Follow research code examples, thorough unit testing |
| Edge cases in WFF detection | Medium | Medium | Test all grammar productions systematically |
| Performance regression from validation | Low | Low | Validation is O(formula_size), negligible vs parsing |

## Implementation Phases

### Phase 1: Add Free Variable Computation for Formulas [COMPLETED]

**Goal**: Create a function to compute free variables of parsed formula prefixes

**Tasks**:
- [ ] Create new file `code/src/model_checker/syntactic/formulas.py` with `compute_formula_free_variables(prefix)` function
- [ ] Handle all prefix structures: predicates, extremals, negation, binary connectives, quantifiers, lambda applications
- [ ] Handle Term objects as arguments (delegate to `term.free_variables()`)
- [ ] Add unit tests for free variable computation

**Timing**: 1 hour

**Files to create**:
- `code/src/model_checker/syntactic/formulas.py` - New module for formula-level operations

**Files to modify**:
- `code/src/model_checker/syntactic/__init__.py` - Export new function

**Verification**:
- Unit tests pass for all formula structures
- Free variables computed correctly for predicates, quantifiers, lambda applications

---

### Phase 2: Add WFF Syntactic Category Checking [COMPLETED]

**Goal**: Create validation to detect non-formula inputs (terms, bare lambdas)

**Tasks**:
- [ ] Add `is_syntactically_wff(prefix)` function to `formulas.py` returning `(bool, str)` tuple
- [ ] Detect and reject bare Term objects (variables, constants, function applications)
- [ ] Detect and reject bare lambda abstractions (`\lambda` at head)
- [ ] Accept valid formula structures (predicates, connectives, quantifiers, lambda applications)
- [ ] Add unit tests for WFF detection

**Timing**: 45 minutes

**Files to modify**:
- `code/src/model_checker/syntactic/formulas.py` - Add WFF checking function

**Verification**:
- Tests reject `v_x`, `a<>`, `f<v_x>` as terms
- Tests reject `\lambda v_x. P[v_x]` as bare lambda
- Tests accept `P[]`, `\forall v_x. P[v_x]`, `(\lambda v_x. P[v_x])(a<>)`

---

### Phase 3: Integrate Validation into Sentence.__init__() [COMPLETED]

**Goal**: Add validation to Sentence class for fail-fast error detection

**Tasks**:
- [ ] Add `_validate_well_formedness()` method to Sentence class
- [ ] Call `is_syntactically_wff()` first, raise ParseError if not WFF
- [ ] Call `compute_formula_free_variables()` second, raise ParseError if open formula
- [ ] Call validation after `self.prefix()` in `__init__()`
- [ ] Add integration tests for Sentence construction with invalid inputs

**Timing**: 45 minutes

**Files to modify**:
- `code/src/model_checker/syntactic/sentence.py` - Add validation method and call in __init__

**Verification**:
- `Sentence("v_x")` raises ParseError with "term" in message
- `Sentence("\\lambda v_x. P[v_x]")` raises ParseError with "Lambda" in message
- `Sentence("P[v_x]")` raises ParseError with "free variable" in message
- `Sentence("P[]")` succeeds
- `Sentence("\\forall v_x. P[v_x]")` succeeds

---

### Phase 4: Remove Task 19 Workaround [COMPLETED]

**Goal**: Clean up the workaround in structure.py now that validation is in place

**Tasks**:
- [ ] Delete `_is_nonpropositional_sentence()` method from ModelStructure class
- [ ] Remove the call to `_is_nonpropositional_sentence()` in `interpret()` method
- [ ] Verify all tests still pass (ill-formed inputs now rejected earlier)
- [ ] Update docstrings if needed

**Timing**: 30 minutes

**Files to modify**:
- `code/src/model_checker/models/structure.py` - Remove workaround method and call

**Verification**:
- Full test suite passes
- No regressions in first-order logic tests
- Ill-formed inputs rejected at parse time, not interpretation time

---

### Phase 5: Comprehensive Testing and Documentation [COMPLETED]

**Goal**: Ensure full coverage and document the validation behavior

**Tasks**:
- [ ] Add comprehensive test file `code/tests/unit/syntactic/test_well_formedness.py`
- [ ] Test all edge cases from research report table
- [ ] Run full test suite to verify no regressions
- [ ] Add docstrings to new functions explaining WFF and sentence criteria
- [ ] Create implementation summary

**Timing**: 1 hour

**Files to create**:
- `code/tests/unit/syntactic/test_well_formedness.py` - Comprehensive well-formedness tests
- `specs/020_add_parser_well_formedness_checking/summaries/implementation-summary-YYYYMMDD.md`

**Verification**:
- All new tests pass
- Full test suite passes: `PYTHONPATH=code/src pytest code/tests/ -v`
- Coverage maintained or improved

## Testing & Validation

- [ ] Unit tests for `compute_formula_free_variables()` covering all formula types
- [ ] Unit tests for `is_syntactically_wff()` covering all valid/invalid cases
- [ ] Integration tests for `Sentence()` constructor with invalid inputs
- [ ] Regression tests: existing test suite passes unchanged
- [ ] Edge cases from research: `P[]`, `P[v_x]`, `\forall v_x. P[v_x]`, `v_x`, `a<>`, `\lambda v_x. P[v_x]`, `(\lambda v_x. P[v_x])(a<>)`

Test commands:
```bash
# Run syntactic tests
PYTHONPATH=code/src pytest code/src/model_checker/syntactic/tests/ -v

# Run new well-formedness tests
PYTHONPATH=code/src pytest code/tests/unit/syntactic/test_well_formedness.py -v

# Run first-order tests
PYTHONPATH=code/src pytest code/tests/unit/theory_lib/logos/subtheories/first-order/ -v

# Run full test suite
PYTHONPATH=code/src pytest code/tests/ -v
```

## Artifacts & Outputs

- `code/src/model_checker/syntactic/formulas.py` - New module with WFF checking and free variable computation
- `code/tests/unit/syntactic/test_well_formedness.py` - Comprehensive tests
- `specs/020_add_parser_well_formedness_checking/summaries/implementation-summary-YYYYMMDD.md` - Summary

## Rollback/Contingency

If implementation causes unexpected regressions:
1. Revert changes to `sentence.py` first (removes validation from constructor)
2. Keep `formulas.py` as utility functions (no harm if not called)
3. Restore `_is_nonpropositional_sentence()` in `structure.py` if removed
4. Investigate failing tests to understand the issue

Git provides full rollback capability: `git revert` or `git checkout` for individual files.
