# Implementation Plan: Add Next/Prev (X/Y) Defined Operator Classes

- **Task**: 111 - Add Next/Prev (X/Y) defined operator classes
- **Status**: [IMPLEMENTING]
- **Effort**: 1 hour
- **Dependencies**: 100 (completed)
- **Research Inputs**: specs/111_next_prev_defined_operators/reports/01_next-prev-operators.md
- **Artifacts**: plans/01_next-prev-operators.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: python
- **Lean Intent**: false

## Overview

Add DefNextOperator and DefPrevOperator as DefinedOperator subclasses to the bimodal operator collection. These temporal "next instant" and "previous instant" operators are defined as Next(phi) = U(phi, bot) and Prev(phi) = S(phi, bot), following the existing DefFutureOperator/DefPastOperator pattern exactly. The implementation is minimal (~25 lines of operator code) plus a test file covering signatures, derived_definition structure, registration, semantic equivalence, and prefix construction.

### Research Integration

Research report (01_next-prev-operators.md) provided:
- Complete DefinedOperator interface requirements (class attributes, derived_definition, print_method, _validate_arity)
- Exact derived_definition return format: `[UntilOperator, argument, [BotOperator]]` and `[SinceOperator, argument, [BotOperator]]`
- Template code from DefFutureOperator (line 1479) and DefPastOperator (line 1516) -- identical structure
- Registration location in bimodal_operators collection (line 1534)
- Test infrastructure patterns from test_until_since.py and test_bimodal.py
- Complete implementation recipe with docstrings

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

ROADMAP.md exists but contains no items. No alignment applicable.

## Goals & Non-Goals

**Goals**:
- Create DefNextOperator with name="\\next", arity=1, derived_definition returning [UntilOperator, argument, [BotOperator]]
- Create DefPrevOperator with name="\\prev", arity=1, derived_definition returning [SinceOperator, argument, [BotOperator]]
- Register both in bimodal_operators collection
- Write comprehensive tests following TDD (tests before implementation)
- Maintain all 171 existing bimodal tests passing

**Non-Goals**:
- Implementing true_at/false_at/find_truth_condition (DefinedOperator handles these automatically)
- Modifying the parser or infix notation handling
- Adding example formulas to examples.py (deferred to task 102/113)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| _validate_arity rejects derived_definition signature | H | L | Use `# type: ignore` comment matching existing pattern |
| BotOperator wrapping format wrong (bare vs list) | M | L | Research confirmed `[BotOperator]` wrapping; verify against TopOperator pattern |
| Existing tests break from operator registration | M | L | Run full test suite after registration; new operators don't affect existing name resolution |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |

Phases within the same wave can execute in parallel.

---

### Phase 1: Write Tests (TDD Red Phase) [COMPLETED]

**Goal**: Create comprehensive test file for DefNextOperator and DefPrevOperator before implementation, establishing the test-first contract.

**Tasks**:
- [x] Create test file `code/src/model_checker/theory_lib/bimodal/tests/unit/test_next_prev.py`
- [x] Write signature tests (TestDefNextOperatorSignature, TestDefPrevOperatorSignature): operator exists, arity == 1, name matches, is DefinedOperator subclass, has required methods
- [x] Write derived_definition structure tests (TestDefNextDefinition, TestDefPrevDefinition): returns list, uses correct base operator (UntilOperator/SinceOperator), uses [BotOperator] as guard
- [x] Write registration tests (TestOperatorRegistration): "\\next" and "\\prev" in bimodal_operators.operator_dictionary
- [x] Write semantic equivalence tests via run_test: `\\next A \\leftrightarrow (A \\Until \\bot)` and `\\prev A \\leftrightarrow (A \\Since \\bot)` are theorems
- [x] Write prefix construction tests: Syntax(["\\next A"], [], bimodal_operators) and Syntax(["\\prev A"], [], bimodal_operators) succeed without error
- [x] Verify tests fail (red phase) because classes do not yet exist

**Timing**: 30 minutes

**Depends on**: none

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_next_prev.py` - new test file

**Verification**:
- Test file exists and is syntactically valid Python
- Tests that reference class attributes fail with ImportError or AttributeError (red phase)

---

### Phase 2: Implement Operators and Verify (TDD Green Phase) [NOT STARTED]

**Goal**: Add DefNextOperator and DefPrevOperator classes and register them, making all tests pass.

**Tasks**:
- [ ] Add DefNextOperator class after DefPastOperator in `code/src/model_checker/theory_lib/bimodal/operators.py`: name="\\next", arity=1, derived_definition returns [UntilOperator, argument, [BotOperator]], print_method delegates to print_over_times
- [ ] Add DefPrevOperator class after DefNextOperator: name="\\prev", arity=1, derived_definition returns [SinceOperator, argument, [BotOperator]], print_method delegates to print_over_times
- [ ] Register DefNextOperator and DefPrevOperator in bimodal_operators collection (after DefPastOperator in the defined operators section)
- [ ] Run new tests: `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/unit/test_next_prev.py -v`
- [ ] Run full existing test suite: `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/ -v`
- [ ] Verify all new tests pass (green phase) and all 171 existing tests still pass

**Timing**: 30 minutes

**Depends on**: 1

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/operators.py` - add two class definitions (~25 lines each) and two registrations

**Verification**:
- All new test_next_prev.py tests pass
- All 171 existing bimodal tests pass
- `DefNextOperator` and `DefPrevOperator` appear in bimodal_operators.operator_dictionary

## Testing & Validation

- [ ] Signature tests: both operators have correct name, arity, and DefinedOperator inheritance
- [ ] Definition tests: derived_definition returns correct prefix-notation lists
- [ ] Registration tests: operators found in bimodal_operators.operator_dictionary
- [ ] Semantic equivalence: Next(A) <-> U(A, bot) is a theorem (no countermodel)
- [ ] Semantic equivalence: Prev(A) <-> S(A, bot) is a theorem (no countermodel)
- [ ] Prefix construction: Syntax can parse "\\next A" and "\\prev A"
- [ ] Regression: all 171 existing bimodal tests still pass

## Artifacts & Outputs

- `specs/111_next_prev_defined_operators/plans/01_next-prev-operators.md` (this plan)
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_next_prev.py` (new test file)
- `code/src/model_checker/theory_lib/bimodal/operators.py` (modified: two new classes + registration)

## Rollback/Contingency

Remove the two class definitions from operators.py and their entries from bimodal_operators. Delete test_next_prev.py. Since no existing code is modified (only additions), rollback is a simple deletion. Git revert of the implementation commit achieves this cleanly.
