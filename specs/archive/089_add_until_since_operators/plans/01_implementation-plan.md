# Implementation Plan: Add Until and Since Operators

- **Task**: 89 - add_until_since_operators
- **Status**: [NOT STARTED]
- **Effort**: 4 hours
- **Dependencies**: None (builds on existing temporal operator patterns)
- **Research Inputs**: specs/089_add_until_since_operators/reports/01_until-since-research.md
- **Artifacts**: plans/01_implementation-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-formats.md, tasks.md
- **Type**: z3
- **Lean Intent**: false

## Overview

Implement Until (U) and Since (S) temporal operators in the bimodal operators.py file. These binary operators enable expressing "event eventually holds while guard holds in between" semantics required by 22 of 42 BX axiom constructors. The implementation follows existing FutureOperator/PastOperator patterns, using ProofChecker-compatible strict witness semantics with open guard intervals.

### Research Integration

Key findings from research report (01_until-since-research.md):
- **ProofChecker semantics**: Until uses `exists s > t, event(s) AND forall r in (t,s): guard(r)` - strict witness, open guard
- **Burgess convention**: `untl(event, guard)` - event is first argument, guard is second
- **Z3 encoding**: Nested quantifiers (ExistsTime containing ForAllTime) with unique variable names
- **Boundary behavior**: Vacuously false at boundary times when no witness exists

## Goals & Non-Goals

**Goals**:
- Implement UntilOperator with true_at, false_at, find_truth_condition, print_method
- Implement SinceOperator as temporal mirror of Until
- Register both operators in bimodal_operators collection
- Ensure correct semantics: strict witness, open guard interval
- Handle bounded model edge cases (boundary times)

**Non-Goals**:
- Performance optimization for deeply nested formulas (defer to future work)
- Adding Until/Since to other theory_lib variants (logos, etc.)
- Implementing weak versions (non-strict witness or closed guard)
- Full BX axiom validation suite (separate task)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Nested quantifier performance | M | M | Use unique variable names; test with small M values |
| Variable name collision | H | L | Use distinct prefixes (until_witness_, until_guard_, since_*) |
| Boundary time vacuous truth | M | M | Document behavior; test edge cases explicitly |
| Open vs closed interval confusion | H | M | Strict adherence to ProofChecker semantics; comprehensive tests |

## Implementation Phases

### Phase 1: UntilOperator Core Implementation [COMPLETED]

**Goal**: Implement the Until operator with correct Z3 encoding for true_at and false_at methods.

**Tasks**:
- [ ] Add UntilOperator class after PastOperator (line ~812)
- [ ] Implement true_at: ExistsTime(witness) with nested ForAllTime(guard)
- [ ] Implement false_at: ForAllTime(witness) with nested ExistsTime(guard failure)
- [ ] Use unique variable names: until_witness_time, until_guard_time

**Timing**: 45 minutes

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/operators.py` - Add UntilOperator class

**Verification**:
- Class compiles without syntax errors
- true_at returns Z3 expression with nested quantifiers
- Variable names are unique to prevent collision

---

### Phase 2: UntilOperator Extension Methods [COMPLETED]

**Goal**: Implement find_truth_condition and print_method for Until operator.

**Tasks**:
- [ ] Implement find_truth_condition: iterate over times, check witness condition
- [ ] Implement print_method: use print_over_times pattern from FutureOperator
- [ ] Handle boundary cases (no future times = vacuously false)

**Timing**: 45 minutes

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/operators.py` - Complete UntilOperator

**Verification**:
- find_truth_condition returns dict mapping world_id to (true_times, false_times)
- Boundary time handling matches research specification

---

### Phase 3: SinceOperator Implementation [COMPLETED]

**Goal**: Implement Since operator as temporal mirror of Until.

**Tasks**:
- [ ] Add SinceOperator class after UntilOperator
- [ ] Implement true_at: ExistsTime(past witness) with ForAllTime(guard in (s,t))
- [ ] Implement false_at: ForAllTime with ExistsTime guard failure
- [ ] Implement find_truth_condition for past-directed evaluation
- [ ] Implement print_method using print_over_times

**Timing**: 45 minutes

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/operators.py` - Add SinceOperator class

**Verification**:
- Time ordering reversed from Until (s < t instead of t < s)
- Guard interval is (s, t) not (t, s)
- Variable names use since_ prefix

---

### Phase 4: Registration and Integration [COMPLETED]

**Goal**: Register operators and verify integration with existing infrastructure.

**Tasks**:
- [ ] Add UntilOperator and SinceOperator to bimodal_operators collection
- [ ] Verify operators appear in correct position (after PastOperator, before defined operators)
- [ ] Run existing bimodal tests to ensure no regressions

**Timing**: 15 minutes

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/operators.py` - Update OperatorCollection

**Verification**:
- Operators registered in bimodal_operators
- Existing tests pass (pytest code/src/model_checker/theory_lib/bimodal/tests/)

---

### Phase 5: Unit Tests [COMPLETED]

**Goal**: Create comprehensive unit tests for Until and Since operators.

**Tasks**:
- [ ] Create test file: test_until_since.py in tests/unit/
- [ ] Test true_at returns Z3 expression
- [ ] Test false_at returns Z3 expression with correct structure
- [ ] Test find_truth_condition with simple extensions
- [ ] Test boundary cases (vacuous falsity at boundaries)
- [ ] Test nested quantifier variable names are unique

**Timing**: 1 hour

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_until_since.py` - New file

**Verification**:
- All new tests pass
- Tests cover: basic semantics, boundary cases, variable naming

---

### Phase 6: Integration Tests and Documentation [COMPLETED]

**Goal**: Test with actual model evaluation and document the operators.

**Tasks**:
- [ ] Add integration test exercising Until/Since with concrete models
- [ ] Test U(p, top) equivalent to F(p) pattern
- [ ] Test S(p, top) equivalent to P(p) pattern  
- [ ] Update operators.py module docstring to include Until/Since
- [ ] Add docstrings with examples to both operator classes

**Timing**: 30 minutes

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/tests/integration/test_until_since_integration.py` - New file
- `code/src/model_checker/theory_lib/bimodal/operators.py` - Update module docstring

**Verification**:
- Integration tests pass with N=2, M=2 model
- Module docstring lists Until and Since operators
- Docstrings follow existing operator documentation pattern

## Testing & Validation

- [ ] Unit tests for UntilOperator.true_at, false_at, find_truth_condition
- [ ] Unit tests for SinceOperator.true_at, false_at, find_truth_condition
- [ ] Boundary case tests (first/last time in interval)
- [ ] Integration test: U(p, top) behaves like F(p)
- [ ] Integration test: S(p, top) behaves like P(p)
- [ ] Regression test: existing bimodal tests still pass
- [ ] Variable collision test: nested formulas with multiple Until/Since

## Artifacts & Outputs

- `code/src/model_checker/theory_lib/bimodal/operators.py` - Modified with UntilOperator, SinceOperator
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_until_since.py` - New unit tests
- `code/src/model_checker/theory_lib/bimodal/tests/integration/test_until_since_integration.py` - New integration tests
- `specs/089_add_until_since_operators/summaries/01_implementation-summary.md` - Execution summary

## Rollback/Contingency

If implementation fails or causes regressions:
1. Revert operators.py to pre-implementation state using git checkout
2. Remove test files (tests are isolated, no dependencies)
3. No state.json or system changes required for rollback

The implementation is additive (new classes appended) and isolated from existing operator logic, making rollback straightforward.
