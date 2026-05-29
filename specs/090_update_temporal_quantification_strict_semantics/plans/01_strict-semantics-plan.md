# Implementation Plan: Task #90

- **Task**: 90 - Update temporal quantification to strict semantics
- **Status**: [NOT STARTED]
- **Effort**: 4 hours
- **Dependencies**: Task 89 (Until/Since operators) - COMPLETED
- **Research Inputs**: specs/090_update_temporal_quantification_strict_semantics/reports/01_strict-semantics-research.md
- **Artifacts**: plans/01_strict-semantics-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: z3
- **Lean Intent**: false

## Overview

This implementation aligns the ModelChecker's temporal semantics with the ProofChecker (Lean). The research confirmed that temporal ordering is already correct (strict `<` ordering in G, H, F, P, Until, Since). The changes required are:

1. **Quantification scope**: Change `ForAllTime`/`ExistsTime` from world-interval to all-D quantification
2. **Atom semantics**: Add domain check so atoms are FALSE outside world's domain (not undefined)
3. **Extension computation**: Update `find_truth_condition` methods to consider all times in D
4. **Test updates**: T-axiom tests become invalid; add seriality axiom tests

### Research Integration

Key findings from research report (01_strict-semantics-research.md):
- Strict ordering (`<`) already correct in all temporal operators
- ProofChecker quantifies over ALL times in domain D, not restricted to world interval
- Atoms should evaluate to FALSE at times outside the world's domain
- T-axioms (G(phi) -> phi) are NOT valid under strict semantics
- Seriality axioms (T -> F(T)) are valid and replace T-axioms

## Goals & Non-Goals

**Goals**:
- Full semantic alignment with ProofChecker Truth.lean
- Change `ForAllTime`/`ExistsTime` to quantify over all times in domain D
- Add domain check to atom evaluation in `true_at`
- Update `find_truth_condition` methods for consistent extension computation
- Update/add tests to verify new semantics
- Preserve existing behavior for non-temporal formulas

**Non-Goals**:
- Changes to the syntactic layer
- Changes to Until/Since operators (already correctly implemented in Task 89)
- Performance optimization (correctness first)
- Adding new temporal operators

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| T-axiom tests fail | M | H | Expected behavior; update tests to expect invalidity |
| Extension computation breaks | H | M | Run full test suite after each change; incremental approach |
| Z3 performance degrades | M | L | Monitor solver times; all-D quantification is bounded by M |
| Atom domain check breaks modal operators | H | M | Test modal operators explicitly after atom change |

## Implementation Phases

### Phase 1: Update Temporal Quantification Scope [NOT STARTED]

**Goal**: Modify `ForAllTime` and `ExistsTime` to quantify over all times in domain D instead of world-specific intervals.

**Tasks**:
- [ ] Modify `ForAllTime` in semantic.py to use `is_valid_time(time_var)` instead of `is_valid_time_for_world(world, time_var)`
- [ ] Modify `ExistsTime` in semantic.py similarly
- [ ] Add clarifying comments explaining the ProofChecker alignment
- [ ] Run existing temporal operator tests to verify structure unchanged

**Timing**: 0.5 hours

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/semantic.py` - ForAllTime and ExistsTime methods (lines 209-245)

**Verification**:
- Unit tests in `test_foralltime.py` should still pass (structure tests)
- Temporal operators should still produce quantified formulas

---

### Phase 2: Add Domain Check to Atom Evaluation [NOT STARTED]

**Goal**: Ensure atoms evaluate to FALSE at times outside the world's domain, matching ProofChecker semantics.

**Tasks**:
- [ ] Modify `true_at` method in semantic.py to add domain check for sentence letters
- [ ] When sentence_letter is not None, wrap truth condition with `is_valid_time_for_world` check
- [ ] Add comment explaining ProofChecker alignment (`atom_false_of_not_domain` theorem)
- [ ] Create unit test for atom evaluation at boundary times

**Timing**: 0.75 hours

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/semantic.py` - true_at method (lines 887-916)

**Code change**:
```python
# Current (line 909-911):
if sentence_letter is not None:
    eval_world_state = z3.Select(world_array, eval_time)
    return self.truth_condition(eval_world_state, sentence_letter)

# New:
if sentence_letter is not None:
    # Atoms are FALSE outside the world's domain (ProofChecker alignment)
    in_domain = self.is_valid_time_for_world(eval_world, eval_time)
    eval_world_state = z3.Select(world_array, eval_time)
    return z3.And(
        in_domain,
        self.truth_condition(eval_world_state, sentence_letter)
    )
```

**Verification**:
- Create test case: atom p at time outside world interval should be false
- Existing extensional operator tests should still pass

---

### Phase 3: Update find_truth_condition Methods [NOT STARTED]

**Goal**: Update extension computation in operators to consider all times in D, not just world-specific intervals.

**Tasks**:
- [ ] Update `FutureOperator.find_truth_condition` to check all D times, not just world interval
- [ ] Update `PastOperator.find_truth_condition` similarly
- [ ] Update `UntilOperator.find_truth_condition` to handle all-D quantification
- [ ] Update `SinceOperator.find_truth_condition` similarly
- [ ] Add helper method to get all valid times in D for a semantics instance

**Timing**: 1.5 hours

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/operators.py` - FutureOperator.find_truth_condition (lines 578-643)
- `code/src/model_checker/theory_lib/bimodal/operators.py` - PastOperator.find_truth_condition (lines 734-799)
- `code/src/model_checker/theory_lib/bimodal/operators.py` - UntilOperator.find_truth_condition (lines 945-1001)
- `code/src/model_checker/theory_lib/bimodal/operators.py` - SinceOperator.find_truth_condition (lines 1148-1204)

**Key changes**:
1. Replace `time_interval` (from world) with `all_D_times` (from semantics)
2. Consider atoms outside domain as false when computing extensions
3. Ensure consistent behavior between Z3 evaluation and Python extension computation

**Verification**:
- Temporal operator truth values should match between Z3 evaluation and extension computation
- Create test comparing `true_at` result with extension at specific times

---

### Phase 4: Test Updates and Validation [NOT STARTED]

**Goal**: Update existing tests and add new tests to verify ProofChecker-aligned semantics.

**Tasks**:
- [ ] Identify any T-axiom tests (G(p) -> p) and update expectations to invalid
- [ ] Add seriality axiom tests: T -> F(T) should be valid, T -> P(T) should be valid
- [ ] Add boundary time tests: atom evaluation at times outside world interval
- [ ] Add integration tests comparing ModelChecker results with known ProofChecker results
- [ ] Run full test suite and document any additional failures

**Timing**: 1.25 hours

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_foralltime.py` - Add domain-scope tests
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_bimodal.py` - Update axiom tests
- `code/src/model_checker/theory_lib/bimodal/tests/integration/` - Add alignment tests

**New test cases**:
```python
# Seriality axiom test (should find no countermodel = valid)
def test_seriality_future():
    """T -> F(T) should be valid under strict semantics."""
    # Top implies eventually Top is true
    
# T-axiom test (should find countermodel = invalid)
def test_t_axiom_invalid():
    """G(p) -> p should NOT be valid under strict semantics."""
    # There exists a model where G(p) is true but p is false at current time
    
# Atom boundary test
def test_atom_false_outside_domain():
    """Atoms should be false at times outside the world's domain."""
```

**Verification**:
- All new tests pass
- Full test suite passes (may need to update some existing tests)
- Document any semantic differences discovered

---

## Testing & Validation

- [ ] Run `pytest code/src/model_checker/theory_lib/bimodal/tests/unit/test_foralltime.py` after Phase 1
- [ ] Run `pytest code/src/model_checker/theory_lib/bimodal/tests/` after each phase
- [ ] Run full model checker test suite: `pytest code/`
- [ ] Manually verify G(p) -> p finds countermodel (T-axiom invalid)
- [ ] Manually verify T -> F(T) finds no countermodel (seriality valid)
- [ ] Compare results with ProofChecker on 2-3 known formulas

## Artifacts & Outputs

- plans/01_strict-semantics-plan.md (this file)
- Modified: code/src/model_checker/theory_lib/bimodal/semantic.py
- Modified: code/src/model_checker/theory_lib/bimodal/operators.py
- Modified/New: code/src/model_checker/theory_lib/bimodal/tests/unit/test_foralltime.py
- Modified: code/src/model_checker/theory_lib/bimodal/tests/unit/test_bimodal.py
- New: code/src/model_checker/theory_lib/bimodal/tests/integration/test_strict_semantics.py
- summaries/01_strict-semantics-summary.md (after implementation)

## Rollback/Contingency

If the changes cause widespread test failures or break critical functionality:

1. **Git revert**: All changes are contained in semantic.py and operators.py; can revert individual files
2. **Incremental approach**: Each phase is independently reversible
3. **Feature flag**: Could introduce `strict_semantics=True/False` setting if backward compatibility needed
4. **Test isolation**: New tests in separate file can be skipped if needed

The changes are localized to:
- 2 methods in semantic.py (ForAllTime, ExistsTime)
- 1 method in semantic.py (true_at atom handling)
- 4 methods in operators.py (find_truth_condition variants)

No schema changes, no new dependencies, no syntactic layer changes.
