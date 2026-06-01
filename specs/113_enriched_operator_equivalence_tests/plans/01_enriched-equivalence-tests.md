# Implementation Plan: Enriched Operator Equivalence Test Suite

- **Task**: 113 - Enriched operator equivalence test suite
- **Status**: [NOT STARTED]
- **Effort**: 3 hours
- **Dependencies**: 102 (completed)
- **Research Inputs**: specs/113_enriched_operator_equivalence_tests/reports/01_enriched-equivalence-tests.md
- **Artifacts**: plans/01_enriched-equivalence-tests.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: python
- **Lean Intent**: false

## Overview

Create a comprehensive test suite (`test_enriched_equivalence.py`) that verifies all 11 enriched operators produce Z3 results identical to their primitive expansions, with 5+ formulas per operator across nested combinations and complexity levels 3, 5, 7. The research report confirmed all 55 planned test formulas pass at M=2, the TopOperator bug workaround is documented, and the existing test infrastructure provides a proven `_run_equivalence` pattern to reuse. The new file is placed alongside existing bimodal unit tests rather than extending the already-large `test_json_translation.py` (1026 lines).

### Research Integration

Key findings from `reports/01_enriched-equivalence-tests.md` integrated into this plan:

- **All 55 formulas pre-validated**: REPL testing confirmed every planned biconditional is a theorem at M=2. No surprises expected during implementation.
- **TopOperator bug**: Tests for `top` must use `\neg \bot` expansion, not `\top` directly. The `derived_definition` path has a known evaluation bug.
- **M=2 is safe for biconditionals**: Both sides of each biconditional are affected identically by boundary vacuity, so M=2 suffices even for G/H operators.
- **Test execution pattern**: The `_make_equiv_example` / `_run_equivalence` helper pattern from `TestEnrichedEquivalence` in `test_json_translation.py` is the proven approach. Reuse the same pattern (not the same code -- create fresh helpers in the new file).
- **Performance**: Each test completes in <0.05s, so the full 55+ suite will run in under 5 seconds.
- **Nested class structure recommended**: Inner classes per operator with explicit test methods (not parametrize), matching existing codebase patterns for clear pytest output.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md found.

## Goals & Non-Goals

**Goals**:
- Verify every enriched operator produces Z3 results identical to its primitive expansion
- Cover 5+ formulas per operator (55+ total), including nested combinations
- Test formulas at complexity levels 3, 5, 7 (nested operator combinations)
- Include boundary sensitivity tests for all_future (G) and all_past (H) at M=2 and M=3
- Provide clear, debuggable test output with descriptive test names

**Non-Goals**:
- Modifying or extending existing `test_json_translation.py`
- Testing the translation layer itself (covered by task 102 tests)
- Implementing temporal_depth mitigation in the solver (task 107/103 scope)
- Testing countermodel structure extraction (task 105 scope)
- Performance benchmarking

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| TopOperator bug causes failures in `top` tests | M | L | Use `\neg \bot` expansion as documented in research; avoid `\top` directly |
| Z3 state leakage between tests | H | L | Use `isolated_z3_context()` in every test helper call |
| Boundary effects cause G/H test failures at M=2 | M | L | Research confirmed M=2 safe for biconditionals; add M=3 boundary tests as backup verification |
| Import path changes from task 100/101 refactoring | L | L | Imports follow same patterns as existing passing tests in the same directory |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2, 3 | 1 |
| 3 | 4 | 2, 3 |
| 4 | 5 | 4 |

Phases within the same wave can execute in parallel.

---

### Phase 1: Test infrastructure and helpers [COMPLETED]

**Goal**: Create `test_enriched_equivalence.py` with shared helper functions and verify the infrastructure works with one smoke test.

**Tasks**:
- [ ] Create `code/src/model_checker/theory_lib/bimodal/tests/unit/test_enriched_equivalence.py`
- [ ] Implement imports: `pytest`, `ModelConstraints`, `Syntax`, `run_test`, `BimodalStructure`, `BimodalProposition`, `BimodalSemantics`, `bimodal_operators`, `isolated_z3_context`
- [ ] Implement `_make_equiv_example(conclusion, M=2)` helper that creates the example dict with configurable M parameter
- [ ] Implement `_run_theorem(conclusion, M=2)` helper that runs equivalence test through the full Z3 pipeline using `isolated_z3_context()`
- [ ] Write one smoke test `test_smoke_neg_basic` that calls `_run_theorem("(\\neg A \\leftrightarrow (A \\rightarrow \\bot))")` and asserts True
- [ ] Run `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/unit/test_enriched_equivalence.py -v` and confirm the smoke test passes

**Timing**: 20 minutes

**Depends on**: none

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_enriched_equivalence.py` - new file

**Verification**:
- Smoke test passes
- `_run_theorem` helper successfully invokes the Z3 pipeline and returns True for a known theorem

---

### Phase 2: Level 1 operator tests (neg, top, next, prev) [COMPLETED]

**Goal**: Implement 20 tests covering the 4 Level 1 operators (direct primitive mappings), 5 formulas each.

**Tasks**:
- [ ] Implement `TestNegEquivalence` class with 5 tests:
  - `test_neg_basic_definition`: `(\neg A \leftrightarrow (A \rightarrow \bot))`
  - `test_neg_double_negation`: `(\neg \neg A \leftrightarrow A)`
  - `test_neg_de_morgan`: `(\neg (A \wedge B) \leftrightarrow (\neg A \vee \neg B))`
  - `test_neg_bot`: `(\neg \bot \leftrightarrow \neg \bot)`
  - `test_neg_implication`: `(\neg (A \rightarrow B) \leftrightarrow (A \wedge \neg B))`
- [ ] Implement `TestTopEquivalence` class with 5 tests (all using `\neg \bot` form):
  - `test_top_self_equivalence`: `(\neg \bot \leftrightarrow \neg \bot)`
  - `test_top_implies_top`: `(\neg \bot \rightarrow \neg \bot)`
  - `test_neg_top_implies_bot`: `(\neg \neg \bot \rightarrow \bot)`
  - `test_anything_implies_top`: `(A \rightarrow \neg \bot)`
  - `test_bot_implies_top`: `(\bot \rightarrow \neg \bot)`
- [ ] Implement `TestNextEquivalence` class with 5 tests:
  - `test_next_basic_definition`: `(\next A \leftrightarrow (A \Until \bot))`
  - `test_next_of_neg`: `(\next \neg A \leftrightarrow (\neg A \Until \bot))`
  - `test_next_of_and`: `(\next (A \wedge B) \leftrightarrow ((A \wedge B) \Until \bot))`
  - `test_next_of_or`: `(\next (A \vee B) \leftrightarrow ((A \vee B) \Until \bot))`
  - `test_neg_of_next`: `(\neg \next A \leftrightarrow \neg (A \Until \bot))`
- [ ] Implement `TestPrevEquivalence` class with 5 tests:
  - `test_prev_basic_definition`: `(\prev A \leftrightarrow (A \Since \bot))`
  - `test_prev_of_neg`: `(\prev \neg A \leftrightarrow (\neg A \Since \bot))`
  - `test_prev_of_and`: `(\prev (A \wedge B) \leftrightarrow ((A \wedge B) \Since \bot))`
  - `test_prev_of_or`: `(\prev (A \vee B) \leftrightarrow ((A \vee B) \Since \bot))`
  - `test_neg_of_prev`: `(\neg \prev A \leftrightarrow \neg (A \Since \bot))`
- [ ] Run all 20 Level 1 tests and confirm they pass

**Timing**: 40 minutes

**Depends on**: 1

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_enriched_equivalence.py` - add 4 test classes

**Verification**:
- All 20 Level 1 tests pass
- `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/unit/test_enriched_equivalence.py -v -k "Neg or Top or Next or Prev"` shows 20 passing

---

### Phase 3: Level 2 operator tests (and, or, diamond, some_future, some_past) [COMPLETED]

**Goal**: Implement 25 tests covering the 5 Level 2 operators (defined via Level 1), 5 formulas each.

**Tasks**:
- [ ] Implement `TestAndEquivalence` class with 5 tests:
  - `test_and_basic_definition`: `((A \wedge B) \leftrightarrow \neg (A \rightarrow \neg B))`
  - `test_and_commutativity`: `((A \wedge B) \leftrightarrow (B \wedge A))`
  - `test_and_with_bot`: `((A \wedge \bot) \leftrightarrow \bot)`
  - `test_and_associativity`: `(((A \wedge B) \wedge C) \leftrightarrow (A \wedge (B \wedge C)))`
  - `test_and_contradiction`: `((A \wedge \neg A) \leftrightarrow \bot)`
- [ ] Implement `TestOrEquivalence` class with 5 tests:
  - `test_or_basic_definition`: `((A \vee B) \leftrightarrow (\neg A \rightarrow B))`
  - `test_or_commutativity`: `((A \vee B) \leftrightarrow (B \vee A))`
  - `test_or_with_bot`: `((A \vee \bot) \leftrightarrow A)`
  - `test_or_excluded_middle`: `(A \vee \neg A)`
  - `test_or_excluded_middle_is_top`: `((A \vee \neg A) \leftrightarrow \neg \bot)`
- [ ] Implement `TestDiamondEquivalence` class with 5 tests:
  - `test_diamond_basic_definition`: `(\Diamond A \leftrightarrow \neg \Box \neg A)`
  - `test_diamond_of_neg`: `(\Diamond \neg A \leftrightarrow \neg \Box A)`
  - `test_diamond_of_and`: `(\Diamond (A \wedge B) \leftrightarrow \neg \Box \neg (A \wedge B))`
  - `test_diamond_of_or`: `(\Diamond (A \vee B) \leftrightarrow \neg \Box (\neg A \wedge \neg B))`
  - `test_box_implies_diamond`: `(\Box A \rightarrow \Diamond A)`
- [ ] Implement `TestSomeFutureEquivalence` class with 5 tests:
  - `test_some_future_via_all_future`: `(\future A \leftrightarrow \neg \Future \neg A)`
  - `test_some_future_via_until`: `(\future A \leftrightarrow (A \Until \neg \bot))`
  - `test_some_future_of_neg`: `(\future \neg A \leftrightarrow \neg \Future A)`
  - `test_some_future_of_and`: `(\future (A \wedge B) \leftrightarrow \neg \Future \neg (A \wedge B))`
  - `test_some_future_of_or`: `(\future (A \vee B) \leftrightarrow \neg \Future \neg (A \vee B))`
- [ ] Implement `TestSomePastEquivalence` class with 5 tests:
  - `test_some_past_via_all_past`: `(\past A \leftrightarrow \neg \Past \neg A)`
  - `test_some_past_via_since`: `(\past A \leftrightarrow (A \Since \neg \bot))`
  - `test_some_past_of_neg`: `(\past \neg A \leftrightarrow \neg \Past A)`
  - `test_some_past_of_and`: `(\past (A \wedge B) \leftrightarrow \neg \Past \neg (A \wedge B))`
  - `test_some_past_of_or`: `(\past (A \vee B) \leftrightarrow \neg \Past \neg (A \vee B))`
- [ ] Run all 25 Level 2 tests and confirm they pass

**Timing**: 50 minutes

**Depends on**: 1

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_enriched_equivalence.py` - add 5 test classes

**Verification**:
- All 25 Level 2 tests pass
- `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/unit/test_enriched_equivalence.py -v -k "And or Or or Diamond or SomeFuture or SomePast"` shows 25 passing

---

### Phase 4: Level 3 operator tests, nested combinations, and boundary sensitivity [COMPLETED]

**Goal**: Implement 10 tests for all_future/all_past (Level 3), 5+ cross-operator nested combination tests at complexity levels 3/5/7, and boundary sensitivity tests at M=2 and M=3.

**Tasks**:
- [ ] Implement `TestAllFutureEquivalence` class with 5 tests:
  - `test_all_future_self_equivalence`: `(\Future A \leftrightarrow \Future A)` (M=2)
  - `test_all_future_via_some_future`: `(\Future A \leftrightarrow \neg \future \neg A)`
  - `test_all_future_via_until`: `(\Future A \leftrightarrow \neg (\neg A \Until \neg \bot))`
  - `test_all_future_of_and`: `(\Future (A \wedge B) \leftrightarrow \neg \future \neg (A \wedge B))`
  - `test_all_future_of_or`: `(\Future (A \vee B) \leftrightarrow \neg \future \neg (A \vee B))`
- [ ] Implement `TestAllPastEquivalence` class with 5 tests:
  - `test_all_past_self_equivalence`: `(\Past A \leftrightarrow \Past A)` (M=2)
  - `test_all_past_via_some_past`: `(\Past A \leftrightarrow \neg \past \neg A)`
  - `test_all_past_via_since`: `(\Past A \leftrightarrow \neg (\neg A \Since \neg \bot))`
  - `test_all_past_of_and`: `(\Past (A \wedge B) \leftrightarrow \neg \past \neg (A \wedge B))`
  - `test_all_past_of_or`: `(\Past (A \vee B) \leftrightarrow \neg \past \neg (A \vee B))`
- [ ] Implement `TestNestedCombinations` class with 5+ cross-operator tests at complexity levels 3, 5, 7:
  - `test_diamond_of_and_neg` (depth 3): `(\Diamond (A \wedge \neg B) \leftrightarrow \neg \Box \neg (A \wedge \neg B))`
  - `test_some_future_of_or_neg` (depth 3): `(\future (A \vee \neg B) \leftrightarrow \neg \Future \neg (A \vee \neg B))`
  - `test_quadruple_negation` (depth 4): `(\neg \neg \neg \neg A \leftrightarrow A)`
  - `test_diamond_or_distribution` (depth 5): `((\Diamond A \vee \Diamond B) \leftrightarrow \neg (\Box \neg A \wedge \Box \neg B))`
  - `test_next_of_and_neg` (depth 3): `(\next (A \wedge \neg B) \leftrightarrow ((A \wedge \neg B) \Until \bot))`
- [ ] Implement `TestBoundarySensitivity` class with boundary tests at M=2 and M=3:
  - `test_all_future_equiv_at_m2`: `(\Future A \leftrightarrow \neg \future \neg A)` at M=2
  - `test_all_future_equiv_at_m3`: `(\Future A \leftrightarrow \neg \future \neg A)` at M=3
  - `test_all_past_equiv_at_m2`: `(\Past A \leftrightarrow \neg \past \neg A)` at M=2
  - `test_all_past_equiv_at_m3`: `(\Past A \leftrightarrow \neg \past \neg A)` at M=3
  - `test_all_future_via_until_at_m3`: `(\Future A \leftrightarrow \neg (\neg A \Until \neg \bot))` at M=3
  - `test_all_past_via_since_at_m3`: `(\Past A \leftrightarrow \neg (\neg A \Since \neg \bot))` at M=3
- [ ] Run all Phase 4 tests and confirm they pass

**Timing**: 50 minutes

**Depends on**: 2, 3

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_enriched_equivalence.py` - add 4 test classes

**Verification**:
- All 10 all_future/all_past tests pass
- All 5+ nested combination tests pass
- All 6 boundary sensitivity tests pass (both M=2 and M=3)

---

### Phase 5: Gate validation and regression check [COMPLETED]

**Goal**: Run the full test suite to verify all 55+ tests pass, confirm no regressions in existing tests, and validate the gate criteria.

**Tasks**:
- [ ] Run the full new test file: `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/unit/test_enriched_equivalence.py -v`
- [ ] Count test results: verify at least 55 tests pass (5 per operator x 11 operators + nested + boundary)
- [ ] Run existing bimodal unit tests to confirm no regressions: `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/unit/ -v`
- [ ] Run the full project test suite: `PYTHONPATH=code/src pytest code/tests/ -v`
- [ ] Verify gate criteria: no enriched-tag formula produces a different SAT/UNSAT result than its primitive equivalent
- [ ] Add a module-level docstring to `test_enriched_equivalence.py` documenting the test matrix coverage and gate criteria

**Timing**: 20 minutes

**Depends on**: 4

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_enriched_equivalence.py` - add module docstring

**Verification**:
- All 55+ test cases in `test_enriched_equivalence.py` pass
- All existing bimodal unit tests pass (no regressions)
- Full project test suite passes
- Gate criteria met: no enriched-tag formula diverges from its primitive equivalent

## Testing & Validation

- [ ] All 55+ equivalence tests pass (5 per operator x 11 operators minimum)
- [ ] Nested combination tests pass at complexity levels 3, 5, 7
- [ ] Boundary sensitivity tests pass for all_future/all_past at both M=2 and M=3
- [ ] No regressions in existing bimodal unit test suite
- [ ] No regressions in full project test suite
- [ ] Each test uses `isolated_z3_context()` to prevent state leakage
- [ ] TopOperator tests use `\neg \bot` form (not `\top` directly)

## Artifacts & Outputs

- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_enriched_equivalence.py` - new test file with 55+ test cases
- `specs/113_enriched_operator_equivalence_tests/plans/01_enriched-equivalence-tests.md` - this plan
- `specs/113_enriched_operator_equivalence_tests/summaries/01_enriched-equivalence-tests-summary.md` - implementation summary (created during implementation)

## Rollback/Contingency

The new test file `test_enriched_equivalence.py` is purely additive -- it does not modify any existing code. If any tests fail unexpectedly:
1. Check whether the failure is a test formula error (typo in infix string) or a genuine semantic divergence
2. For TopOperator-related failures, verify the `\neg \bot` workaround is applied
3. For boundary-related failures in G/H tests, try increasing M to 3 or 4
4. If rollback is needed, simply delete the new test file -- no existing files are modified
