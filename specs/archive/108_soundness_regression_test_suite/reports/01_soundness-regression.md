# Research Report: Soundness Regression Test Suite for Boundary and Shift-Closure Edge Cases

**Task**: 108 - Soundness regression test suite for boundary and shift-closure edge cases
**Date**: 2026-06-01
**Mode**: Single-agent research
**Session**: sess_1780354243_1181c9

## Summary

This report provides a comprehensive analysis of the existing test coverage for the bimodal oracle, identifies specific coverage gaps for the five test categories in the task description, and provides concrete guidance for implementing `test_soundness_regression.py`.

**Key findings**:

1. **Coverage gaps are real but targeted**: The existing `test_boundary_regression.py` and `test_oracle_provider.py` cover much of categories 3 (forward_comp/converse — `test_frame_class_mapping.py`) and 5 (M=max(depth,2) deviation — partially). Categories 1, 2, and 4 have significant uncovered ground.

2. **Boundary vacuity semantics are confirmed**: The ForAllTime guard at domain edge `t=M-1` creates genuine vacuity — `G(phi)` at `t=M-1` is vacuously true regardless of phi. With `M=max(depth,2)` (current oracle), depth-2+ formulas face boundary artifacts at M=2.

3. **Shift closure is `capped_skolem_abundance_constraint`**: There is no explicit "shift closure" check in extracted countermodels. The existing tests only test frame axioms (nullity/converse/forward_comp) post-hoc. Shift closure of extracted world histories is untested.

4. **State isolation is covered for the provider**: `test_oracle_provider.py::TestStateIsolation` has 100-call tests, but they use only 2 fixed formulas repeatedly. The task requires a broader mix of 5+ formulas including SAT, UNSAT, and temporal formulas.

5. **M deviation is documented but not regression-tested with crafted counterexamples**: The oracle uses `M=max(depth,2)`. For depth≥2, this means M=depth not M=depth+2. Concrete formulas that expose boundary gaps at M=depth but not at M=depth+2 are not currently tested.

---

## 1. Current Test Coverage Inventory

### test_boundary_regression.py (task 107, 63 tests)

| Class | Coverage | Gaps |
|-------|----------|------|
| TestBoundaryAnalysis | Pure Python: M_safe formula, domain size, reachable depth | No Z3 solver calls — verifies math only |
| TestBoundaryDocumentation | Z3 behavioral: 8 tests, primarily M=2 vs M=3 for TN_CM_1 | No tests for temporal_depth >= 2 boundary artifacts |
| TestExampleRegression | 43-example parametric suite, all pass | Tests examples at their native M values, not at dynamic M |
| TestTemporalDepthAllTags | All 17 JSON tags, nested formulas, M_safe computation | Complete |

**Gap**: No test directly verifies that `F(G(p))` with M=2 produces a wrong result and M=4 produces a correct result. The "spurious SAT" scenario described in the task is not tested as a boundary-unsafe formula.

### test_oracle_provider.py (task 103, ~40 tests)

| Class | Coverage | Gaps |
|-------|----------|------|
| TestProviderProperties | Static contract: provider_id, version, frame_classes | Complete |
| TestFindCountermodelContract | Output keys, types, boundary_safe flag, temporal_depth | No temporal_depth >= 2 formulas tested |
| TestValidateSelf | Basic SAT/UNSAT validation | Complete |
| TestStateIsolation | 100 sequential SAT, 100 sequential UNSAT, 100 mixed | Only uses 4 fixed formulas (2 SAT, 2 UNSAT); no temporal depth-2+ formulas |
| TestFormulaFoldedJson | formula_folded_json output | Complete |
| TestOracleExampleRegression | 42 active examples via standard pipeline | Uses standard pipeline, not oracle's JSON API |
| TestOracleOutputCompleteness | boundary_safe consistency | Tests formula_json without temporal depth >= 2 |

**Gap**: State isolation is only tested with propositional formulas. No temporal depth-2+ formulas in the isolation suite.

### test_frame_class_mapping.py (post-hoc frame axiom tests)

| Class | Coverage | Gaps |
|-------|----------|------|
| TestFixtureSmoke | Fixture validity | Complete |
| TestNullityIdentityPostHoc | task_rel(s, 0, u) ↔ s=u | Complete |
| TestConversePostHoc | task_rel(s,d,u) ↔ task_rel(u,-d,s) | Complete for duration range (-M+1, M-1) |
| TestForwardCompPostHoc | Compositionality for composable pairs | Complete for valid duration range |
| TestLawfulHistoryPostHoc | Consecutive states have unit task_rel | Complete |

**Gap**: These tests use a fixed fixture (N=2, M=2, `task_rel(0,1,1)` forced). They do not test against actual oracle output (the serialized `task_relation` from `extract_task_triples`). The task requires testing shift closure of extracted countermodels (not just the solver's internal Z3 model).

---

## 2. Boundary Vacuity: How ForAllTime Guards Work at Domain Edge

The domain D = (-M, M) gives integer points {-(M-1), ..., M-1}. Evaluation is always at t=0.

### ForAllTime guard at t=M-1:

```python
# ForAllTime(world, time_var, body):
z3.ForAll(
    time_var,
    z3.Implies(
        self.is_valid_time(time_var),  # time_var > -M AND time_var < M
        body
    )
)
```

`G(phi)` at t=M-1 with body `Implies(time_var > M-1, phi_at(time_var))`:
- Universe of time_var: all integers (Z3 quantifies over all integers)
- Guard `is_valid_time(time_var)` restricts to `(-M, M)`, i.e., time_var ∈ {-(M-1), ..., M-1}
- Inner guard `time_var > M-1` requires time_var ≥ M, but the outer guard requires time_var ≤ M-1
- Both guards together: **no valid time_var satisfies both** → ForAll is vacuously true

**Concrete case for boundary_safe=False test**: `F(G(p))` with M=2 (depth=2, M_safe=4):
- `F(G(p))` at t=0: ExistsTime t' > 0 such that G(p) at t' is true
- Only t'=1 exists (M=2, domain {-1,0,1})
- G(p) at t'=1: ForAllTime t'' > 1 in D → p at t''
  - No t'' satisfies both t'' > 1 AND t'' ∈ {-1,0,1}
  - ForAll is vacuously true regardless of p
- Therefore F(G(p)) at t=0 is SAT vacuously even if p is false everywhere

With M=4 (depth=2, M_safe=4):
- F(G(p)) at t=0: ExistsTime t' ∈ {1,2,3} such that G(p) at t'
- G(p) at t'=1: ForAllTime t'' > 1 in {-3,-2,-1,0,1,2,3} → requires p at t''=2 and t''=3
- G(p) at t'=2: requires p at t''=3 only
- G(p) at t'=3: vacuously true (no t'' > 3 in domain)
- F(G(p)) at t=0 is SAT iff there exists t' ∈ {1,2,3} where G(p) holds non-vacuously
- p must hold at t=2 (for G(p) at t=1) or p must hold at t=3 (for G(p) at t=2)
- This is a genuine (non-vacuous) constraint

**For the test**: `F(G(p))` should be:
- SAT at M=2 even if p is forced to be false (spurious — shows boundary artifact)
- UNSAT at M=4 when p is forced false (correct)
- SAT at M=4 when p can be free (correct — p can be true at t=2 or t=3)

### Formulas with boundary_safe=False that produce correct results anyway

The M=max(depth,2) deviation means:
- depth=0: M=2, M_safe=3 → boundary_safe=False (M≤depth+1). But depth=0 has no temporal ops → no boundary effect.
- depth=1: M=2, M_safe=3 → boundary_safe=False. But M=2 still gives one future time point.
- depth=2: M=2, M_safe=4 → boundary_safe=False. This is where artifacts can arise.
- depth=3: M=3, M_safe=5 → boundary_safe=False. M=3 gives only 1 future point past t=1.

So the test suite should focus on depth=2 and depth=3 formulas to expose the gap.

---

## 3. Shift Closure: What It Means and Where to Test It

### Definition (from semantic.py comments)

"Shift closure" means that for every world w with interval [s, e], for every shift delta where [s+delta, e+delta] stays within the global domain (-M, M), there exists a world w' with:
1. interval [s+delta, e+delta]
2. w'(t+delta) = w(t) for all t in [s, e]

This is the `capped_skolem_abundance_constraint` in BimodalSemantics.

### What the extracted task_relation does NOT capture

The extracted `task_relation` from `extract_task_triples` in `serialization.py` iterates over:
- All state pairs (s, u) in 0..2^N-1
- All durations d in -(M-1)..M-1

It returns `{"source": s, "duration": d, "target": u}` for all triples where `task_rel(s, d, u)` evaluates to True.

**Shift closure in the task_relation**: If the world histories satisfy shift closure, then for every world w with `w(t)=s` and `w(t+d)=u`, there must exist a world w' with `w'(t'+delta)=s` and `w'(t'+delta+d)=u` for any valid shift delta. This means `task_rel(s, d, u)` should hold regardless of the shift — which means shift closure implies the task_relation is "invariant" under shifts (it doesn't change based on which shift offset we use).

**The actual test target**: Since shift closure is a property of world histories (not of task_rel directly), the test should:
1. Extract the world_histories from the oracle output
2. For each world history w with interval [s, e] and some shift delta where [s+delta, e+delta] ⊆ (-M, M):
   - Verify there exists a world w' with interval [s+delta, e+delta]
   - Verify w'(t+delta) = w(t) for all t in [s, e]

The `world_histories` field in the oracle output is a list of `{"world_id": int, "times": {str: str}}` dicts where times maps time strings to state strings.

### Shift closure edge cases from duration range (-M+1, M-1)

The task says "shifts within (-M+1, M-1)". For M=2, this is just {-1, 0, 1}. For M=3, it's {-2,-1,0,1,2}.

For a shift closure test, a useful oracle call returns SAT (has a countermodel), and then we verify:
- For world_id=0 with times {-1: "a", 0: "b", 1: "c"} and shift delta=1:
  - We need world with times {0: "a", 1: "b", 2: "c"} to exist in world_histories
  - BUT: M=2 gives domain {-1,0,1}, so shift by +1 would require time=2 which is outside the domain
  - So for M=2, the ONLY valid shift for a world spanning {-1,0,1} is delta=0 (no shift)

This means shift closure tests require M≥3 to have non-trivial shifts.

### Useful test formula for shift closure

Use `MD_CM_1`: Box(A∨B) → Box(A), Box(B) with N=2, M=3. This produces a countermodel and the world_histories should have shift-closed worlds.

Or better: use a SAT formula via the oracle (Z3OracleProvider.find_countermodel) and check the returned world_histories for shift closure.

---

## 4. forward_comp and converse: Coverage and Gaps

### What test_frame_class_mapping.py tests

- Converse: checks `(s, d, u) ∈ pairs → (u, -d, s) ∈ pairs` for all d in valid_dur range
- Forward_comp: checks `(s,d1,v) ∈ pairs ∧ (v,d2,u) ∈ pairs ∧ d1+d2 ∈ valid_dur → (s,d1+d2,u) ∈ pairs`

These are tested against the solver's raw Z3 model via `extract_task_rel_pairs`.

### What is NOT tested

The oracle's `extract_task_triples` serializes the task_relation as a list in the output dict. The `test_soundness_regression.py` should test this **serialized** output (the list of `{source, duration, target}` dicts), not the raw Z3 model. This is the post-hoc validation on the oracle's public output, not on the internal Z3 representation.

**Gap**: No test verifies that the `task_relation` field in `Z3OracleProvider.find_countermodel()` output satisfies converse and forward_comp across all durations in the extracted triple set, using the public API output.

### Duration range in extracted triples

`extract_task_triples` iterates durations in `range(-(M-1), M)`, which is {-(M-1), ..., M-1}. This is the same range as `extract_task_rel_pairs` in the frame mapping tests.

**Important**: The converse check must use the same range. If `(s, d, u)` is in the output but `(u, -d, s)` requires d to be at the range boundary (d = ±(M-1)), then -d = ∓(M-1) which is still in range. However, if d=0, then -d=0, and nullity applies.

---

## 5. State Isolation: Current Coverage and Gaps

### Existing coverage

`TestStateIsolation` in `test_oracle_provider.py`:
- `test_100_sequential_sat_calls`: 100 calls with `SIMPLE_SAT_JSON = {"tag": "atom", "name": "A"}` (depth=0)
- `test_100_sequential_unsat_calls`: 100 calls with `SIMPLE_UNSAT_JSON = {"tag": "imp", ...}` (depth=0)  
- `test_100_mixed_calls`: 25 rounds × 4 formulas = 100 calls; all are propositional (depth=0)
- `test_no_semantics_reference_leak`: Single call check for `provider._semantics is None`

### Gap: No temporal depth in isolation tests

All 4 formulas used in isolation tests are depth=0. The task requires "a mix of SAT and UNSAT formulas" including temporal depth-1 and depth-2 formulas.

### Additional gap: No cross-call contamination check

The existing tests only check that SAT formulas return non-None and UNSAT formulas return None. They do not check for subtle state leakage like:
- A SAT result from formula A changing what the oracle returns for formula B
- A temporal formula causing Z3 context contamination (if `isolated_z3_context` has any gap)

The `isolated_z3_context` in `context.py` should prevent this, but the test should verify it explicitly.

---

## 6. Known-Boundary-Unsafe Formulas: Design for 5 Test Cases

These are formulas where M=depth produces boundary artifacts but M=max(depth+2,3) produces correct results.

### Formula 1: F(G(p)) — depth=2

- `{"tag": "some_future", "arg": {"tag": "all_future", "arg": {"tag": "atom", "name": "p"}}}`
- With M=2 (current oracle for depth=2): vacuously SAT (G(p) at t=1 is vacuously true)
- With M=4 (M_safe): SAT only if there exists t' where G(p) is genuinely satisfied
- Oracle test: `find_countermodel(FG_p_json)` returns non-None with M=2 (due to boundary artifact)
  - But since the oracle uses M=max(depth,2)=2, this is boundary-unsafe (boundary_safe=False)
  - Result's `boundary_safe` should be `False`

### Formula 2: G(F(p)) — depth=2

- `{"tag": "all_future", "arg": {"tag": "some_future", "arg": {"tag": "atom", "name": "p"}}}`
- G(F(p)) at t=0 with M=2: ForAll t'>0: ExistTime t''>t' with p at t''
  - t'=1: ExistsTime t''>1 in {-1,0,1} — no such t'' — G(F(p)) at t'=1 is FALSE
  - Wait: G(F(p)) is universal — for ALL t'>0, F(p) must hold. At t'=1, F(p) is false (no t''>1).
  - So G(F(p)) is UNSAT at M=2? No, G(F(p)) is tested as invalidity of ~G(F(p)), i.e., SAT for ~G(F(p))...
  - Actually the oracle checks invalidity of G(F(p)) directly — finds a model where G(F(p)) is false
  - A model where G(F(p)) is false: ∃t'>0 where F(p) is false at t' — this is easy with p false everywhere
  - So G(F(p)) is invalid (SAT for countermodel), regardless of M
  - This is not a useful boundary test

### Formula 3: G(p) → F(G(p)) — depth=2

- `{"tag": "imp", "left": {"tag": "all_future", "arg": p}, "right": {"tag": "some_future", "arg": {"tag": "all_future", "arg": p}}}`
- This formula says: "if p holds in all future times, then there is a future time where p holds in all further future times"
- With M=2 (domain {-1,0,1}): G(p) requires p at t=1. F(G(p)) requires exists t'>0 where G(p) holds. At t'=1, G(p) is vacuously true (no t''>1). So F(G(p)) is satisfied trivially. The implication G(p)→F(G(p)) has no countermodel (formula is "valid" via boundary artifact). oracle returns None.
- With M=4: G(p) requires p at t=1,2,3. F(G(p)) requires exists t' ∈ {1,2,3} where G(p) holds genuinely. At t'=1: G(p) requires p at 2,3 — genuine. So the implication's conclusion requires more than just vacuous G. Now: if G(p) holds at t=0 → p at 1,2,3 → F(G(p)): at t'=1, G(p) requires p at 2,3 (both satisfied by G(p)), so F(G(p)) holds. The formula is still valid (no countermodel). oracle returns None.
- **Not distinguishable — not a useful test case.**

### Formula 4: H(P(p)) → G(F(p)) — temporal depth=2, mixing past and future

The key insight for a useful boundary-unsafe formula: we need a formula that is **valid** in the infinite-time semantics but appears **invalid** (has a spurious countermodel) when M=depth due to boundary vacuity.

Or: a formula that is **invalid** in the infinite-time semantics but appears **valid** (oracle returns None spuriously) when M=depth due to boundary making an UNSAT that should be SAT.

**The most reliable approach**: Test formulas where the oracle with M=2 returns boundary_safe=False, verify the result is consistent with the correct semantics, and verify that with M=max(depth+2,3) the oracle returns the same or a non-spurious result.

### Revised 5 test formulas focusing on oracle output with boundary_safe=False

**Formula 1**: `some_future(atom("p"))` — F(p), depth=1, M=2
- boundary_safe: False (M=2, depth+1=2, so M=2 = depth+1, NOT M > depth+1)
- Result: oracle should find countermodel (p always false)
- Verify: boundary_safe=False, temporal_depth=1, time_bound=2
- Expected: non-None (SAT: countermodel exists — p is false at all times)

**Formula 2**: `all_future(atom("p"))` — G(p), depth=1, M=2
- Similar to F(p) for countermodel: G(p) has countermodel (p false at t=1)
- Expected: non-None, boundary_safe=False

**Formula 3**: `some_future(all_future(atom("p")))` — F(G(p)), depth=2, M=2 (current oracle M=max(2,2)=2)
- Boundary artifact: G(p) at t=1 is vacuously true → F(G(p)) is SAT trivially
- Result: non-None returned by oracle
- boundary_safe: False (M=2, depth=2, so 2 > 3 is False)
- Verify boundary_safe=False in result

**Formula 4**: `all_future(some_future(atom("p")))` — G(F(p)), depth=2, M=2
- G(F(p)) at t=0: ForAll t'>0 in {-1,0,1}: ExistsTime t''>t' with p
  - t'=1: need t''>1 in {-1,0,1} — none → F(p) at t'=1 is FALSE
  - So G(F(p)) is FALSE at t=0 → countermodel (any model) works
- Expected: non-None (genuine countermodel, not spurious)
- Verify boundary_safe=False

**Formula 5**: `all_future(all_future(atom("p")))` — G(G(p)), depth=2, M=2
- G(G(p)) at t=0 with M=2:
  - Outer G at t=0: ForAll t'>0 in {-1,0,1} → t'=1
  - G(p) at t'=1: ForAll t''>1 in {-1,0,1} → none → vacuously TRUE
  - So outer G at t=0 only needs G(p) at t'=1, which is vacuously true
  - G(G(p)) is therefore vacuously SAT (countermodel trivially requires p false — but G(G(p)) at t=0 is TRUE regardless of p!)
  - Wait: the ORACLE checks invalidity of G(G(p)), i.e., SAT for ~G(G(p))
  - ~G(G(p)) at t=0: ExistsTime t'>0 where ~G(p) at t'
  - At t'=1: ~G(p) at t'=1 requires ExistsTime t''>1 where ~p — but no t''>1 in domain
  - So ~G(p) at t'=1 is FALSE → ~G(G(p)) at t=0 is FALSE → oracle returns None (UNSAT spuriously!)
  - With M=4: ~G(G(p)) can be SAT (p false at t=3 makes G(p) at t=2 false, making G(G(p)) at t=0 false)
  - **This is the key boundary-unsafe formula**: oracle returns None with M=2 but non-None with M=4

**Conclusion**: G(G(p)) (depth=2) is the prime test case:
- With M=max(depth,2)=2: oracle returns None (spuriously valid — UNSOUND for theorem validation)
- With M=max(depth+2,3)=4: oracle returns non-None (correct countermodel found)
- Expected oracle output fields: boundary_safe=False (M=2, depth=2: 2 > 3 is False)

---

## 7. M Deviation Analysis: max(depth,2) vs max(depth+2,3)

### Current oracle implementation

In `provider.py` (line 215):
```python
depth = temporal_depth(formula_json)
M = max(depth, 2)
```

### Implications by depth

| depth | M (current) | M_safe | boundary_safe | Risk |
|-------|------------|--------|---------------|------|
| 0 | 2 | 3 | False (M=depth+1, not >depth+1 for depth=1 case: 2>1 is True!) | Actually True: M=2, depth=0, 2>0+1=True |
| 1 | 2 | 3 | False (M=2, depth=1: 2>2 is False) | Depth=1 temporal ops: G at t=1 has vacuous future |
| 2 | 2 | 4 | False | **HIGH RISK**: G(G(p)) spuriously UNSAT |
| 3 | 3 | 5 | False (M=3, depth=3: 3>4 is False) | G(G(G(p))) with M=3 |
| 4 | 4 | 6 | False (M=4, depth=4: 4>5 is False) | Deep nesting |

Wait — recalculating `boundary_safe` from `serialization.py`:
```python
boundary_safe = M > depth + 1
```

For depth=0, M=2: `2 > 0+1 = 2 > 1 = True`. So depth=0 is boundary_safe=True. Good.
For depth=1, M=2: `2 > 1+1 = 2 > 2 = False`. depth=1 is boundary_safe=False.
For depth=2, M=2: `2 > 2+1 = 2 > 3 = False`. depth=2 is boundary_safe=False.
For depth=3, M=3: `3 > 3+1 = 3 > 4 = False`. depth=3 is boundary_safe=False.

### The Skolem abundance over-constraint issue at M=3

The provider comment (lines 208-213) explains:
> M=2 is the practical safe maximum: it allows countermodel search for depth-0 and depth-1 formulas without the M=3 over-constraint issue. For depth>=2 formulas, M=max(depth, 2) extends the time domain.

The "over-constraint" refers to `skolem_abundance` (the `capped_skolem_abundance_constraint`) at M≥3 causing solver timeouts for no-premise queries. This is a known performance regression, not a soundness issue per se.

### Risk for test_soundness_regression.py

Tests should NOT try to fix the M deviation — they should **document** it by:
1. Testing that `boundary_safe=False` for depth≥1 formulas (expected given M=max(depth,2))
2. Testing that for the specific formula G(G(p)) with M=2, the oracle returns None
3. Documenting this as a known limitation via comments, not a bug to fix

The gate says "no boundary-unsafe formulas produce incorrect results" — but the G(G(p)) case with M=2 IS incorrect (oracle says valid when it is not). The test should document this known-incorrect behavior and assert the boundary_safe=False flag, not try to fix M.

**Alternative interpretation**: The gate tests should use a harness that applies the correct M and verifies the oracle produces the right result. The `test_soundness_regression.py` should test oracle correctness AT the oracle's native M, with `boundary_safe` as the flag.

---

## 8. Formula Construction Approach

### JSON formulas used in the oracle

The oracle accepts JSON formula dicts directly. No need for json_to_prefix/prefix_to_infix in test code — the oracle handles the conversion internally.

```python
# Depth-2 formulas (temporal)
FG_p = {"tag": "some_future", "arg": {"tag": "all_future", "arg": {"tag": "atom", "name": "p"}}}
GG_p = {"tag": "all_future", "arg": {"tag": "all_future", "arg": {"tag": "atom", "name": "p"}}}
GF_p = {"tag": "all_future", "arg": {"tag": "some_future", "arg": {"tag": "atom", "name": "p"}}}
FG_p_implication = {
    "tag": "imp",
    "left": {"tag": "all_future", "arg": {"tag": "atom", "name": "p"}},
    "right": {"tag": "some_future", "arg": {"tag": "all_future", "arg": {"tag": "atom", "name": "p"}}},
}
```

### Standard pipeline formulas (for state isolation test)

For broader state isolation testing, use formulas of varying depth and expected outcomes:
- Depth-0 SAT: `{"tag": "atom", "name": "A"}` (existing)
- Depth-0 UNSAT: `{"tag": "imp", "left": A, "right": A}` (existing)
- Depth-1 SAT: `{"tag": "some_future", "arg": A}` (FUTURE_SAT_JSON, existing)
- Depth-1 UNSAT: `{"tag": "all_future", "arg": {"tag": "imp", "left": A, "right": A}}` (G(A→A) is valid)
- Depth-2 SAT: `{"tag": "imp", "left": GG_p, "right": GF_p}` — or simpler depth-2 invalid formula
- Depth-2: G(F(p)) is invalid (countermodel: p false everywhere)

---

## 9. Test Category Mapping to Test Classes

### Category 1: Boundary Vacuity Tests

**Class**: `TestBoundaryVacuity`

Tests:
1. `test_depth2_formula_boundary_safe_is_false`: Call oracle with GG_p (depth=2), verify `result["boundary_safe"] is False` and `result["time_bound"] == 2`
2. `test_depth1_formula_boundary_safe_is_false`: F(p) depth=1, verify boundary_safe=False
3. `test_depth0_formula_boundary_safe_is_true`: atom(A) depth=0, verify boundary_safe=True
4. `test_gg_p_returns_none_with_m2`: G(G(p)) returns None from oracle (known boundary-unsafe UNSAT spurious)
5. `test_boundary_safe_false_depth1_still_correct`: F(p) has correct countermodel (p false) even with boundary_safe=False

### Category 2: Shift Closure Tests

**Class**: `TestShiftClosure`

Tests:
1. `test_extracted_worlds_satisfy_shift_closure`: For a SAT oracle result with M≥3, verify world_histories are shift-closed
2. `test_shift_closure_within_valid_shifts_range`: Verify shifts in (-M+1, M-1) are accounted for

Note: With M=2 (current oracle default for most formulas), the only valid non-zero shift for world interval [-1,1] would be +1 (to [0,2]) but 2 is outside domain — so for M=2, shift closure is vacuously satisfied (no non-zero valid shifts). Tests should use formulas with M≥3.

**Special case**: Use `all_future(all_past({"tag": "atom", "name": "p"}))` (depth=2) with M=3 (max(2,2)=2 currently, but we can construct a formula with depth=1 but that forces M≥3 through the oracle... Actually, the oracle uses M=max(depth,2) so depth=1 gives M=2). For shift closure testing, we may need to use `BimodalSemantics` directly with M=3, not the oracle's M.

**Revised approach**: Create a `BimodalSemantics` instance with M=3 directly (bypassing the oracle), extract a Z3 model, then run shift closure checks on the extracted world histories.

### Category 3: Guarded Compositionality Tests

**Class**: `TestGuardedCompositionality`

Tests validate the `task_relation` field in oracle output (not raw Z3 model):
1. `test_forward_comp_in_oracle_output`: For SAT oracle result, extract task_relation list, verify compositionality
2. `test_converse_in_oracle_output`: For SAT oracle result, verify converse axiom on task_relation list
3. `test_nullity_in_oracle_output`: For SAT oracle result, verify nullity axiom on task_relation list
4. `test_all_durations_in_range`: All durations in task_relation are within [-(M-1), M-1]

The key difference from `test_frame_class_mapping.py`: these tests work on the serialized oracle output dict, not on the internal Z3 model.

### Category 4: State Isolation Regression

**Class**: `TestStateIsolationRegression`

Tests:
1. `test_100_calls_mixed_temporal_depths`: Run 100 sequential calls with rotating set of 5 formulas (depth 0-2, SAT and UNSAT)
2. `test_sat_unsat_interleaving_stability`: Interleave SAT depth-2 and UNSAT depth-2 formulas; verify no cross-contamination
3. `test_temporal_atom_interleaving`: Mix temporal (depth-1) and propositional formulas; verify consistent results
4. `test_isolated_context_confirmed`: Verify provider._semantics is None after each call in a 10-call sequence

### Category 5: Known-Boundary-Unsafe Formulas

**Class**: `TestKnownBoundaryUnsafe`

Tests:
1. `test_fg_p_boundary_safe_false_returns_result`: F(G(p)) with M=2 (depth=2), verify boundary_safe=False and result is non-None (spurious SAT documented)
2. `test_gg_p_boundary_safe_false_returns_none`: G(G(p)) with M=2 (depth=2), verify boundary_safe=False and result is None (spurious UNSAT documented)
3. `test_gf_p_boundary_unsafe_but_correct`: G(F(p)) with M=2, verify boundary_safe=False, result non-None (correct — genuine countermodel)
4. `test_depth1_all_future_correct_with_m2`: G(p) with M=2, boundary_safe=False, but result non-None (correct countermodel — p false at t=1)
5. `test_depth0_always_boundary_safe`: atom(p) with M=2, boundary_safe=True, correct SAT

---

## 10. Key File Locations

| File | Purpose | Notes |
|------|---------|-------|
| `/code/src/bimodal_logic/provider.py` | Z3OracleProvider | `find_countermodel()`, M=max(depth,2) logic |
| `/code/src/bimodal_logic/serialization.py` | `extract_task_triples`, `serialize_countermodel` | boundary_safe computation |
| `/code/src/bimodal_logic/translation.py` | `temporal_depth()`, `json_to_prefix()` | formula construction |
| `/code/src/model_checker/theory_lib/bimodal/semantic.py` | `BimodalSemantics` | `build_converse_constraint`, `build_forward_comp_constraint`, `capped_skolem_abundance_constraint` |
| `/code/src/model_checker/theory_lib/bimodal/tests/unit/test_boundary_regression.py` | Task 107 boundary tests | Do NOT duplicate |
| `/code/src/model_checker/theory_lib/bimodal/tests/unit/test_oracle_provider.py` | Task 103 oracle tests | Do NOT duplicate |
| `/code/src/model_checker/theory_lib/bimodal/tests/unit/test_frame_class_mapping.py` | Frame axiom post-hoc | Tests raw Z3 model, NOT oracle output |
| `/code/src/model_checker/utils/context.py` | `isolated_z3_context` | Required for state isolation |

### Target file location for new tests

`/code/src/model_checker/theory_lib/bimodal/tests/unit/test_soundness_regression.py`

---

## 11. Risk Analysis Summary

| Risk | Severity | Mitigation |
|------|---------|------------|
| G(G(p)) with M=2 returns None (spurious theorem) | HIGH — oracle reports valid formula as theorem | Document in test with explicit comment; assert boundary_safe=False |
| G(G(p)) with M=2 used to prove a soundness-critical theorem | MEDIUM | Oracle results with boundary_safe=False should be treated as provisional |
| Shift closure is hard to test with M=2 (vacuous) | LOW — shift closure tests degenerate | Use BimodalSemantics directly with M=3 for shift closure tests |
| State isolation tests only cover propositional formulas | LOW — isolated_z3_context is trusted | Add depth-1/2 formulas to the isolation mix |
| M=max(depth+2,3) not yet implemented due to skolem_abundance | HIGH if enabled — would break examples | Do NOT change M in provider.py as part of this task |
| forward_comp/converse tests duplicate test_frame_class_mapping.py | MEDIUM duplication | Focus on oracle OUTPUT (task_relation list), not raw Z3 model |

---

## 12. Implementation Notes

### Imports required for test_soundness_regression.py

```python
from bimodal_logic import Z3OracleProvider
from bimodal_logic.translation import temporal_depth
from model_checker.theory_lib.bimodal.semantic import BimodalSemantics
from model_checker.utils.context import isolated_z3_context
import z3
```

### Helper for extracting task_relation as a set

```python
def _task_rel_as_set(task_relation):
    return {(t["source"], t["duration"], t["target"]) for t in task_relation}
```

### Helper for verifying forward_comp on oracle output

```python
def _check_forward_comp(task_relation, M):
    pairs = _task_rel_as_set(task_relation)
    valid_dur = range(-M + 1, M)
    violations = []
    for (s, d1, v) in pairs:
        for (v2, d2, u) in pairs:
            if v != v2:
                continue
            d_sum = d1 + d2
            if d_sum not in valid_dur:
                continue
            if (s, d_sum, u) not in pairs:
                violations.append((s, d1, v, d2, u, d_sum))
    return violations
```
