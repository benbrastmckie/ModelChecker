# Teammate C Findings: Critic Analysis

**Task 97**: Optimize build_frame_constraints for Z3 solver performance
**Role**: Critic -- Gaps, Risks, and Blind Spots
**Date**: 2026-05-29

---

## Key Findings (Gaps and Risks)

### Finding 1: classical_truth Removal Has a Hidden Timing Risk

**Confidence: Medium**

The `classical_truth` constraint `ForAll([ws, sl], Or(truth_condition(ws,sl), Not(truth_condition(ws,sl))))` is logically tautological -- `z3.simplify()` confirms it reduces to `True`. Removing it appears safe, but there is a subtle timing effect.

`truth_condition(ws, sl)` appears in `classical_truth` and **nowhere else in frame_constraints**. When this constraint is present, `truth_condition` enters Z3's E-matching ground term index early (as the first quantifier in the list). When removed, `truth_condition` only appears later, via `premise_constraints` and `conclusion_constraints` generated when formulas are evaluated via `true_at()`.

For most examples this timing shift is harmless because premises/conclusions always introduce `truth_condition` terms. However, for pathological cases where:
- The formula has no sentence letters (e.g., bot -> A via `EX_FALSO_TH`), or
- Z3's MBQI relies on `truth_condition` being grounded before processing some quantifier interaction,

the removal could cause different solver behavior. The `# NOTE: order matters!` comment at line 668 exists without explanation -- it may document empirical sensitivity to exactly this kind of ground-term timing.

**Validation needed**: Run the full test suite with `classical_truth` removed and confirm identical results. Focus especially on `EX_FALSO_TH` (no premises, only `\bot -> A`) and examples where `contingent=False, disjoint=False` (so no proposition_constraints introduce ground terms independently).

---

### Finding 2: "Order Matters" Comment Has No Explanation

**Confidence: High**

Line 668 says `# NOTE: order matters!` but there is no comment explaining what it means or what the consequence of reordering is. This is a significant documentation gap for any optimization that reorders constraints.

Z3's behavior with quantifiers is sensitive to the order constraints are added because:
1. The E-matching ground term index is built incrementally as constraints are added.
2. MBQI candidate generation can be influenced by which ground terms exist when a quantifier is first processed.
3. Unsat core extraction depends on constraint labeling which reflects addition order.

**Validation needed**: Before any reordering, run all 60+ examples with the original order and record which pass, then repeat with the proposed new order and diff the results. The absence of any comment explaining the ordering makes it impossible to reason about safety without empirical testing.

---

### Finding 3: task_minimization Is Mislabeled -- Uncommenting Would Break Semantics

**Confidence: High**

The `task_minimization` constraint is commented out with `# MAYBE`, and the docstring says "encourages minimal changes" (implying a soft hint). But it is actually a **hard ForAll constraint**:

```python
ForAll([world_id, time_point],
    Implies(
        And(is_world(world_id), valid_time_for_world(world_id, time_point),
            valid_time_for_world(world_id, time_point + 1)),
        Select(world_function(world_id), time_point) ==
        Select(world_function(world_id), time_point + 1)
    )
)
```

This forces **all consecutive states in all worlds to be identical**. Enabling this would make temporal variation impossible -- every world history would be constant. All temporal examples (`TN_CM_1`, `TN_TH_2`, `BX_*` axioms) would fail. The comment "Encourages minimal state changes" is misleading and the constraint is correctly left commented out. Any optimizer who encounters this should treat it as permanently disabled.

---

### Finding 4: max_world_id Grows Exponentially -- Optimizations Help Only at Small Scale

**Confidence: High**

The formula `max_world_id = M * 2^(M*N)` creates extremely large domains for the BX axiom examples:

| N | M | max_world_id | Example |
|---|---|-------------|---------|
| 2 | 2 | 32 | most basic examples |
| 2 | 3 | 192 | BM_TH_1, BM_TH_2 |
| 2 | 4 | 1024 | BX5, BX6, BX11 |
| 3 | 4 | 16,384 | BX2G, BX2H, BX3, BX13 |
| 4 | 5 | 5,242,880 | BX7 (excluded from CI) |

**No frame constraint caps the `is_world` domain**. The `is_world` function is a Z3 UF with domain `IntSort`. With MBQI enabled, Z3 can consider `is_world(n) = True` for arbitrarily large `n`, not just `n < max_world_id`. The `enumeration_constraint` and `convex_world_ordering` push worlds to be non-negative and contiguous, but they do not cap the domain at `max_world_id`.

This means: for `N=3, M=4`, the quantified constraints `lawful`, `world_uniqueness`, and `skolem_abundance` reason over a potentially unbounded integer domain with only convexity as a bound. Frame-level optimizations (patterns, tautology removal) provide only polynomial improvement at best -- the fundamental problem is exponential domain size.

**Proposed optimizations do NOT address this root cause.** Adding patterns to existing constraints or removing `classical_truth` will not reduce the domain size that MBQI must explore.

---

### Finding 5: world_uniqueness Is a Nested ForAll/Exists Without Any Pattern

**Confidence: High**

```python
world_uniqueness = ForAll([world_one, world_two],
    Implies(And(is_world(w1), is_world(w2), w1 != w2),
        Exists([some_time],
            And(valid_time(t), valid_time_for_world(w1, t), valid_time_for_world(w2, t),
                Select(wf(w1), t) != Select(wf(w2), t)))))
```

This is `ForAll/Exists` with **0 patterns** (confirmed by `c.num_patterns() == 0`). For MBQI, Z3 must find a witness `some_time` for any pair `(w1, w2)` where both are valid worlds with `w1 != w2`. This is expensive: each pair of worlds generates an existential obligation.

Adding patterns such as `patterns=[z3.MultiPattern(is_world(w1), is_world(w2))]` would restrict instantiation to only fire when both `is_world(w1)` and `is_world(w2)` appear as ground terms. **This could cause incompleteness**: if Z3 hasn't generated `is_world(n)` ground terms for some valid world ID `n`, the uniqueness obligation would never fire, and Z3 could produce a model with duplicate worlds. This would be a **soundness regression** -- the model would satisfy the constraints but be logically wrong.

---

### Finding 6: skolem_abundance Has a Nested ForAll -- Not Just Two Quantified Variables

**Confidence: High**

The `capped_skolem_abundance_constraint` has `num_vars=2` (source_world, shift_amount), but its consequent contains an **additional nested ForAll** via `matching_states_when_shifted_var`:

```python
ForAll([source_world, shift_amount],
    Implies(conditions,
        And(is_world(shift_of(src, shift)),
            start_eq,
            end_eq,
            ForAll([time],   # <-- nested!
                Implies(And(in_source_interval, in_target_interval),
                    Select(wf(src), t) == Select(wf(shift_of(src, shift)), t + shift))))))
```

So the effective quantifier depth is 3 (outer `ForAll [src, shift]` + inner `ForAll [time]`). For MBQI this means:
1. For any candidate `(src, shift)`, Z3 must verify the inner ForAll over all times.
2. This inner ForAll has no pattern, so MBQI generates witnesses heuristically.
3. At `N=3, M=4`: `source_world` ranges over ~16384 possible worlds.

Task 98 specifically cites "Z3's quantifier instantiation engine has no memory cap and expands ground terms unboundedly when processing the capped Skolem abundance constraint combined with forward_comp." This finding is consistent with the 3-level nesting observed here.

---

### Finding 7: world_interval_constraint Also Has a Doubly-Nested Quantifier

**Confidence: High**

`world_interval_constraint()` is used in `frame_constraints` (not the commented-out `time_interval_constraint`). Its body contains:

```
ForAll([interval_world], 
    Implies(is_world(interval_world),
        Or(And(start_eq1, end_eq1, ForAll(other_time, ...)),
           And(start_eq2, end_eq2, ForAll(other_time, ...)),
           ...M options...)))
```

Each `Or` branch contains a `valid_array_domain(interval_world, start, end)` which is itself a nested `ForAll`. This is doubly-quantified (outer world variable + inner time variable). The inner `ForAll` uses `Var(1)` to reference the outer bound variable -- Z3 must track this cross-quantifier reference.

For `M=4`, there are 4 `Or` branches, each with a `ForAll`. Combined with the large `max_world_id`, this constraint is significantly more expensive than its `num_vars=1` count suggests.

The commented-out `time_interval_constraint` (grounded version) would be worse: for `N=3, M=4` it would create `16,384 * 6 = 98,304` Z3 Python objects at constraint construction time. **Keep this commented out.**

---

### Finding 8: The Test Suite Has No Isolation Tests for Individual Frame Constraints

**Confidence: High**

The existing test files are:
- `test_bimodal.py`: Runs 60+ example cases end-to-end, tests valid/invalid classification.
- `test_frame_constraints.py`: Tests nullity, converse, and forward_comp **combined** in `solver.add(semantics.frame_constraints)`.

Neither file tests the effect of **removing** or **modifying** individual frame constraints. Specifically:
- No test verifies that removing `classical_truth` preserves all results.
- No test verifies that adding patterns to `world_uniqueness` preserves all results.
- No test isolates whether `world_interval` vs `time_interval` gives identical models.
- No test verifies `task_restriction` (commented out with `# MAYBE`) would be safe or harmful if added.

**KNOWN_TIMEOUT_EXAMPLES in test_bimodal.py** already excludes several cases:
- `TN_CM_1`, `TN_CM_2` (time out)
- `BM_CM_3` (Z3 state non-determinism)
- `MD_TH_2` (not explained)
- `BM_TH_1`, `BM_TH_2` (30s each, too slow for CI)
- `MF_MODAL_FUTURE_TH` (NOT a theorem under bimodal semantics)
- `BX7_LINEAR_U_TH`, `BX7P_LINEAR_S_TH` (N=4, M=5, OOM risk)

Any optimization must be validated against the FULL set including excluded examples, as these are precisely the high-M, high-N cases where the optimization matters most.

---

### Finding 9: task_restriction Removal Has Unknown Implications

**Confidence: Medium**

`task_restriction` (commented out with `# MAYBE`) constrains `task_rel` to only hold for transitions that appear in some lawful world history. Without it, `task_rel` is unconstrained -- Z3 can assert `task_rel(s, d, u)` for any states, regardless of whether a world history realizes that transition.

The `lawful` constraint requires that states in a world history are connected by `task_rel`. The `forward_comp` constraint derives composed `task_rel` relations. But **without `task_restriction`**, spurious `task_rel(s, d, u)` could exist for states that never appear together in any world history.

The impact depends on what the modal operators do: if `NecessityOperator` and temporal operators don't directly use `task_rel`, the spurious relations may be harmless. But if any operator or constraint queries `task_rel` to find paths between world states, spurious relations could introduce false countermodels.

**Gap**: There is no analysis of which operators use `task_rel` directly vs. which use `world_function` arrays. Investigation of `operators.py` shows that `NecessityOperator`, `FutureOperator`, and `PastOperator` all use `world_function` arrays, not `task_rel` directly. But `task_rel` is used in `lawful`, `task_restriction`, `nullity_identity`, `converse`, and `forward_comp`. The `forward_comp` pattern fires when `task_rel(w,d1,v)` AND `task_rel(v,d2,u)` are both present -- if `task_rel` is unconstrained, this could cause runaway composition derivation.

---

### Finding 10: Task 97 and Task 98 Optimizations May Conflict

**Confidence: Medium**

Task 97 targets performance optimization of frame constraints. Task 98 (dependency on 97) investigates OOM kills with M>=3. The proposed optimizations for task 97 might:

1. **Help OOM (good)**: Removing `classical_truth` reduces Z3 quantifier count. Adding patterns to reduce instantiation. These could reduce peak memory.

2. **Hurt OOM (bad)**: If a "fix" causes more Z3 instantiation cycles (e.g., wrong pattern choice forces MBQI to restart candidate generation), peak memory could increase even if wall-clock time improves.

3. **Trade wall-clock for memory**: Some optimizations might make the solver faster on small cases but cause it to allocate more memory for large M cases where the exponential domain is unavoidable.

The OOM behavior described in task 98 ("Z3's quantifier instantiation engine has no memory cap and expands ground terms unboundedly") is not addressable by constraint reordering or pattern annotations alone -- it requires either domain bounding (adding `ForAll n, n >= max_world_id -> not is_world(n)`) or a fundamentally different formulation for large N/M cases.

---

## Recommended Approach (Validation Strategy)

### Before Any Change

1. **Capture baseline**: Run the full test suite including `KNOWN_TIMEOUT_EXAMPLES` with extended timeouts. Record exact pass/fail/timeout for each example. This becomes the regression baseline.

2. **Profile individually**: Use `solver.statistics()` after each `solver.check()` call to capture `rlimit count`, `max memory`, and instantiation counts. Z3's statistics API provides `rlimit count` as a proxy for computational work.

3. **Establish order-sensitivity baseline**: Run the same 10 examples 5 times each with the current constraint order and document variance in solve time. High variance examples are at risk of false-positive validation.

### For Each Proposed Optimization

1. **Remove classical_truth**: Test ALL examples including examples with only `\bot` and `\top` (no sentence letters). Verify model extraction still works correctly for contingent examples.

2. **Add patterns to world_uniqueness**: Before adding any pattern, verify the resulting constraint is still `unsat` for `world_one == world_two` (a pair of identical worlds should still violate uniqueness). Add the pattern and run the full suite; any theorem that previously passed but now "finds a countermodel" is a soundness regression.

3. **Reorder constraints**: Document why the new order is expected to be better. Run 20+ trials of BM_CM_1, BM_CM_2, BM_CM_4 (known non-deterministic) to confirm no increase in timeout rate.

4. **Task 98 memory limits**: Before optimizing task 97, confirm that Z3's `memory_max_size` parameter can be set in `z3_adapter.py`. If yes, set a hard limit (e.g., 24GB) and verify that OOM kills turn into graceful "unknown" returns rather than process termination.

---

## Evidence/Examples (Specific Code References)

| Finding | File | Lines | Key Evidence |
|---------|------|-------|--------------|
| classical_truth tautology | semantic.py | 509-517 | `z3.simplify(ForAll([ws,sl], Or(f,Not(f)))) == True` (confirmed) |
| "order matters" undocumented | semantic.py | 668 | Comment with no explanation |
| task_minimization hard constraint | semantic.py | 1250-1275 | Hard `==` in body, not soft hint |
| max_world_id formula | semantic.py | 202 | `M * (2 ** (M * N))` -- N=3,M=4 gives 16,384 |
| is_world unbounded domain | semantic.py | 195-199 | `z3.Function('is_world', IntSort, BoolSort)` -- no upper bound |
| world_uniqueness no patterns | semantic.py | 596-616 | `num_patterns=0` confirmed in Python |
| skolem_abundance nested ForAll | semantic.py | 1187-1248 | `matching_states_when_shifted_var` is inner ForAll at line 1111 |
| world_interval nested ForAll | semantic.py | 797-828 | `valid_array_domain` is inner ForAll at line 908 |
| No isolation tests | tests/unit/test_frame_constraints.py | 207-231 | All tests use `solver.add(semantics.frame_constraints)` |
| task_restriction risk | semantic.py | 618-654 | 3-level nested exists; commented with `# MAYBE` |
| time_interval_constraint explosion | semantic.py | 830-876 | Loop over `range(max_world_id)` -- 16,384 iterations for N=3,M=4 |
| forward_comp has pattern | semantic.py | 380-388 | `patterns=[z3.MultiPattern(task_rel(w,d1,v), task_rel(v,d2,u))]` |
| MBQI/ematching both enabled | solver/z3_adapter.py | 37-39 | `smt.mbqi=True` AND `smt.ematching=True` simultaneously |

---

## Confidence Summary

| Finding | Confidence | Risk Level |
|---------|-----------|------------|
| classical_truth timing risk | Medium | Low-Medium |
| "order matters" undocumented | High | Medium |
| task_minimization mislabeled | High | High (if uncommented) |
| max_world_id exponential scaling | High | High (fundamental limit) |
| world_uniqueness soundness risk from patterns | High | High |
| skolem_abundance nested ForAll | High | High (memory) |
| world_interval nested ForAll | High | Medium |
| No isolation tests | High | Medium |
| task_restriction unknown implications | Medium | Medium |
| Task 97/98 optimization conflict | Medium | Medium |

---

## Appendix: Domain Size Quick Reference

To estimate impact of any optimization, use this table:

| N | M | max_world_id | In CI? | max_time |
|---|---|-------------|--------|----------|
| 1 | 1 | 2 | Yes | 5s |
| 2 | 1 | 4 | Yes | 2-10s |
| 1 | 2 | 4 | Yes | 10s |
| 2 | 2 | 32 | Yes | 2-15s |
| 1 | 3 | 24 | Yes | 10s |
| 2 | 3 | 192 | No (30s) | 30s |
| 3 | 3 | 648 | Yes | 10-15s |
| 2 | 4 | 1,024 | Yes | 15-20s |
| 3 | 4 | 16,384 | Yes | 15-30s |
| 4 | 5 | 5,242,880 | No (OOM) | 60s |

Optimizations that only help for `max_world_id < 1000` are low-value. The CI-included BX axiom examples at N=3,M=4 (`max_world_id=16384`) are the most important targets.
