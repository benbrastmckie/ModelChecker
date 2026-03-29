# Research Report: Task #42

**Task**: Uniform eval_point threading across all logos subtheory operators
**Date**: 2026-03-29
**Mode**: Team Research (2 teammates)
**Session**: sess_1774805513_25gkqo

## Summary

Research confirms the task description is accurate: modal and counterfactual operators construct bare `{"world": u}` dicts that silently drop the variable assignment, breaking compositionality with first-order formulas. The constitutive operators are already correctly aligned with the formal theory. The fix is straightforward and well-scoped.

## Key Findings

### Primary Approach (from Teammate A): Implementation Patterns

**The Core Problem**:
The `eval_point` dictionary carries both `"world"` (current world state) and optionally `"assignment"` (first-order variable bindings). Several intensional operators construct new eval_point dicts from scratch when shifting worlds, dropping the assignment key:

| File | Lines | Pattern | Impact |
|------|-------|---------|--------|
| `modal/operators.py` | 46, 58 | `{"world": u}` | Drops assignment in necessity |
| `modal/operators.py` | 118, 131 | `{"world": u, "time": ...}` | Drops assignment AND raises KeyError |
| `counterfactual/operators.py` | 50, 65 | `{"world": u}` | Drops assignment in counterfactual |

**Correct Pattern Exists**: First-order operators already use the correct pattern:
```python
assignment = sem.get_assignment(eval_point)
new_assignment = assignment.variant(variable, domain_elem)
new_eval_point = sem.with_assignment(eval_point, new_assignment)
```
This uses `{**eval_point, "assignment": ...}` to preserve all existing keys.

**Solution**: Add analogous `with_world` helper and use it in all world-shifting operators:
```python
def with_world(self, eval_point, world):
    """Create a new evaluation point with a different world, preserving all other keys."""
    return {**eval_point, "world": world}
```

**Extensional vs. Intensional Classification**:
- **Extensional operators** (negation, conjunction, disjunction, conditionals, constitutive): Pass `eval_point` unchanged - CORRECT
- **Intensional world-shifting** (necessity, counterfactual): Should use `with_world` - NEEDS FIX
- **Variable-binding** (forall, exists, lambda): Use `with_assignment` - CORRECT

### Theory Alignment (from Teammate B): Constitutive Semantics

**Two-Layer Architecture Confirmed**:
- **Hyperintensional layer** (chapter 02): `M, sigma, s forces phi` - verifiers and falsifiers
- **Intensional layer** (chapter 03): `M, tau, x, sigma, i |= phi` - truth at world-histories

**Constitutive Operators Are Correct**:
1. Correctly pin `extended_verify`/`extended_falsify` to null state
2. Thread `eval_point` through to sub-formulas (necessary for contingent arguments)
3. Use `extended_verify`/`extended_falsify` (hyperintensional) in inner quantifications
4. Ground and Essence clauses match the formal lemma exactly

**Relevance Operator Note**: Not formally specified in chapters 02-03, but consistent with the bilattice framework.

## Synthesis

### Conflicts Resolved
No conflicts between teammates - findings are complementary:
- Teammate A identified the problem sites and solution pattern
- Teammate B confirmed constitutive semantics are correct and need no changes

### Gaps Identified
1. **PossibilityOperator vestigial code**: Lines 118, 131 reference `eval_point["time"]` which doesn't exist - may need removal or rewrite
2. **Documentation**: The semantic principle (extensional vs intensional) should be documented in code comments

### Recommendations

**Phase 1: Add `with_world` helper** to `LogosSemantics` (semantic.py)
```python
def with_world(self, eval_point, world):
    """Create a new evaluation point with a different world, preserving all other keys."""
    return {**eval_point, "world": world}
```

**Phase 2: Fix modal operators** (modal/operators.py)
- NecessityOperator.true_at (line 46): `{"world": u}` -> `sem.with_world(eval_point, u)`
- NecessityOperator.false_at (line 58): `{"world": u}` -> `sem.with_world(eval_point, u)`
- PossibilityOperator: Review/remove vestigial bimodal code

**Phase 3: Fix counterfactual operators** (counterfactual/operators.py)
- CounterfactualOperator.true_at (line 50): `{"world": u}` -> `semantics.with_world(eval_point, u)`
- CounterfactualOperator.false_at (line 65): `{"world": u}` -> `semantics.with_world(eval_point, u)`

**Phase 4: Verify unchanged subtheories**
- Extensional operators: Confirm still pass `eval_point` through unchanged
- Constitutive operators: Confirm still correct (no changes needed)
- First-order operators: Confirm `with_assignment` pattern still works

**Phase 5: Test compositionality**
- Test `Box(forall x. phi(x))` - modal + first-order
- Test `(A boxright B) -> forall x. C(x)` - counterfactual + first-order

## Teammate Contributions

| Teammate | Angle | Status | Confidence |
|----------|-------|--------|------------|
| A | Implementation patterns | completed | high |
| B | Theory alignment | completed | high |

## References

- Teammate A findings: `specs/042_uniform_eval_point_threading/reports/01_teammate-a-findings.md`
- Teammate B findings: `specs/042_uniform_eval_point_threading/reports/01_teammate-b-findings.md`
- Theory chapter 02: `/home/benjamin/Projects/Logos/Theory/typst/manual/chapters/02-constitutive.typ`
- Theory chapter 03: `/home/benjamin/Projects/Logos/Theory/typst/manual/chapters/03-dynamics.typ`
- Modal operators: `src/model_checker/logos/subtheories/modal/operators.py`
- Counterfactual operators: `src/model_checker/logos/subtheories/counterfactual/operators.py`
- Semantic helpers: `src/model_checker/logos/semantic.py`
