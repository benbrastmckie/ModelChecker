# Debug Report: Missing Countermodels in Bimodal Theory

## Metadata
- **Date**: 2025-10-01
- **Issue**: BM_CM_1, BM_CM_2, BM_CM_3 fail to find countermodels despite symmetry with BM_CM_4
- **Severity**: High
- **Type**: Logic bug in modal operator semantics
- **Related**: Witness predicate implementation (Phase 4)

## Problem Statement

After implementing witness predicates for bimodal modal operators (commits 89a6eabe and 27b2c9d2), three of four symmetric bimodal countermodel examples fail to find countermodels when they should:

| Example | Premise | Conclusion | Expected | Actual | Status |
|---------|---------|------------|----------|--------|--------|
| BM_CM_1 | ∀Future A | □A | Countermodel | No countermodel | ❌ FAIL |
| BM_CM_2 | ∀Past A | □A | Countermodel | No countermodel | ❌ FAIL |
| BM_CM_3 | ◇A | ∃future A | Countermodel | No countermodel | ❌ FAIL |
| BM_CM_4 | ◇A | ∃past A | Countermodel | **Countermodel found** | ✓ PASS |

**Key Observation**: BM_CM_4 succeeds, but BM_CM_1/2/3 fail. The difference is that BM_CM_4 has the modal operator (◇) in the **premise**, while the failing cases have modal operators (□ or future/past) in the **conclusions**.

## Investigation Process

### 1. Test Execution

Ran examples with:
```bash
PYTHONPATH=Code/src Code/dev_cli.py Code/src/model_checker/theory_lib/bimodal/examples.py
```

### 2. UNSAT Core Analysis

All three failing examples show:
```
UNSATISFIABLE CORE CONSTRAINTS:
- Frame constraints: 0
- Model constraints: 0
- Premise constraints: 0
- Conclusion constraints: 0
```

**Critical Finding**: All constraint counts are **ZERO**. This indicates Z3 found the constraint set UNSAT without needing any specific constraints. This suggests:
1. The frame constraints themselves are contradictory, OR
2. The combination of frame + modal constraints is unsatisfiable, OR
3. There's a fundamental error in how constraints are being generated

### 3. Witness Predicate Registration

Examined `semantic.py`:
```python
# Line 65: Witness registry initialized
self.witness_registry = WitnessRegistry(self.N, self.M)
```

**Finding**: Witness registry is initialized but **never populated**. No calls to `register_witness_predicate()` exist in the codebase.

**Impact**: The `NecessityOperator.false_at()` method always uses the fallback `Exists` quantification because no predicates are ever registered:
```python
# operators.py:423
if semantics.witness_registry.has_witness_predicate(formula_str):
    # Use witness predicate approach (NEVER EXECUTED)
else:
    # Fallback to existential quantification (ALWAYS EXECUTES)
```

### 4. Modal Operator Structure

**NecessityOperator.true_at()** (line 394):
```python
other_world = z3.Int('nec_true_world')
return z3.ForAll(other_world, ...)
```

**NecessityOperator.false_at()** (line 438-439):
```python
other_world = z3.Int('nec_true_world')  # SAME VARIABLE NAME
return z3.Exists(other_world, ...)
```

**Potential Issue**: Variable name collision when both `true_at()` and `false_at()` are called in the same context (e.g., when negating modal formulas in conclusions).

### 5. Symmetry Analysis

Why does BM_CM_4 succeed while BM_CM_1/2/3 fail?

**BM_CM_4** (succeeds):
- Premise: `◇A` → Uses `DefPossibilityOperator.true_at()` → Uses `NecessityOperator.false_at()`
- Conclusion: `∃past A` → No modal operator, just temporal existential

**BM_CM_1** (fails):
- Premise: `∀Future A` → No modal operator, uses `FutureOperator.true_at()`
- Conclusion: `□A` → When negated: `¬□A` → Uses `NecessityOperator.false_at()`

**Hypothesis**: The issue occurs when modal operators appear in **conclusions** (which get negated), not premises.

## Findings

### Root Cause Analysis

**Primary Cause**: Suspected constraint generation bug when modal operators appear in negated conclusions.

**Contributing Factors**:
1. Witness predicates are initialized but never populated
2. Variable name reuse in `NecessityOperator` (`'nec_true_world'` in both methods)
3. UNSAT core showing zero constraints suggests fundamental frame constraint issue
4. Asymmetry between premise and conclusion handling of modal operators

### Evidence

1. **UNSAT with zero constraints**: Indicates frame-level conflict
2. **Asymmetric behavior**: Only conclusion-modal cases fail
3. **Witness registry empty**: Predicates never registered despite infrastructure
4. **BM_CM_4 success**: Proves fallback `Exists` quantification can work

## Proposed Solutions

### Option 1: Fix Frame Constraint Generation

**Description**: Investigate why frame constraints are creating UNSAT before considering premises/conclusions.

**Approach**:
1. Add detailed logging to `build_frame_constraints()`
2. Check if `contingent=True` setting is causing issues
3. Verify `world_interval_start/end` constraints are valid
4. Test with simpler settings (N=2, M=1)

**Pros**: Addresses root cause if it's frame-level
**Cons**: Requires deep understanding of frame constraint logic

### Option 2: Implement Witness Predicate Registration

**Description**: Complete the witness predicate implementation by actually registering predicates during model building.

**Approach**:
1. Add `register_witness_predicate()` calls in `build_frame_constraints()`
2. Generate witness constraints using `WitnessConstraintGenerator`
3. Add witness constraints to `frame_constraints` list
4. Test if witness predicates avoid the UNSAT issue

**Pros**: Completes the feature as designed in Phase 4
**Cons**: May not fix the issue if root cause is elsewhere

### Option 3: Fix Variable Name Collision

**Description**: Use unique variable names in `NecessityOperator.true_at()` and `false_at()`.

**Approach**:
```python
# true_at(): Use 'nec_true_world'
# false_at(): Use 'nec_false_world' or 'nec_witness_world'
```

**Pros**: Simple fix, eliminates potential name collision
**Cons**: Unlikely to be root cause (Z3 should handle scoping)

### Option 4: Investigate Conclusion Negation

**Description**: Debug how conclusions are negated and constraints are built for modal operators in conclusions.

**Approach**:
1. Add logging to see how `¬□A` is expanded
2. Check if `DefPossibilityOperator` is correctly handling negation
3. Verify `false_at()` is being called correctly
4. Compare constraint structure between premise-modal and conclusion-modal cases

**Pros**: Directly targets observed asymmetry
**Cons**: May be complex to trace through negation logic

## Recommendations

**Priority 1** (Immediate): Option 4 - Investigate conclusion negation and modal operator handling
**Priority 2** (Short-term): Option 3 - Fix variable name collision as defensive measure
**Priority 3** (Medium-term): Option 2 - Complete witness predicate registration
**Priority 4** (Deep-dive): Option 1 - Full frame constraint audit if issues persist

## Next Steps

1. **Debug logging**: Add print statements to track:
   - How `□A` in conclusion gets negated
   - What constraints are generated for negated modals
   - Whether `true_at()` or `false_at()` is called

2. **Minimal reproduction**: Create single test case with just `□A` in conclusion to isolate issue

3. **Constraint inspection**: Export Z3 constraints to file and examine structure for contradictions

4. **Git bisect**: If needed, use git bisect to find exact commit that introduced regression (if this ever worked)

## References

- **Implementation Plan**: Code/src/model_checker/theory_lib/bimodal/specs/plans/002_witness_predicates_corrected.md
- **Examples File**: Code/src/model_checker/theory_lib/bimodal/examples.py (lines 309-379)
- **NecessityOperator**: Code/src/model_checker/theory_lib/bimodal/operators.py (lines 374-449)
- **BimodalSemantics**: Code/src/model_checker/theory_lib/bimodal/semantic.py (line 65)
- **Commits**:
  - 27b2c9d2: "feat: integrate witness predicates into NecessityOperator.false_at() (Phase 4 Part 2)"
  - 89a6eabe: "feat: integrate witness components into BimodalSemantics (Phase 4 Part 1)"

---

**Status**: Investigation complete, debugging required
**Next Actions**: Implement debug logging and minimal test case
**Assigned**: Pending implementation
