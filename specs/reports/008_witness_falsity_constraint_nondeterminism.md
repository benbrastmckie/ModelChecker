# Witness Falsity Constraint Non-Determinism Investigation

## Metadata
- **Date**: 2025-10-02
- **Issue**: Witness predicate falsity constraint exhibits non-deterministic behavior
- **Status**: Implementation attempted, unreliable results
- **Related**:
  - specs/reports/007_box_countermodel_failure_investigation.md
  - specs/reports/006_hybrid_optimization_results.md

## Executive Summary

Investigation into BM_CM_1 countermodel failure revealed that the witness predicate infrastructure was missing a critical falsity constraint. Implementation of this constraint was attempted but exhibits non-deterministic behavior:

- **One successful run**: BM_CM_1 found countermodel in 0.24 seconds (11:32 PDT)
- **All subsequent runs**: BM_CM_1 times out without finding countermodel (12:25+ PDT)
- **Same code, same environment**: Results vary between runs

This non-determinism suggests either:
1. Z3 solver non-determinism with current quantifier structure
2. Subtle bug in falsity constraint implementation
3. Over-constraining that occasionally gets lucky with solver search order

**Conclusion**: The falsity constraint approach needs architectural reconsideration before it can be considered a reliable fix.

## Background

### The Missing Constraint Problem

Report 007 correctly identified that witness predicates ensure `accessible_world()` returns a **valid** world, but don't ensure the argument is **false** there:

```python
# What was implemented (before fix attempt):
main_constraint = z3.ForAll(
    [eval_world_var, eval_time_var],
    z3.Implies(
        z3.And(
            self.semantics.is_world(eval_world_var),
            self.semantics.is_valid_time_for_world(eval_world_var, eval_time_var)
        ),
        z3.And(
            # Only ensures witness is valid
            self.semantics.is_world(witness_world),
            self.semantics.is_valid_time_for_world(witness_world, eval_time_var)
        )
    )
)
# MISSING: Constraint that argument is false at witness_world!
```

This leaves Z3 without guidance about what value `accessible_world()` should return, making countermodel finding inefficient or impossible for Box formulas.

### BM_CM_1 Example

**Formula**: `\Future A |- \Box A`

**Expected countermodel**:
- World W0 where `\Future A` is true (A is true at some future time in W0)
- Conclusion `\Box A` is false in W0
- For `\Box A` to be false, there must exist an accessible world where A is false
- The witness `accessible_world(W0, t)` should return such a world

**Behavior before fix**:
- Timeout after 5 seconds
- No countermodel found
- UNSAT core shows no constrained clauses (Z3 gives up)

## Implementation Attempt

### Code Changes

Modified `Code/src/model_checker/theory_lib/bimodal/semantic/witness_constraints.py`:

#### 1. Implemented `_witness_constraint_for_falsity()` method

```python
def _witness_constraint_for_falsity(
    self,
    formula_str: str,
    argument_ast: Any,
    accessible_world_pred: z3.FuncDeclRef
) -> z3.BoolRef:
    """Generate constraint ensuring accessible_world points to a world
    where the argument is false."""

    # Variable names with formula prefix to avoid collisions
    eval_world_var = z3.Int(f'{formula_str}_falsity_eval_world')
    eval_time_var = z3.Int(f'{formula_str}_falsity_eval_time')

    # Get the witness world for this eval point
    witness_world = accessible_world_pred(eval_world_var, eval_time_var)

    # ForAll eval_world, eval_time:
    #   If (eval_world is valid AND eval_time is valid for eval_world)
    #   Then argument is false at (accessible_world(eval_world, eval_time), eval_time)
    falsity_constraint = z3.ForAll(
        [eval_world_var, eval_time_var],
        z3.Implies(
            z3.And(
                # Preconditions: eval point is valid
                self.semantics.is_world(eval_world_var),
                self.semantics.is_valid_time_for_world(eval_world_var, eval_time_var)
            ),
            # Postcondition: argument is false at witness world
            self.semantics.false_at(
                argument_ast,
                {"world": witness_world, "time": eval_time_var}
            )
        )
    )

    return falsity_constraint
```

#### 2. Integrated into `generate_witness_constraints()`

```python
constraints.append(main_constraint)

# Add falsity constraint if formula_ast is a Box formula
if formula_ast and hasattr(formula_ast, 'arguments') and formula_ast.arguments:
    argument_ast = formula_ast.arguments[0]
    falsity_constraint = self._witness_constraint_for_falsity(
        formula_str,
        argument_ast,
        accessible_world_pred
    )
    constraints.append(falsity_constraint)

return constraints
```

### Conceptual Correctness

The implementation is conceptually sound:

**For BM_CM_1**: `\Future A |- \Box A`
- We want to find a model where premise is TRUE and conclusion is FALSE
- For `\Box A` to be FALSE, there must exist an accessible world where A is false
- The falsity constraint ensures: `accessible_world(w, t)` returns a world where A is false
- This should make `Box.false_at()` work correctly

**Semantic interpretation**:
- The constraint applies to ALL evaluation points in the model
- It defines the FUNCTION `accessible_world()` globally
- For any world/time pair, calling `accessible_world()` returns a world where the argument is false

This is actually correct for the semantics of the witness predicate!

## Test Results: Non-Determinism

### First Test Run (11:32 PDT)

```bash
export PYTHONPATH=src && ./dev_cli.py src/model_checker/theory_lib/bimodal/examples.py
```

**Result**: ✅ SUCCESS
```
EXAMPLE BM_CM_1: there is a countermodel.

Atomic States: 2
Semantic Theory: Bimodal

Premise:
1. \Future A

Conclusion:
2. \Box A

Z3 Run Time: 0.24 seconds
```

**File**: `/tmp/bimodal_test.txt`
**Timestamp**: 11:32 AM PDT

### Second Test Run (12:25 PDT) - Fresh Python Cache

```bash
find src -name "*.pyc" -delete && find src -name "__pycache__" -type d -exec rm -rf {} +
export PYTHONPATH=src && ./dev_cli.py src/model_checker/theory_lib/bimodal/examples.py
```

**Result**: ✗ FAILURE
```
EXAMPLE BM_CM_1: there is no countermodel.

Atomic States: 2
Semantic Theory: Bimodal

Premise:
1. \Future A

Conclusion:
2. \Box A

Z3 Run Time: 5.0004 seconds
```

**File**: `/tmp/fresh_test.txt`
**Timestamp**: 12:25 PM PDT

### Third Test Run (12:26 PDT) - Testing Consistency

**Result**: ✗ FAILURE (same as second run)
```
Z3 Run Time: 5.0005 seconds
EXAMPLE BM_CM_1: there is no countermodel.
```

### Verification: Baseline Without Fix

```bash
git stash  # Remove falsity constraint changes
export PYTHONPATH=src && timeout 30 ./dev_cli.py src/model_checker/theory_lib/bimodal/examples.py
```

**Result**: ✗ FAILURE (as expected)
```
EXAMPLE BM_CM_1: there is no countermodel.
Z3 Run Time: 5.0006 seconds
```

After `git stash pop` to restore changes, still getting failures.

## Analysis

### Why Non-Determinism?

Several hypotheses for why the same code produces different results:

#### Hypothesis 1: Z3 Internal Non-Determinism

Z3's quantifier instantiation can be non-deterministic due to:
- **E-matching heuristics**: Order of pattern matching can vary
- **MBQI fallback**: Model-based instantiation may explore different paths
- **Hash-based internal data structures**: Iteration order not guaranteed

**Evidence**:
- Same code, same environment, different results
- Z3 documentation notes that quantifier solving is not deterministic
- No user-level Z3 configuration to force determinism

#### Hypothesis 2: Over-Constraining with Occasional Lucky Search

The falsity constraint might be over-constraining the model:

```python
# This says: "For ALL (w,t), argument is FALSE at accessible_world(w,t)"
# In other words: "Box(argument) is FALSE everywhere in the model"
z3.ForAll([w, t],
    Implies(valid(w,t),
        false_at(argument, accessible_world(w,t))
    )
)
```

This makes `\Box A` false in ALL worlds. For BM_CM_1:
- Premise `\Future A`: Requires A to be true at SOME future time in W0
- Conclusion `\Box A`: Made false everywhere by constraint
- But: Does making Box false everywhere conflict with finding a satisfying model for Future?

**Temporal vs Modal Independence**: `\Future A` talks about TIMES within a world. `\Box A` talks about OTHER WORLDS. These should be independent!

**Possible conflict**: If Z3's search heuristics start with trying to make Box true somewhere, then encounter the global falsity constraint, it might give up. But if it starts differently, it might find the model.

#### Hypothesis 3: Recursive Evaluation Causes Infinite Regress

The falsity constraint calls `self.semantics.false_at(argument_ast, ...)`:

```python
self.semantics.false_at(
    argument_ast,  # This is the argument INSIDE the Box
    {"world": witness_world, "time": eval_time_var}
)
```

If `argument_ast` itself contains modal operators, this could trigger recursive witness lookups:
- Evaluating `Box(Future A)` requires witness for `Future A`
- Witness constraint for `Future A` might require evaluating `Future A` at witness world
- This creates nested quantifiers over nested quantifiers

**For BM_CM_1**: Argument is just atomic `A`, so no recursion. This hypothesis doesn't apply here.

#### Hypothesis 4: Constraint Interaction with Frame Axioms

The bimodal theory has frame axioms ensuring world validity. The falsity constraint adds another layer of quantifiers. Possible interaction:

```
Frame axioms: ForAll w: [world properties]
Witness validity: ForAll w, t: Implies(valid(w,t), [witness is valid])
Falsity constraint: ForAll w, t: Implies(valid(w,t), [argument false at witness])
```

Three nested ForAll layers might trigger different instantiation patterns depending on Z3's internal state.

### Why Success on First Run?

The first successful run (0.24s) suggests the constraint CAN work. Possible explanations:

1. **Lucky E-matching Order**: Z3 happened to instantiate quantifiers in an order that quickly found the model
2. **Warm-up Effect**: Some Z3 internal state from previous runs helped (but cache was cleared...)
3. **System State**: CPU scheduling, memory allocation patterns, etc. affected Z3 heuristics
4. **Measurement Error**: Did I misread the output? (Verified: output file shows "there is a countermodel")

## Current Status

### What Works
- ✅ Falsity constraint implementation is syntactically correct
- ✅ Conceptually sound: witness should point to world where argument is false
- ✅ Worked once (0.24s), proving it CAN find the countermodel
- ✅ No regressions in other examples (when it runs)

### What Doesn't Work
- ✗ Non-deterministic: Same code gives different results
- ✗ Unreliable: Fails more often than it succeeds (1/4 runs successful)
- ✗ No clear debugging path: Can't reproduce success reliably

### Attempted Debugging
1. ✅ Cleared Python cache: No effect
2. ✅ Verified git state: Code is consistent
3. ✅ Checked baseline: Confirmed constraint is needed (baseline always fails)
4. ✗ Cannot reproduce success: Subsequent runs all fail

## Recommendations

### Immediate Actions

1. **Do NOT merge this implementation**: Non-deterministic behavior is unacceptable for production code

2. **Document the finding**: The witness infrastructure IS incomplete (Report 007 correct), but the fix attempted here is not reliable

3. **Revert to baseline**: Keep witness constraints WITHOUT falsity constraint until better solution found

### Alternative Approaches

#### Option A: Existential Witness Instead of Universal Function

Instead of a universal function `accessible_world(w,t)`, use existential constraints in each `Box.false_at()` call:

```python
def false_at(self, argument, eval_point):
    """Box is false if there EXISTS an accessible world where argument is false."""
    semantics = self.semantics
    eval_time = eval_point["time"]

    # Existential quantifier: there exists a world where argument is false
    witness_world_var = z3.Int(f'box_false_witness_{id(argument)}')

    return z3.And(
        semantics.is_world(witness_world_var),
        semantics.is_valid_time_for_world(witness_world_var, eval_time),
        semantics.false_at(argument, {"world": witness_world_var, "time": eval_time})
    )
```

**Pros**:
- No global witness function needed
- No universal constraints over ALL eval points
- Simpler Z3 constraint structure

**Cons**:
- Loses the witness predicate abstraction
- Every call creates new existential variable
- May be less efficient for multiple Box formulas

#### Option B: Selective Falsity Constraints

Only add falsity constraints when evaluating `Box.false_at()`, not globally:

```python
def false_at(self, argument, eval_point):
    # Get witness as usual
    witness_world = accessible_world_pred(eval_world, eval_time)

    # Add local constraint that argument is false at THIS witness
    return z3.And(
        semantics.is_world(witness_world),
        semantics.is_valid_time_for_world(witness_world, eval_time),
        semantics.false_at(argument, {"world": witness_world, "time": eval_time})
    )
```

The third line is ALREADY in the current `Box.false_at()` implementation! So why isn't this working?

**Answer**: Because the witness function `accessible_world()` is unconstrained. Z3 can choose ANY value for it, and only when evaluating `Box.false_at()` do we add the constraint that argument is false. But by then, Z3 may have already assigned the witness to some arbitrary world.

#### Option C: Two-Phase Witness Generation

1. **Phase 1**: Let Z3 generate model WITHOUT witness functions
2. **Phase 2**: Given the model, compute witness values explicitly in Python

This is similar to how Diamond operator works with existential search.

**Pros**:
- No complex quantifier interaction
- Deterministic witness computation
- Full control over witness selection

**Cons**:
- Requires major architectural change
- Two solver passes instead of one
- Not compatible with current framework

#### Option D: Quantifier-Free Witness Encoding

For finite domain (N worlds, M times), enumerate all possibilities:

```python
# Instead of: ForAll w,t: Implies(valid(w,t), false_at(arg, witness(w,t)))
# Use:
z3.And([
    z3.Implies(
        valid(w, t),
        false_at(argument, witness(w, t))
    )
    for w in range(N)
    for t in range(M)
])
```

**Pros**:
- Eliminates quantifier instantiation non-determinism
- Z3 handles propositional SAT well
- Deterministic results

**Cons**:
- Explosion for large N, M
- Less elegant than quantified approach
- May not scale to complex formulas

### Research Directions

1. **Z3 Quantifier Profiling**: Use Z3's quantifier instantiation profiling to understand what's happening differently between successful and failed runs

2. **Alternative Solvers**: Try CVC5 or other SMT solvers to see if issue is Z3-specific

3. **Constraint Decomposition**: Break falsity constraint into smaller pieces to identify problematic interaction

4. **Deterministic Z3 Configuration**: Research if there are Z3 settings to force deterministic solving (may sacrifice performance)

## Conclusion

The witness predicate falsity constraint issue identified in Report 007 is real and significant. The implementation attempted here is conceptually correct but exhibits unacceptable non-deterministic behavior in practice.

**Root cause of non-determinism**: Unknown, but likely related to Z3 quantifier instantiation heuristics interacting with the global ForAll constraint structure.

**Immediate recommendation**: Revert the falsity constraint implementation and document this as an open research problem requiring deeper investigation before attempting another fix.

**Long-term recommendation**: Consider architectural alternatives (Options A-D above) that avoid or minimize universal quantification over unconstrained functions.

## Files Modified (Currently Uncommitted)

- `Code/src/model_checker/theory_lib/bimodal/semantic/witness_constraints.py`
  - Lines 130-176: Implemented `_witness_constraint_for_falsity()`
  - Lines 116-125: Added falsity constraint to `generate_witness_constraints()`
- `specs/reports/006_hybrid_optimization_results.md`
  - Updated with falsity constraint findings (needs reversion)
- `specs/reports/007_box_countermodel_failure_investigation.md`
  - Added RESOLUTION section (needs reversion)

**Recommendation**: Revert all changes, document findings in this report (008), update Report 007 to note attempted fix and non-determinism issue.

## Test Evidence

### Successful Run Evidence

File: `/tmp/bimodal_test.txt`
```
EXAMPLE BM_CM_1: there is a countermodel.
Atomic States: 2
Semantic Theory: Bimodal
Premise:
1. \Future A
Conclusion:
2. \Box A
Z3 Run Time: 0.24 seconds
```

Timestamp: 2025-10-02 11:32 AM PDT

### Failed Run Evidence

File: `/tmp/fresh_test.txt`
```
EXAMPLE BM_CM_1: there is no countermodel.
Atomic States: 2
Semantic Theory: Bimodal
Premise:
1. \Future A
Conclusion:
2. \Box A
Z3 Run Time: 5.0004 seconds
```

Timestamp: 2025-10-02 12:25 PM PDT

### Time Delta
53 minutes between successful and failed run with identical code.

## Related Issues

- **BM_CM_2**: Still times out (pre-existing, separate issue)
- **TN_CM_2**: Still times out (pre-existing, not related to Box operator)
- **Reference Performance**: example_run.md shows BM_CM_1 at 0.14s (close to our successful 0.24s)

## Next Steps

1. Revert uncommitted changes
2. Update Report 007 to note attempted fix and non-determinism finding
3. Create issue tracking non-determinism problem
4. Research Option D (quantifier-free encoding) as most promising alternative
5. Consider consulting Z3 experts or mailing list about quantifier non-determinism
