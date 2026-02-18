# CVC5 Feasibility Test for BM_CM_1 Implementation Plan

## Metadata
- **Date**: 2025-10-02
- **Feature**: CVC5 feasibility test for witness predicate quantifier patterns
- **Scope**: Manual translation of BM_CM_1 example to CVC5 API
- **Estimated Phases**: 4
- **Standards File**: `/home/benjamin/Documents/Philosophy/Projects/ModelChecker/CLAUDE.md`
- **Research Reports**:
  - `specs/reports/009_alternative_smt_solvers_evaluation.md`
  - `specs/reports/010_z3_to_cvc5_refactoring_effort_assessment.md`
  - `specs/reports/008_witness_falsity_constraint_nondeterminism.md`

## Overview

This plan implements a focused feasibility test to determine if CVC5 can handle the witness predicate quantifier patterns that are problematic for Z3. Given that Plan 103 (quantifier-free encoding) **failed** to solve BM_CM_1, testing CVC5 is now the highest-priority next step.

### Problem Context

**Current State**:
- BM_CM_1 example: `\Future A |- \Box A` (should have countermodel)
- Z3 with quantified witness predicates: **Timeout (5s)**
- Z3 with quantifier-free witness encoding: **Timeout (5s)** (Plan 103 failed)
- Both approaches fail to find the countermodel

**Critical Question**: Does CVC5 have better quantifier instantiation heuristics for this specific pattern?

### Success Criteria

- [ ] CVC5 finds countermodel for BM_CM_1 (Z3 fails)
- [ ] CVC5 completes in <2 seconds (Z3 times out at 5s)
- [ ] Results are deterministic (5+ runs produce identical results)
- [ ] CVC5 API translation patterns are identified
- [ ] Decision made: proceed with full migration OR abandon CVC5

## Technical Design

### BM_CM_1 Example Specification

**Premises**: `\Future A` (A is true at some future time)
**Conclusion**: `\Box A` (A is true in all possible worlds)
**Expected**: Countermodel exists (conclusion false)

**Settings**:
- N = 2 worlds
- M = 2 time points
- Contingent propositions enabled

**Z3 Encoding** (current):
```python
# Atomic proposition
A = z3.Const("AtomSort!val!0", AtomSort)

# World structure
W = z3.Array(WorldIdSort, z3.ArraySort(TimeSort, WorldStateSort))

# Witness predicate for Box operator
Box_A_accessible_world = z3.Function(
    "Box_A_accessible_world",
    z3.IntSort(), z3.IntSort(),  # (eval_world, eval_time)
    z3.IntSort()  # returns accessible world
)

# Premise: Future A (A true at some future time in main world)
# Conclusion: Box A (A true in all worlds) - should be FALSE for countermodel

# Witness constraints (ForAll quantifier):
z3.ForAll([eval_world, eval_time],
    z3.Implies(
        z3.And(is_world(eval_world), is_valid_time(eval_world, eval_time)),
        z3.And(
            is_world(Box_A_accessible_world(eval_world, eval_time)),
            is_valid_time(Box_A_accessible_world(eval_world, eval_time), eval_time),
            false_at(A, Box_A_accessible_world(eval_world, eval_time), eval_time)
        )
    )
)
```

### CVC5 Translation Strategy

**API Mapping**:
```python
# Z3 → CVC5 Translation

# 1. Solver creation
solver = cvc5.Solver()
solver.setLogic("ALL")  # Full logic with quantifiers
solver.setOption("produce-models", "true")

# 2. Sorts (types)
IntSort = solver.getIntegerSort()
BoolSort = solver.getBooleanSort()
AtomSort = solver.mkUninterpretedSort("AtomSort")

# 3. Functions
accessible_world = solver.mkConst(
    solver.mkFunctionSort([IntSort, IntSort], IntSort),
    "Box_A_accessible_world"
)

# 4. Quantifiers
eval_world_var = solver.mkVar(IntSort, "eval_world")
eval_time_var = solver.mkVar(IntSort, "eval_time")

body = solver.mkTerm(
    cvc5.Kind.IMPLIES,
    precondition,
    postcondition
)

forall = solver.mkTerm(
    cvc5.Kind.FORALL,
    solver.mkTerm(cvc5.Kind.VARIABLE_LIST, eval_world_var, eval_time_var),
    body
)

# 5. Solving
result = solver.checkSat()
if result.isSat():
    # Extract model values
```

### Key Differences to Handle

1. **Term Construction**: CVC5 uses `mkTerm(Kind.*, ...)` vs Z3's infix operators
2. **Function Declaration**: Different pattern for uninterpreted functions
3. **Quantifier Syntax**: Requires explicit variable list term
4. **Model Extraction**: Iterator-based vs direct access

## Implementation Phases

### Phase 0: Environment Setup

**Objective**: Install CVC5 and verify basic functionality
**Complexity**: Low

**Tasks**:
- [ ] Install CVC5 Python bindings
  ```bash
  pip install cvc5
  ```
- [ ] Verify installation
  ```bash
  python -c "import cvc5; print(cvc5.__version__)"
  ```
- [ ] Test basic CVC5 usage
  ```python
  import cvc5
  slv = cvc5.Solver()
  slv.setLogic("QF_LIA")  # Quantifier-free linear integer arithmetic
  x = slv.mkConst(slv.getIntegerSort(), "x")
  constraint = slv.mkTerm(cvc5.Kind.GT, x, slv.mkInteger(0))
  slv.assertFormula(constraint)
  print(slv.checkSat())  # Should print "sat"
  ```

**Testing**:
```bash
# Quick smoke test
python3 -c "
import cvc5
s = cvc5.Solver()
s.setLogic('QF_LIA')
x = s.mkConst(s.getIntegerSort(), 'x')
s.assertFormula(s.mkTerm(cvc5.Kind.GT, x, s.mkInteger(0)))
print('CVC5 working:', s.checkSat().isSat())
"
```

**Validation**:
- CVC5 imports successfully
- Basic constraint solving works
- Ready to proceed with translation

### Phase 1: Manual BM_CM_1 Translation

**Objective**: Translate BM_CM_1 witness constraints to CVC5 API
**Complexity**: High

**Tasks**:
- [ ] Create `test_bm_cm_1_cvc5.py` script
  - Location: Project root (for easy execution)
  - Based on template from Report 009 Appendix
- [ ] Define CVC5 sorts (Integer, Boolean, AtomSort)
  - IntSort for world IDs and times
  - Uninterpreted sort for atomic propositions
- [ ] Create witness predicate function
  - `Box_A_accessible_world(world, time) -> world`
  - Uninterpreted function declaration
- [ ] Translate frame constraints (simplified)
  - World validity (0 <= w < N)
  - Time validity (within intervals)
- [ ] Encode premise: \Future A
  - A true at (world=0, time=1)
- [ ] Encode conclusion (negated): ~\Box A
  - Exists world where A is false
  - Use witness: accessible_world(0, 0) returns world where A false
- [ ] Add witness validity constraints (quantified)
  - ForAll eval_world, eval_time:
    If valid eval point, then witness valid
    AND argument false at witness
- [ ] Configure solver options
  - Set timeout (initially none, to see how long it takes)
  - Enable model production
  - Try different quantifier strategies if needed

**Implementation Template**:
```python
#!/usr/bin/env python3
"""
CVC5 Feasibility Test: BM_CM_1
Test if CVC5 can find countermodel for: \Future A |- \Box A
"""

import cvc5
from cvc5 import Kind
import time

def test_bm_cm_1_cvc5():
    """Test BM_CM_1 with CVC5 solver."""

    # Create solver
    slv = cvc5.Solver()
    slv.setLogic("ALL")  # Full logic with quantifiers + arithmetic
    slv.setOption("produce-models", "true")

    # Optional: Try different quantifier instantiation strategies
    # slv.setOption("smt.mbqi", "true")  # Model-based quantifier instantiation
    # slv.setOption("quant-cf", "true")  # Conflict-based instantiation

    # Define sorts
    IntSort = slv.getIntegerSort()
    BoolSort = slv.getBooleanSort()
    AtomSort = slv.mkUninterpretedSort("AtomSort")

    # Settings
    N = 2  # 2 worlds
    M = 2  # 2 time points

    # Atomic proposition A
    A = slv.mkConst(AtomSort, "A")

    # Truth condition function: truth(world, time, atom) -> bool
    truth_fn = slv.mkConst(
        slv.mkFunctionSort([IntSort, IntSort, AtomSort], BoolSort),
        "truth"
    )

    # Witness predicate: accessible_world(eval_world, eval_time) -> world
    accessible_world = slv.mkConst(
        slv.mkFunctionSort([IntSort, IntSort], IntSort),
        "Box_A_accessible_world"
    )

    # Helper: is_world(w) = (0 <= w < N)
    def is_world(w):
        return slv.mkTerm(
            Kind.AND,
            slv.mkTerm(Kind.LEQ, slv.mkInteger(0), w),
            slv.mkTerm(Kind.LT, w, slv.mkInteger(N))
        )

    # Helper: is_valid_time(w, t) = (within world's time interval)
    # Simplified: assume all times valid for all worlds
    def is_valid_time(w, t):
        return slv.mkTerm(
            Kind.AND,
            slv.mkTerm(Kind.LEQ, slv.mkInteger(0), t),
            slv.mkTerm(Kind.LT, t, slv.mkInteger(M))
        )

    # PREMISE: \Future A
    # Simplified: A is true at (world=0, time=1)
    premise = slv.mkTerm(
        Kind.APPLY_UF,
        truth_fn,
        slv.mkInteger(0),  # main world
        slv.mkInteger(1),  # future time
        A
    )
    slv.assertFormula(premise)

    # CONCLUSION (negated for countermodel): ~\Box A
    # We want: exists world where A is false
    # Use witness: accessible_world(0, 0) returns that world
    witness_world = slv.mkTerm(
        Kind.APPLY_UF,
        accessible_world,
        slv.mkInteger(0),  # eval at main world
        slv.mkInteger(0)   # eval at time 0
    )

    conclusion_false = slv.mkTerm(
        Kind.NOT,
        slv.mkTerm(Kind.APPLY_UF, truth_fn, witness_world, slv.mkInteger(0), A)
    )
    slv.assertFormula(conclusion_false)

    # WITNESS CONSTRAINTS (critical!)
    # ForAll eval_world, eval_time:
    #   If (valid eval point) Then (witness valid AND argument false there)

    eval_world_var = slv.mkVar(IntSort, "eval_world")
    eval_time_var = slv.mkVar(IntSort, "eval_time")

    witness_var = slv.mkTerm(Kind.APPLY_UF, accessible_world, eval_world_var, eval_time_var)

    precondition = slv.mkTerm(
        Kind.AND,
        is_world(eval_world_var),
        is_valid_time(eval_world_var, eval_time_var)
    )

    postcondition = slv.mkTerm(
        Kind.AND,
        # Witness must be valid world
        is_world(witness_var),
        # Witness time must be valid
        is_valid_time(witness_var, eval_time_var),
        # CRITICAL: Argument must be FALSE at witness
        slv.mkTerm(
            Kind.NOT,
            slv.mkTerm(Kind.APPLY_UF, truth_fn, witness_var, eval_time_var, A)
        )
    )

    witness_constraint = slv.mkTerm(
        Kind.FORALL,
        slv.mkTerm(Kind.VARIABLE_LIST, eval_world_var, eval_time_var),
        slv.mkTerm(Kind.IMPLIES, precondition, postcondition)
    )
    slv.assertFormula(witness_constraint)

    # SOLVE
    print("Solving BM_CM_1 with CVC5...")
    start = time.time()
    result = slv.checkSat()
    elapsed = time.time() - start

    print(f"Result: {result}")
    print(f"Time: {elapsed:.4f}s")

    if result.isSat():
        print("✅ Countermodel found!")

        # Extract key values
        print("\nModel values:")
        print(f"  truth(0,1,A) = {slv.getValue(slv.mkTerm(Kind.APPLY_UF, truth_fn, slv.mkInteger(0), slv.mkInteger(1), A))}")
        print(f"  accessible_world(0,0) = {slv.getValue(witness_world)}")
        print(f"  truth(witness,0,A) = {slv.getValue(slv.mkTerm(Kind.APPLY_UF, truth_fn, witness_world, slv.mkInteger(0), A))}")

        return True
    elif result.isUnsat():
        print("❌ UNSAT - No countermodel (incorrect, should exist)")
        return False
    else:
        print("⚠️ UNKNOWN - Solver could not determine")
        return False

if __name__ == "__main__":
    print("=" * 60)
    print("CVC5 Feasibility Test: BM_CM_1")
    print("Testing: \\Future A |- \\Box A")
    print("Expected: Countermodel exists")
    print("=" * 60)
    print()

    # Run 5 times to test determinism
    results = []
    times = []

    for i in range(5):
        print(f"\n--- Run {i+1} ---")
        success = test_bm_cm_1_cvc5()
        results.append(success)
        # Note: Would need to track times, but template above doesn't return it
        print()

    # Analyze results
    print("=" * 60)
    print("RESULTS SUMMARY")
    print("=" * 60)

    success_count = sum(results)

    if success_count == 5:
        print("✅ DETERMINISTIC: All 5 runs found countermodel")
        print("✅ DECISION: CVC5 succeeds where Z3 fails")
        print("✅ RECOMMENDATION: Proceed with CVC5 migration (Plan 010)")
    elif success_count == 0:
        print("❌ CONSISTENT FAILURE: No runs found countermodel")
        print("❌ DECISION: CVC5 has same issues as Z3")
        print("❌ RECOMMENDATION: Rethink witness predicate architecture")
    else:
        print(f"⚠️ NON-DETERMINISTIC: {success_count}/5 runs found countermodel")
        print("⚠️ DECISION: CVC5 also exhibits non-determinism")
        print("⚠️ RECOMMENDATION: Portfolio approach or alternative architecture")
```

**Testing**:
```bash
# Run the test
cd /home/benjamin/Documents/Philosophy/Projects/ModelChecker
python3 test_bm_cm_1_cvc5.py
```

**Validation**:
- Script runs without errors
- CVC5 produces a result (sat/unsat/unknown)
- Result is captured and analyzed
- Determinism tested across 5 runs

### Phase 2: Result Analysis and Comparison

**Objective**: Analyze CVC5 results and compare with Z3
**Complexity**: Medium

**Tasks**:
- [ ] Document CVC5 performance
  - Solving time for each run
  - Result (sat/unsat/unknown)
  - Memory usage (if observable)
- [ ] Compare with Z3 baseline
  - Z3 with quantified witnesses: 5s timeout, no result
  - Z3 with quantifier-free: 5s timeout, no result
  - CVC5 with quantified witnesses: [actual result]
- [ ] Test determinism
  - Run 5+ times
  - Check if results identical
  - Check if timing consistent
- [ ] Extract and validate countermodel (if found)
  - Verify premise satisfied (Future A true)
  - Verify conclusion false (Box A false)
  - Verify model structure makes semantic sense
- [ ] Try CVC5 solver options if initial test fails
  - Different quantifier instantiation modes
  - Timeout adjustments
  - Logic settings

**CVC5 Solver Options to Try** (if needed):
```python
# Model-based quantifier instantiation (like Z3's MBQI)
slv.setOption("smt.mbqi", "true")

# Conflict-based instantiation
slv.setOption("quant-cf", "true")

# Enumerative instantiation (CVC5's unique feature)
slv.setOption("quant-epr", "true")

# Timeout per check-sat call (milliseconds)
slv.setOption("tlimit-per", "5000")

# Incremental solving
slv.setOption("incremental", "true")
```

**Testing**:
```bash
# If CVC5 succeeds, validate the countermodel
# If CVC5 fails, try with different options

# Test with MBQI enabled
python3 test_bm_cm_1_cvc5.py --mbqi

# Test with conflict-based instantiation
python3 test_bm_cm_1_cvc5.py --quant-cf

# Test with timeout
python3 test_bm_cm_1_cvc5.py --timeout 10000
```

**Validation**:
- Performance metrics collected
- Comparison table created (Z3 vs CVC5)
- Determinism assessment complete
- Countermodel validated (if found)
- Solver options explored if needed

### Phase 3: API Translation Pattern Documentation

**Objective**: Document Z3→CVC5 translation patterns for future use
**Complexity**: Medium

**Tasks**:
- [ ] Create translation reference document
  - File: `specs/reports/011_z3_to_cvc5_api_translation.md`
  - Document all API differences encountered
  - Provide side-by-side examples
- [ ] Document key patterns
  - Solver creation and configuration
  - Sort/type definitions
  - Function declarations (uninterpreted functions)
  - Quantifier syntax (ForAll/Exists)
  - Constraint building (And, Or, Implies, etc.)
  - Model extraction
- [ ] Identify challenging translations
  - Patterns that were difficult to translate
  - Workarounds needed
  - Potential gotchas for full migration
- [ ] Estimate translation effort for full migration
  - Based on patterns encountered
  - Extrapolate to all Z3 usage in codebase
  - Update effort estimate in Report 010

**Translation Reference Template**:
```markdown
# Z3 to CVC5 API Translation Reference

## Solver Setup

| Z3 | CVC5 |
|----|------|
| `import z3` | `import cvc5; from cvc5 import Kind` |
| `solver = z3.Solver()` | `solver = cvc5.Solver()` |
| `solver.set("timeout", 5000)` | `solver.setOption("tlimit-per", "5000")` |

## Sorts (Types)

| Z3 | CVC5 |
|----|------|
| `z3.IntSort()` | `solver.getIntegerSort()` |
| `z3.BoolSort()` | `solver.getBooleanSort()` |
| `z3.DeclareSort("Atom")` | `solver.mkUninterpretedSort("Atom")` |

## [Continue with comprehensive reference...]
```

**Testing**:
- Review translation reference for accuracy
- Test each pattern with minimal example
- Ensure all BM_CM_1 patterns covered

**Validation**:
- Translation reference is complete
- All patterns from BM_CM_1 documented
- Examples are working
- Useful for full migration decision

### Phase 4: Decision and Next Steps

**Objective**: Make go/no-go decision on CVC5 migration
**Complexity**: Low

**Tasks**:
- [ ] Analyze all results
  - CVC5 performance: success or failure
  - Determinism: yes or no
  - Translation complexity: easy or hard
- [ ] Make recommendation
  - **If CVC5 succeeds**: Proceed with Plan 010 (6-10 week migration)
  - **If CVC5 fails**: Abandon CVC5, investigate alternatives
  - **If CVC5 partial**: Consider portfolio approach or further investigation
- [ ] Update Report 010 with findings
  - Add empirical CVC5 test results
  - Update recommendation section
  - Adjust effort estimates if needed
- [ ] Document decision
  - Create `specs/reports/011_cvc5_feasibility_results.md`
  - Include all test data, analysis, recommendation
  - Reference in Report 010
- [ ] Plan next action
  - If proceeding: Start Phase 1 of Plan 010 (abstraction layer)
  - If not: Plan alternative approach (new report/plan)

**Decision Matrix**:

| CVC5 Result | Determinism | Translation Complexity | Decision |
|-------------|-------------|------------------------|----------|
| ✅ Success | ✅ Yes | Easy/Medium | ✅ **Proceed with Plan 010** |
| ✅ Success | ❌ No | Easy/Medium | ⚠️ Portfolio approach |
| ✅ Success | ✅ Yes | Hard | ⚠️ Evaluate effort vs benefit |
| ❌ Failure | N/A | N/A | ❌ **Abandon CVC5, new approach** |

**Testing**:
- Review all collected data
- Validate decision logic
- Ensure recommendation is justified

**Validation**:
- Decision is data-driven
- All stakeholders aware of findings
- Next steps clearly defined
- Documentation complete

## Testing Strategy

### Test-Driven Approach

1. **Phase 1**: Write CVC5 translation, test incrementally
   - Start with basic sorts and constraints
   - Add witness predicates
   - Add quantifiers last (most complex)
   - Test each addition before proceeding

2. **Phase 2**: Comprehensive result validation
   - Verify CVC5 result matches expected (countermodel exists)
   - Cross-check with known BM_CM_1 model structure
   - Test multiple runs for determinism

3. **Phase 3**: Pattern extraction and documentation
   - Test each documented pattern in isolation
   - Ensure reproducibility

### Success Metrics

**Functional**:
- [ ] CVC5 finds countermodel (or conclusively fails)
- [ ] Results deterministic across 5+ runs
- [ ] Model structure validated

**Performance**:
- [ ] CVC5 solving time <5s (ideally <2s)
- [ ] Faster than Z3 (if it succeeds)

**Process**:
- [ ] Translation patterns documented
- [ ] Decision criteria met
- [ ] Next steps planned

## Documentation Requirements

### Files to Create/Update

1. **Test Script**: `test_bm_cm_1_cvc5.py`
   - Standalone Python script
   - Comprehensive comments
   - Can be run independently

2. **Translation Reference**: `specs/reports/011_z3_to_cvc5_api_translation.md`
   - Pattern catalog
   - Examples for each pattern
   - Gotchas and workarounds

3. **Results Report**: `specs/reports/012_cvc5_feasibility_results.md`
   - Test methodology
   - Results (with data)
   - Analysis and interpretation
   - Recommendation

4. **Update Report 010**: Add empirical findings
   - CVC5 test results section
   - Updated recommendation based on data
   - Revised effort estimates if applicable

## Dependencies

### External Dependencies
- **CVC5 Python bindings**: `pip install cvc5`
- **Python 3.8+**: Already installed
- **Time module**: Standard library

### Internal Dependencies
- Understanding of BM_CM_1 semantics (from examples.py)
- Knowledge of Z3 encoding (from current implementation)
- Report 009 (CVC5 evaluation)
- Report 010 (migration effort assessment)

### Prerequisites
- BM_CM_1 example definition (examples.py lines ~315-328)
- Understanding of witness predicate architecture
- Z3 baseline performance data (5s timeout, no result)

## Risk Assessment

### Risk 1: CVC5 Installation Issues
**Likelihood**: Low
**Impact**: Low

**Mitigation**:
- Test installation in Phase 0
- Use virtual environment if needed
- Document installation steps

**Fallback**: Use Docker container with CVC5 pre-installed

### Risk 2: API Translation Errors
**Likelihood**: Medium
**Impact**: High

**Mitigation**:
- Incremental translation with testing
- Reference CVC5 documentation throughout
- Compare with Report 009 appendix template

**Fallback**: Simplify translation, use minimal subset

### Risk 3: CVC5 Also Fails
**Likelihood**: Medium-High
**Impact**: Critical

**Mitigation**:
- Try multiple CVC5 solver options
- Document failure mode for analysis
- Prepare alternative strategy

**Fallback**: Abandon solver migration, rethink witness predicate architecture

### Risk 4: Inconclusive Results
**Likelihood**: Low
**Impact**: Medium

**Mitigation**:
- Run many trials (10+ if needed)
- Try different configurations
- Consult CVC5 community/docs if needed

**Fallback**: Mark as "needs further investigation", plan follow-up

## Timeline

**Phase 0**: 1-2 hours (CVC5 setup and verification)
**Phase 1**: 4-6 hours (BM_CM_1 translation and testing)
**Phase 2**: 2-3 hours (Result analysis and comparison)
**Phase 3**: 2-3 hours (Pattern documentation)
**Phase 4**: 1-2 hours (Decision and planning)

**Total Estimated Time**: 1-2 days

## Success Criteria Summary

### Must Have
- [ ] CVC5 test runs without errors
- [ ] Clear result (sat/unsat/unknown) obtained
- [ ] Determinism assessed (5+ runs)
- [ ] Translation patterns documented
- [ ] Go/no-go decision made with justification

### Nice to Have
- [ ] CVC5 finds countermodel (Z3 fails)
- [ ] CVC5 faster than Z3
- [ ] Translation patterns are simple
- [ ] Strong case for full migration

### Success Outcomes

**Best Case**: CVC5 finds countermodel in <2s, deterministically
→ **Action**: Proceed with Plan 010 (full CVC5 migration)

**Moderate Case**: CVC5 mixed results or partial success
→ **Action**: Portfolio approach or targeted CVC5 use

**Worst Case**: CVC5 fails like Z3
→ **Action**: Abandon solver approach, rethink witness predicate architecture

## Notes

### Design Decisions

**Why BM_CM_1?**
- Simplest failing example (quantified and quantifier-free both timeout)
- Well-understood expected result (countermodel exists)
- Representative of witness predicate pattern
- If CVC5 can't solve this, won't solve harder cases

**Why Manual Translation?**
- Fastest way to test feasibility (1-2 days vs weeks for full abstraction)
- Allows understanding API differences deeply
- Provides data for migration effort estimation
- Can iterate quickly on solver options

**Why Not Use pySMT?**
- Want to test CVC5 directly, not through abstraction
- pySMT adds translation overhead
- Need to understand raw CVC5 behavior for migration decision

### Implementation Notes

**CVC5 Quantifier Strategies**:
CVC5 has multiple quantifier instantiation techniques:
1. E-matching (like Z3)
2. Conflict-based instantiation (cbqi)
3. Enumerative instantiation (unique to CVC5)
4. Machine learning-guided (recent research)

Try different modes if initial test fails.

**Model Extraction Differences**:
- Z3: `model[var]` direct access
- CVC5: `solver.getValue(term)` for each term
- Need to construct terms for all values we want to extract

**Timeout Handling**:
- CVC5: Set per-check timeout with `tlimit-per` option
- Different from Z3's global timeout
- May need to tune for comparison

### Future Enhancements

If CVC5 succeeds:
1. Test other failing examples (BM_CM_2, TN_CM_2)
2. Benchmark CVC5 on all bimodal examples
3. Compare performance with Z3 across suite
4. Estimate full migration timeline based on patterns

If CVC5 fails:
1. Research alternative SMT solvers (Yices, veriT)
2. Investigate non-SMT approaches (SAT solver + theory)
3. Rethink witness predicate encoding fundamentally

## Commit Messages

**Phase 0**:
```
chore: setup CVC5 environment for feasibility testing

Install CVC5 Python bindings and verify basic functionality.
Smoke test confirms CVC5 can solve simple constraints.

Related: specs/plans/104_cvc5_feasibility_test.md
         specs/reports/010_z3_to_cvc5_refactoring_effort_assessment.md
```

**Phase 1**:
```
test: translate BM_CM_1 to CVC5 API for feasibility test

Manual translation of BM_CM_1 witness predicate constraints:
- Premise: \Future A (A true at future time)
- Conclusion: \Box A (A true in all worlds) - seeking countermodel
- Witness predicate with ForAll quantifier
- 5 runs for determinism testing

Z3 baseline: 5s timeout, no result (both quantified and quantifier-free)
CVC5 result: [To be determined]

Related: specs/plans/104_cvc5_feasibility_test.md
         specs/reports/009_alternative_smt_solvers_evaluation.md
```

**Phase 2**:
```
docs: analyze CVC5 vs Z3 performance on BM_CM_1

CVC5 Results:
- Result: [sat/unsat/unknown]
- Time: [X.XX]s (Z3: 5s timeout)
- Determinism: [Yes/No] (5 runs)

Analysis:
- [Interpretation of results]
- [Comparison with Z3]
- [Implications for migration]

Related: specs/plans/104_cvc5_feasibility_test.md
```

**Phase 3**:
```
docs: document Z3 to CVC5 API translation patterns

Created translation reference based on BM_CM_1 conversion:
- Solver setup and configuration
- Sort/type definitions
- Function declarations
- Quantifier syntax
- Constraint construction
- Model extraction

Estimated translation complexity: [Easy/Medium/Hard]

Related: specs/plans/104_cvc5_feasibility_test.md
         specs/reports/011_z3_to_cvc5_api_translation.md
```

**Phase 4**:
```
docs: CVC5 feasibility decision and results

Decision: [Proceed with CVC5 / Abandon CVC5 / Further investigation]

Key Findings:
- CVC5 [succeeded/failed] where Z3 timed out
- Translation complexity: [assessment]
- Determinism: [yes/no]
- Performance: [faster/slower/comparable]

Recommendation: [Next steps based on decision matrix]

Related: specs/plans/104_cvc5_feasibility_test.md
         specs/reports/012_cvc5_feasibility_results.md
         specs/reports/010_z3_to_cvc5_refactoring_effort_assessment.md
```

## Plan Summary

This plan implements a **1-2 day focused feasibility test** to determine if CVC5 can solve the witness predicate quantifier pattern that both Z3 approaches (quantified and quantifier-free) fail on.

**Approach**:
1. Install and verify CVC5
2. Manually translate BM_CM_1 to CVC5 API
3. Test for success, determinism, and performance
4. Document translation patterns
5. Make data-driven decision on full migration

**Outcome Possibilities**:
- **CVC5 succeeds** → Proceed with Plan 010 (6-10 week migration)
- **CVC5 fails** → Rethink witness predicate architecture
- **CVC5 partial** → Portfolio or targeted approach

**Critical Success Factor**: This test will definitively answer whether CVC5's quantifier handling is superior to Z3's for this specific pattern, informing the multi-week migration decision.
