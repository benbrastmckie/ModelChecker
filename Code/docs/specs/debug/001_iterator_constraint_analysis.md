# Debug Analysis 001: Iterator Constraint Preservation Issue

## Issue Summary

Iterator produces MODEL 2+ with false premises and true conclusions despite preserving all constraints. This violates the fundamental requirement that all models should be valid countermodels where premises remain true and conclusions remain false at the evaluation world.

## Reproduction Steps

1. Run any of these commands:
   ```bash
   ./dev_cli.py src/model_checker/theory_lib/exclusion/examples.py
   ./dev_cli.py src/model_checker/theory_lib/imposition/examples.py
   ./dev_cli.py src/model_checker/theory_lib/logos/examples.py
   ```
2. Expected behavior: All MODEL 2+ should have true premises and false conclusions at evaluation world
3. Actual behavior: MODEL 2+ often show false premises and/or true conclusions

## Investigation Log

### Phase 1: Non-invasive Analysis

- [x] Created minimal test case
- [ ] Analyzed with existing tools (-z -p flags)
- [ ] Created constraint verification script
- [ ] Reviewed related code
- [ ] Checked similar issues in findings/

### Phase 2: Code Instrumentation (if needed)

- [ ] Created debug branch
- [ ] Added instrumentation
- [ ] Collected debug output
- [ ] Identified root cause

## Test Cases

### Test 1: Minimal Atomic Premise
- Theory: logos
- Premises: ['A']
- Conclusions: []
- Settings: N=2, iterate=2

### Test 2: Negated Premise
- Theory: logos
- Premises: ['\\neg A']
- Conclusions: []
- Settings: N=2, iterate=2

### Test 3: Complex Formula
- Theory: logos
- Premises: ['(A \\wedge B)']
- Conclusions: ['C']
- Settings: N=2, iterate=2

### Test 4: Theory Comparison
- Run same test across logos, exclusion, imposition
- Compare behavior differences

## Findings

### Initial Observations
- Z3 constraints are correctly preserved (from findings 017/018)
- MODEL 1 always correct (premises true, conclusions false)
- MODEL 2+ often violate constraints despite Z3 satisfaction
- Issue occurs across multiple theories

### Constraint Analysis

From running test_minimal_iterator.py with -z -p flags:

1. **MODEL 1 always correct**: Premises true, conclusions false at evaluation world
2. **MODEL 2+ violations observed**:
   - TEST1: Premise A is FALSE at evaluation world 'a' (should be true)
   - TEST3: Conclusion C is TRUE at evaluation world 'a' (should be false)

From verify_constraints.py analysis:

1. **Premise constraint structure** for 'A':
   ```
   Or(And(0 | w == w, verify(0, A)),
      And(1 | w == w, verify(1, A)),
      And(2 | w == w, verify(2, A)),
      And(3 | w == w, verify(3, A)))
   ```
   This correctly encodes "A is true at w if some state containing w verifies A"

2. **Constraint references main_world**: The constraint properly uses variable 'w'

3. **Z3 constraint types**: All constraints are proper BoolRef expressions

### Z3 Model Comparison

From debug output comparison:

**TEST1 - MODEL 1 vs MODEL 2**:
- MODEL 1: Two worlds (a, b), A verified by 'a', falsified by 'b' → A true at 'a' ✓
- MODEL 2: One world (a), A verified by ∅, falsified by 'a' → A false at 'a' ✗

**Key observation**: In MODEL 2, the evaluation world 'a' is listed as falsifying A, making the premise false. This violates the premise constraint that should require A to be true at the evaluation world.

### Root Cause Analysis

**Hypothesis**: The iterator is finding models that satisfy constraints symbolically but not semantically. When Z3 builds MODEL 2:

1. It preserves all constraints including `premise_behavior(A)`
2. The constraint requires A to be true at world 'w'
3. But when building the new model, the verify/falsify functions are reassigned
4. The new assignment makes A false at the evaluation world
5. Z3 considers the constraint satisfied because it's evaluating symbolically, not checking the actual semantic evaluation

**Evidence**:
- Constraints are correctly generated (verified by script)
- Z3 claims constraints are satisfied (shown in model output)
- But semantic evaluation shows premises false (observed in output)
- This suggests a gap between Z3's symbolic satisfaction and semantic truth

### Related Issues
- Finding 017: MODEL 2 Empty Verifiers/Falsifiers (fixed sentence letter inclusion)
- Finding 018: Iterator Model vs Countermodel Behavior (clarified intent)

## Phase 1 Conclusion

The non-invasive investigation has revealed:
1. Constraints are correctly generated
2. Z3 claims all constraints are satisfied  
3. But semantic evaluation shows violations
4. This indicates a fundamental issue in how constraints are preserved/evaluated

**Decision**: Proceed to Phase 2 code instrumentation to trace the exact point where symbolic and semantic satisfaction diverge.

## Solution & Verification

### Proposed Fix
*To be determined after Phase 2 investigation*

### Test Results
*To be filled after implementing fix*

### Performance Impact
*To be assessed*

## Notes

Key questions to investigate:
1. Are premise/conclusion constraints being generated correctly?
2. Is Z3 interpreting constraints differently than our evaluation?
3. Is there a mismatch between model building and constraint satisfaction?
4. Do theory-specific semantics have bugs in true_at/false_at?