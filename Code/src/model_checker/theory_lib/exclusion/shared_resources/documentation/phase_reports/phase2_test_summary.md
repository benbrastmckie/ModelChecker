# Phase 2 Test Results Summary

## Overview
After completing Phase 2 simplification and fixing all print functionality, the exclusion theory examples are fully runnable with the following results:

## Test Statistics
- **Total Examples**: 32
- **Examples with False Premises**: 10
- **Examples with True Conclusions**: 0
- **Examples with Errors**: 0

## Comparison with Baseline
- **Baseline False Premises**: 8
- **Current False Premises**: 10
- **Regression**: 2 additional examples now have false premises

## Examples with False Premises

### From Baseline (8)
1. **Double Negation Elimination**: Premise `¬¬A` evaluates to false
2. **Triple Negation Entailment**: Premise `¬¬¬A` evaluates to false
3. **Quadruple Negation Entailment**: Premise `¬¬¬¬A` evaluates to false
4. **Conjunctive DeMorgan's LR**: Premise `¬(A ∧ B)` evaluates to false
5. **Conjunctive DeMorgan's RL**: Premise `(¬A ∨ ¬B)` evaluates to false
6. **Disjunctive DeMorgan's LR**: Premise `¬(A ∨ B)` evaluates to false
7. **Disjunctive DeMorgan's RL**: Premise `(¬A ∧ ¬B)` evaluates to false
8. **EX_TH_18**: Complex formula with false premise

### New Regressions (2)
1. **No Gluts**: Premise `(A ∧ ¬A)` evaluates to false
2. **Disjunctive Syllogism**: Premise `¬B` evaluates to false

## Example Output Format

The restored print functionality now shows:

```
State Space
  #b000 = □
  #b001 = a (world)
  #b010 = b (world)
  #b011 = a.b (impossible)
  ...

Excludes
  a ✖ a
  a ✖ a.b
  ...

The evaluation world is: b

INTERPRETED PREMISE:
1. |(A ∧ ¬A)| = ∅ (False in b)
    |A| = {b} (True in b)
    |¬A| = ∅ (False in b)
      |A| = {b} (True in b)
```

## Key Observations

1. **Exclusion Operator Issues**: All false premises involve the exclusion operator (¬), confirming that the issue is in how exclusion is evaluated vs. how constraints are generated.

2. **Consistent Pattern**: The exclusion operator consistently returns empty verifier sets (∅) when it should have verifiers, leading to false evaluations.

3. **Regression Pattern**: The two new regressions (No Gluts, Disjunctive Syllogism) also involve exclusion operators, suggesting the simplification may have exposed additional edge cases.

## Next Steps for Phase 3

The false premise issue persists as expected. Phase 3 will need to:
1. Fix the recursive reduction in true_at for proper verifier existence checking
2. Ensure extended_verify for ExclusionOperator correctly implements the three conditions
3. Align constraint generation with truth evaluation
4. Test each fix against these 10 problematic examples