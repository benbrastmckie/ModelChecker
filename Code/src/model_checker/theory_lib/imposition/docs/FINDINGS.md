# Imposition Theory Frame Constraint Testing Findings

## Test Configurations

### Baseline Configuration
- Uses original `actuality` constraint only
- Result: Only IM_TH_12 fails (as expected)

### Alternative 1 (actuality_v2)
- Replaces `actuality` with `actuality_v2` constraint
- `actuality_v2` ensures: For any possible state x, world y, and world z where x is part of z, then imposition(x, y, z) must hold

### Alternative 2 (nullity)
- Uses original `actuality` constraint
- Adds new `nullity` constraint
- `nullity` ensures: If state x is possible but not compatible with world y, and z is a world containing x, then imposition(x, y, z) must hold

## Test Results Summary

### Baseline (Original actuality only)
- **Failed**: IM_TH_12
- **Passed**: All other tests (32 passed)

### Alternative 1 (actuality_v2)
- **Failed Countermodels**: IM_CM_1, IM_CM_3, IM_CM_4, IM_CM_5, IM_CM_6, IM_CM_7, IM_CM_8, IM_CM_9, IM_CM_10, IM_CM_11, IM_CM_12, IM_CM_13, IM_CM_14, IM_CM_17
- **Passed Theorems**: All theorems passed (including IM_TH_12)
- **Total**: 14 failed, 19 passed

### Alternative 2 (actuality + nullity)
- **Failed Countermodels**: IM_CM_1, IM_CM_3, IM_CM_4, IM_CM_6, IM_CM_8, IM_CM_9, IM_CM_12
- **Passed**: All theorems passed (including IM_TH_12), and some countermodels
- **Total**: 7 failed, 26 passed

## Key Observations

1. **actuality_v2 Success**: Successfully fixes IM_TH_12, making it show "no countermodel" as expected
2. **actuality_v2 Over-constraint**: Causes many countermodel examples to fail, suggesting it's too strong
3. **nullity Partial Success**: Also fixes IM_TH_12 while causing fewer countermodel failures
4. **Common Failures**: Both alternatives cause failures in antecedent strengthening and contraposition examples

## Failed Test Categories

### Alternative 1 (actuality_v2) Failures
- Antecedent strengthening (IM_CM_1, IM_CM_3, IM_CM_4, IM_CM_5)
- Monotonicity (IM_CM_6)
- Contraposition (IM_CM_7, IM_CM_8, IM_CM_9)
- Transitivity (IM_CM_10, IM_CM_11, IM_CM_12)
- Sobel sequences (IM_CM_13, IM_CM_14)
- Disjunctive antecedent (IM_CM_17)

### Alternative 2 (nullity) Failures
- Antecedent strengthening (IM_CM_1, IM_CM_3, IM_CM_4)
- Monotonicity (IM_CM_6)
- Contraposition (IM_CM_8, IM_CM_9)
- Transitivity (IM_CM_12)

## Detailed Output Analysis

See specific test outputs in the following sections for detailed Z3 models and constraint analysis.