# Findings: Why Counterfactual Examples Work on Commit e8820e77ecfb

## Summary

After careful analysis, I discovered that **the counterfactual examples appear to "work" on commit e8820e77ecfb by accident, not by design**. The iterator finds different models, but MODEL 2+ are not valid countermodels because they evaluate premises and conclusions with different verify/falsify functions than MODEL 1.

## The Fundamental Issue

The ModelChecker's iterator has a unique self-referential constraint problem:
- verify/falsify functions are **part of the model** being solved for
- When finding MODEL 2, we generate constraints using MODEL 1's functions  
- But Z3 solves for NEW verify/falsify functions in MODEL 2
- This means MODEL 2 evaluates formulas differently than MODEL 1

## Why It Appears to Work

On commit e8820e77ecfb, running counterfactual examples shows:
1. MODEL 1 is found correctly (valid countermodel)
2. MODEL 2 is found with different world structure
3. BUT: MODEL 2 shows the **exact same** |A|, |B|, |C| values as MODEL 1

This indicates MODEL 2 is using different verify/falsify functions but happening to produce the same evaluations. The premises and conclusions still have the same truth values, so it's not actually testing a different semantic scenario.

## What Changed During Refactoring

The current implementation tries to fix this by:
1. Using `object.__new__` to bypass ModelDefaults constructor
2. Manually initializing attributes in two phases
3. Attempting to preserve the Z3 model from iteration

However, this doesn't solve the fundamental issue - we're still creating fresh semantic functions rather than preserving MODEL 1's functions.

## The Core Architecture Problem

Both implementations suffer from the same issue:
1. **Working commit**: Creates fresh ModelDefaults which auto-solves with new functions
2. **Current code**: Tries to manually build structure but still gets new functions

Neither approach preserves MODEL 1's verify/falsify functions when creating MODEL 2.

## Evidence from Output

Looking at the counterfactual example output:
```
MODEL 1/2: 
|A| = < {a, a.b.c.d}, {b.c} >
|B| = < {a.b, a.b.c.d, ...}, {a.c} >  
|C| = < {a.c}, {a.b.c.d, a.b.d, a.d, b} >

MODEL 2/2:
|A| = < {a, a.b.c.d}, {b.c} >  # SAME AS MODEL 1!
|B| = < {a.b, a.b.c.d, ...}, {a.c} >  # SAME AS MODEL 1!
|C| = < {a.c}, {a.b.c.d, a.b.d, a.d, b} >  # SAME AS MODEL 1!
```

The verification/falsification changes shown in the diff are the **underlying** function changes, but the **evaluated propositions** remain the same.

## Why This Matters

For the iterator to work correctly for validity testing:
1. All models must use the SAME verify/falsify functions
2. Only the world structure should change between models
3. This ensures we're testing the same semantic interpretation across different structures

## Conclusion

The "working" commit doesn't actually work correctly - it finds structurally different models that happen to preserve truth values by accident. The refactoring exposed this issue by making it more obvious that MODEL 2 can have different truth values for premises/conclusions.

The solution requires implementing one of the approaches from our research:
1. **Evaluation Override** (recommended): Override proposition evaluation to use MODEL 1's functions
2. **Constraint Projection**: Project MODEL 1's evaluations as constraints
3. **Solver Integration**: Modify constraint generation to use fixed functions

None of these are currently implemented in either version of the code.