# Debug Report: Proposition Linkage Fix for MODEL 2

## Problem

When MODEL 2 was created during iteration, it would fail with:
```
AttributeError: 'NoneType' object has no attribute 'model_structure'
```

This occurred when trying to print MODEL 2, specifically in modal operators that access `sentence_obj.proposition.model_structure`.

## Root Cause

The issue was that MODEL 2's sentences still had propositions pointing to MODEL 1:

1. MODEL 1 creates sentences and their propositions
2. Iterator creates MODEL 2 with fresh ModelConstraints
3. MODEL 2 reuses the same sentence objects from MODEL 1
4. These sentences still have `proposition` attributes pointing to MODEL 1
5. When printing MODEL 2, operators try to access `proposition.model_structure` which is MODEL 1's structure, not MODEL 2's

## Solution

Added a critical step in `_build_new_model_structure` after creating MODEL 2:

```python
# CRITICAL: Update propositions to point to new model structure
# Without this, sentences still have propositions pointing to MODEL 1
new_structure.interpret(new_structure.premises + new_structure.conclusions)
```

The `interpret` method:
1. Recursively traverses all sentences
2. Calls `update_proposition(self)` on each sentence
3. This creates new proposition objects linked to MODEL 2

## Implementation Details

### File Modified
`src/model_checker/iterate/core.py`, line 615

### Key Methods Involved
- `ModelDefaults.interpret()` - Recursively updates sentence propositions
- `Sentence.update_proposition()` - Creates proposition linked to model structure
- `PropositionDefaults.__init__()` - Takes model_structure as parameter

## Test Results

After fix, all theories successfully create MODEL 2:

```
✓ logos/modal       - Found 2/2 models
✓ logos/constitutive - Found 2/2 models  
✓ logos/relevance   - Found 2/2 models
✓ logos/extensional - Found 2/2 models
✓ logos/counterfactual - Found 2/2 models
✓ exclusion         - Found 2/2 models
✓ imposition        - Found 2/2 models
✓ logos (main)      - Found 2/2 models (with 1 example finding only 1/2)
```

## Remaining Issues

One example in main logos still only finds 1/2 models after 16 attempts. This appears to be a constraint generation issue rather than the proposition linkage problem.

## Lessons Learned

When creating new model structures that reuse syntax objects, it's critical to re-instantiate propositions to maintain proper object linkage. The `interpret` method is designed for exactly this purpose but wasn't being called during iteration.