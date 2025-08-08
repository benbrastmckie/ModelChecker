# Debug Report: Model Iteration Errors Investigation

## Overview

This report documents the investigation of errors encountered when running model iteration on three theory examples:
1. Exclusion theory examples
2. Imposition theory examples  
3. Logos counterfactual subtheory examples

## Test Commands

```bash
./dev_cli.py src/model_checker/theory_lib/exclusion/examples.py
./dev_cli.py src/model_checker/theory_lib/imposition/examples.py
./dev_cli.py src/model_checker/theory_lib/logos/subtheories/counterfactual/examples.py
```

## Findings

### 1. Exclusion Theory - CRITICAL ERROR

**Status**: ❌ FAILS with AttributeError

**Error Message**:
```
AttributeError: 'WitnessSemantics' object has no attribute 'falsify'
```

**Stack Trace**:
```python
Traceback (most recent call last):
  File "/home/benjamin/Documents/Philosophy/Projects/ModelChecker/Code/src/model_checker/builder/module.py", line 795, in process_example
    model_structures = theory_iterate_example(example, max_iterations=iterate_count)
  File "/home/benjamin/Documents/Philosophy/Projects/ModelChecker/Code/src/model_checker/theory_lib/exclusion/iterate.py", line 160, in iterate_example
    iterator = ExclusionModelIterator(example)
  File "/home/benjamin/Documents/Philosophy/Projects/ModelChecker/Code/src/model_checker/iterate/core.py", line 121, in __init__
    initial_pattern = StructuralPattern(
  File "/home/benjamin/Documents/Philosophy/Projects/ModelChecker/Code/src/model_checker/iterate/patterns.py", line 12, in __init__
    self.pattern = self._extract_pattern(model_constraints, z3_model)
  File "/home/benjamin/Documents/Philosophy/Projects/ModelChecker/Code/src/model_checker/iterate/patterns.py", line 48, in _extract_pattern
    if z3.is_true(z3_model.eval(semantics.falsify(state, letter), model_completion=True))
AttributeError: 'WitnessSemantics' object has no attribute 'falsify'
```

**Root Cause**:
The `StructuralPattern._extract_pattern` method assumes all semantic theories have both `verify` and `falsify` methods. However, the exclusion theory's `WitnessSemantics` class uses a unilateral semantics with only `verify` and `excludes` methods - it does not have a `falsify` method.

**Location in Code**:
- File: `src/model_checker/iterate/patterns.py`
- Lines: 44-49 (falsify pattern extraction)

### 2. Imposition Theory - SUCCESS

**Status**: ✅ PASSES - No errors

**Behavior**:
- Successfully finds 2 distinct models
- Pattern-based iteration works correctly
- All examples complete without errors

### 3. Logos Counterfactual Theory - SUCCESS

**Status**: ✅ PASSES - No errors

**Behavior**:
- Successfully finds 2 distinct models
- Handles edge cases gracefully (e.g., invalid models with no possible worlds)
- Pattern-based iteration works correctly

**Notable Message**:
```
[ITERATION] Found invalid model (no possible worlds) - attempt 1/5
```
This shows the iterator correctly handling and retrying when generating invalid models.

## Analysis

### Primary Issue: Semantic Theory Assumption

The pattern extraction code in `patterns.py` makes an incorrect assumption that all semantic theories implement bilateral semantics with both `verify` and `falsify` methods. This assumption breaks for unilateral semantics like exclusion theory.

### Code Location

```python
# src/model_checker/iterate/patterns.py, lines 44-49
pattern['falsify'] = {}

for letter in model_constraints.sentence_letters:
    letter_str = str(letter)
    pattern['falsify'][letter_str] = [
        state for state in all_states
        if z3.is_true(z3_model.eval(semantics.falsify(state, letter), model_completion=True))
    ]
```

## Recommendations

### Immediate Fix

The pattern extraction code should check if the semantic theory has a `falsify` method before attempting to use it:

```python
# Check if semantics supports falsification
if hasattr(semantics, 'falsify'):
    pattern['falsify'] = {}
    for letter in model_constraints.sentence_letters:
        letter_str = str(letter)
        pattern['falsify'][letter_str] = [
            state for state in all_states
            if z3.is_true(z3_model.eval(semantics.falsify(state, letter), model_completion=True))
        ]
else:
    pattern['falsify'] = None  # Or handle unilateral semantics differently
```

### Long-term Solution

Consider creating separate pattern extraction strategies for:
1. **Bilateral semantics** (verify/falsify) - logos, imposition, bimodal
2. **Unilateral semantics** (verify/excludes) - exclusion

This could be implemented through:
- A semantic type property on each theory
- Different pattern extraction methods based on semantic type
- Theory-specific pattern extractors

## Impact Assessment

- **Exclusion theory**: Currently broken for iteration
- **Other theories**: Working correctly
- **Pattern extraction**: Needs to be made semantic-aware

## Test Coverage Gap

The current test suite (`test_patterns.py`, `test_iterator_patterns.py`) only tests with mock semantics that have both `verify` and `falsify` methods. Tests should be added for unilateral semantics.

## Additional Finding: Core Iterator Issue

After fixing the pattern extraction, a similar issue was found in `core.py`:
- The `_extract_verify_falsify_from_z3` method (line 679) also assumes `falsify` exists
- The base `SemanticStructure.initialize_with_state` method assumes bilateral semantics
- This causes errors when building MODEL 2 for exclusion theory

## Resolution

All issues have been successfully resolved:

1. **Pattern extraction code in `patterns.py`**: Added `hasattr` check for falsify method
2. **Verify/falsify extraction in `core.py`**: Added similar check in `_extract_verify_falsify_from_z3`
3. **WitnessSemantics class**: Overrode `initialize_with_state` to handle unilateral semantics

## Verification Results

After implementing the fixes:

- **Exclusion theory**: ✅ Successfully finds 2 distinct models
- **Imposition theory**: ✅ Successfully finds 2 distinct models  
- **Logos counterfactual theory**: ✅ Successfully finds 2 distinct models

## Conclusion

The iteration implementation now correctly handles both bilateral and unilateral semantic theories. The key insight was that unilateral semantics (like exclusion theory) only have `verify` methods, not `falsify`, so all code must check for the existence of `falsify` before using it.