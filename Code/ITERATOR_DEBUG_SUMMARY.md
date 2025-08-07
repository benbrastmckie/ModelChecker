# Iterator Debug Investigation Summary

## Overview

This debug branch contains a systematic investigation of the iterator constraint preservation issue where MODEL 2+ produce invalid countermodels with false premises and true conclusions.

## Investigation Process

### Phase 1: Non-Invasive Analysis
- Created minimal test cases (`test_minimal_iterator.py`)
- Used existing debug flags (-z -p) to analyze behavior
- Created constraint verification script (`verify_constraints.py`)
- Identified mismatch between Z3 satisfaction and semantic evaluation

### Phase 2: Code Instrumentation
- Added strategic debug output to trace constraint flow
- Discovered Z3 reports constraints satisfied but evaluation fails
- Identified verify/falsify function reassignment as root cause

## Root Cause

**Issue**: ModelConstraints are built with MODEL 1's verify/falsify functions, but MODEL 2+ assign different functions, causing a context mismatch.

**Technical Details**:
- Constraints expect: `verify(1, A) = True` (from MODEL 1)
- MODEL 2 assigns: `verify(1, A) = False`
- Result: Premise A becomes false at evaluation world

## Documentation Created

1. **Debug Analysis**: `docs/specs/debug/001_iterator_constraint_analysis.md`
   - Complete investigation log with findings

2. **Findings**: `docs/specs/findings/019_iterator_constraint_preservation.md`
   - Consolidated technical analysis and root cause

3. **Research**: `docs/specs/research/002_iterator_fix_approaches.md`
   - Five alternative approaches with comparative analysis

4. **Debug Protocol**: `docs/DEBUG.md`
   - Generalized debugging methodology for future use

## Recommended Fix

**Approach 1: Fresh ModelConstraints** (Best long-term solution)
- Create new ModelConstraints for each iteration
- Ensures constraints match model context
- Highest correctness, moderate complexity

**Approach 2: Pin Functions** (Quick fix)
- Add constraints to preserve verify/falsify assignments
- Simple to implement but limits model diversity
- Good temporary solution

## Next Steps

1. Review the alternative approaches in `docs/specs/research/002_iterator_fix_approaches.md`
2. Choose preferred approach based on priorities (correctness vs simplicity)
3. Implement fix in a new branch
4. Verify all tests pass with fix applied

## Branch Status

- All debug code has been reverted
- Only documentation and research files remain
- Ready for implementation of chosen fix approach