# Phase 2 Handoff: Fix Constraint Dispatch in semantic.py

**Date**: 2026-06-01
**Status**: COMPLETED
**Phase**: 2 of 4

## Summary

Modified `build_frame_constraints()` in `semantic.py` to conditionally dispatch to a new
fully-ground abundance constraint implementation at M>=3.

## Key Changes

### semantic.py: Conditional Dispatch (~line 658)
Changed from:
```python
skolem_abundance = self.capped_skolem_abundance_constraint()
```
To:
```python
if self.M >= 3:
    skolem_abundance = self.build_grounded_abundance_constraints()
else:
    skolem_abundance = [self.capped_skolem_abundance_constraint()]
```

### semantic.py: Return Statement (~line 798)
Changed `skolem_abundance` to `*skolem_abundance` to unpack the list.

### semantic.py: `build_grounded_abundance_constraints` Method (Complete Rewrite)
The original implementation (Task 98) used `ForAll[src]` + Skolem function `shift_of_capped`.
This caused memory blowup at M>=3 because Skolem-created world IDs triggered MBQI
instantiation of other `ForAll[w]` frame constraints (lawful, world_interval).

The new implementation uses **fully ground** (quantifier-free) constraints:
- Enumerate source world IDs 0..3*M (e.g., 0..8 for M=3)
- For each (source_id, interval, shift) triple, assert: some target_id in 0..3*M exists as the shift
- Target existence expressed as a disjunction over bounded world IDs
- No Skolem functions, no ForAll quantifiers → Z3 resolves via pure SAT reasoning

Constraint counts: M=3: 54, M=4: 144, M=5: 300

## Deviations from Plan

The plan said to use `build_grounded_abundance_constraints()` (the existing ForAll[src]+Skolem
method). During implementation, we discovered this approach still causes memory blowup at M>=3
due to indirect MBQI interactions. The method was rewritten with a fully-ground (quantifier-free)
enumerated approach that resolves in <2 seconds at M=3.

## Test Results

- `test_shift_closure_on_extracted_worlds_m3`: XPASS (was xfail, now passes in 2s)
- `test_grounded_dispatch_at_m3`: PASSED
- `test_capped_dispatch_at_m2`: PASSED
- `test_m3_solver_no_timeout_on_atom`: PASSED (1.44s at M=3)
- All 12 boundary vacuity and compositionality tests: PASSED

## Next Phase

Phase 3: Change provider.py M formula from `max(depth, 2)` to `max(depth+2, 3)` and
update test assertions for the new M values and boundary_safe=True.
