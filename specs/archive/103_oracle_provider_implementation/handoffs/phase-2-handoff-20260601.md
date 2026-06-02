# Phase 2 Handoff: Serialization Helpers

**Phase**: 2 of 5
**Status**: COMPLETED
**Timestamp**: 2026-06-01

## What Was Done

Implemented `code/src/bimodal_logic/serialization.py` with four public functions:

1. `extract_true_false_atoms()`: Uses `structure.z3_main_world_state` (actual Z3 bitvec) with `semantics.truth_condition()` to evaluate atoms at the main evaluation point.

2. `extract_task_triples()`: Iterates `range(2**N) x range(-(M-1), M) x range(2**N)`, using `z3.BitVecVal(s, N)` and `z3.IntVal(d)` to convert integers to Z3 types for `semantics.task_rel()`.

3. `serialize_world_histories()`: Converts `structure.world_histories` (dict of dict) to list of `{"world_id": int, "times": {str: str}}` dicts. Note: values are already strings like 'a', 'b' from bitvec_to_worldstate conversion.

4. `serialize_countermodel()`: Assembles full result dict including all required keys.

## Key Finding

`structure.world_histories` stores STRING representations of states (e.g., 'a'), not Z3 bitvecs. For atom truth evaluation, must use `structure.z3_main_world_state` which is the actual Z3 BitVecNumRef.

## Verification

Manual test with EX_CM_1 (SAT):
- trueAtoms: [{'name': 'B'}]
- falseAtoms: [{'name': 'A'}]  
- task_triples: 4 nullity triples (d=0 self-loops)
- world_histories: [{'world_id': 0, 'times': {'0': 'a'}}]

## Next Phase

Phase 3: Implement `Z3OracleProvider.find_countermodel()` in `code/src/bimodal_logic/provider.py`.
Key: BimodalStructure second parameter is named `max_time` but receives full settings dict.
