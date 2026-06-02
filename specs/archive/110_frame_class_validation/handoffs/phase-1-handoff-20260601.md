# Phase 1 Handoff: Document Frame Axiom Mapping and Hierarchy

**Task**: 110
**Phase**: 1
**Status**: COMPLETED
**Timestamp**: 2026-06-01

## What Was Done

Added comprehensive frame hierarchy documentation to two files:

1. **code/src/bimodal_logic/provider.py** - New module-level docstring covering:
   - Terminology disambiguation ("Base" = TaskFrame axioms, not FrameClass.Base)
   - Mapping table: Z3 constraint builder -> BimodalLogic TaskFrame.lean field
   - Three Z3 approximation discrepancies (bounded domain, converse guard, forward_comp asymmetry)
   - List of 8 additional model-building constraints beyond the 3 TaskFrame axioms
   - Full soundness analysis for the disabled task_restriction constraint
   - Added `supported_frame_classes = frozenset({"Base"})` to the stub class

2. **code/src/model_checker/theory_lib/bimodal/semantic.py** - Two additions:
   - Frame hierarchy section in `build_frame_constraints()` docstring classifying all 11 constraints into TaskFrame axioms (7-9) vs model-building (1-6, 8-9) vs disabled (10)
   - 50-line soundness analysis comment block near the disabled task_restriction constraint explaining why disabling it is sound for countermodel generation

## Verification

- `grep -c "TaskFrame" code/src/bimodal_logic/provider.py` = 12 (present)
- `grep -c "soundness" code/src/model_checker/theory_lib/bimodal/semantic.py` = 1 (present)
- `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/unit/test_frame_constraints.py -v` = 8 passed

## Next Phase

Phase 2: Create test infrastructure and fixtures in test_frame_class_mapping.py
