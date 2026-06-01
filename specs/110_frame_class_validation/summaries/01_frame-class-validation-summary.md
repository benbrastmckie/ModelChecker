# Implementation Summary: Task #110 - Frame Class Validation for Base Frame

- **Task**: 110
- **Status**: COMPLETED
- **Date**: 2026-06-01
- **Duration**: ~1.5 hours

## Overview

Implemented documentation and tests validating the correspondence between the Z3 oracle's "Base" frame class and BimodalLogic's `TaskFrame` structure. All 4 phases completed with 13 new tests passing.

## What Was Implemented

### Phase 1: Frame Axiom Mapping Documentation

Added comprehensive documentation to two files:

**`code/src/bimodal_logic/provider.py`** - New module-level docstring (140 lines) covering:
- Terminology disambiguation: "Base" in `supported_frame_classes` means TaskFrame axiom satisfaction, NOT BimodalLogic's proof-system `FrameClass.Base` (37 axioms)
- Mapping table: Z3 constraint builder -> BimodalLogic TaskFrame.lean field
- Three Z3 approximation discrepancies (bounded domain, converse guard, forward_comp asymmetry)
- Soundness analysis of the disabled task_restriction constraint
- Added `supported_frame_classes = frozenset({"Base"})` attribute to the Z3OracleProvider stub

**`code/src/model_checker/theory_lib/bimodal/semantic.py`** - Two documentation additions:
- Frame hierarchy section in `build_frame_constraints()` classifying all 11 constraints into TaskFrame axioms (7-9), model-building (1-6, 8-9), and disabled (10)
- 50-line soundness analysis comment block near the disabled task_restriction constraint

### Phase 2: Test Infrastructure

Created `code/src/model_checker/theory_lib/bimodal/tests/unit/test_frame_class_mapping.py` with:
- `semantics` fixture: BimodalSemantics(N=2, M=2) for fast solver performance
- `solved_model` fixture: Adds frame constraints + task_rel(0,1,1) assertion, returns (semantics, model) pair
- `extract_task_rel_pairs()`: Enumerates all (source, duration, target) triples in model
- `extract_world_histories()`: Extracts {world_id: {time: state}} from model
- `TestFixtureSmoke`: 4 smoke tests verifying infrastructure works

### Phase 3: Post-Hoc Frame Axiom Validation Tests

5 test classes covering all TaskFrame axioms:

- `TestNullityIdentityPostHoc` (2 tests): Verifies no zero-duration tasks between distinct states; all states have self-tasks
- `TestConversePostHoc` (1 test): Verifies each (s,d,u) has converse (u,-d,s) within valid bounds
- `TestForwardCompPostHoc` (1 test): Verifies composable pairs yield their composition
- `TestLawfulHistoryPostHoc` (1 test): Verifies consecutive world-states connected by unit-duration tasks
- `TestFrameClassDeclarationConsistency` (4 tests): Documents and verifies the "Base" frame class claim

### Phase 4: Integration Verification

- All 13 new tests pass in ~9 seconds
- 8 existing `test_frame_constraints.py` tests still pass
- Full bimodal test suite: 184 passed, 1 pre-existing failure (BM_CM_1, not introduced by task 110)

## Plan Deviations

- **M=2 instead of M=3 for fixtures**: Plan specified M=3 for abundance/ShiftClosed alignment, but M=3 with N=2 causes solver timeout (>120s). M=2 is sufficient for testing all three TaskFrame axioms (durations -1, 0, 1). Deviation is justified and documented in fixture docstring.

## Artifacts

- `/home/benjamin/Projects/ModelChecker/code/src/bimodal_logic/provider.py` - Enhanced with frame hierarchy documentation
- `/home/benjamin/Projects/ModelChecker/code/src/model_checker/theory_lib/bimodal/semantic.py` - Enhanced docstrings and soundness analysis
- `/home/benjamin/Projects/ModelChecker/code/src/model_checker/theory_lib/bimodal/tests/unit/test_frame_class_mapping.py` - New test file (13 tests)
