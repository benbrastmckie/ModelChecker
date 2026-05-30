# Implementation Summary: Task #91

**Completed**: 2026-05-29
**Duration**: ~45 minutes
**Session**: sess_1748540500_i91cb

## Overview

Refactored the task relation from binary `task(w, u)` to ternary `task_rel(w, d, u)` where `d` is an explicit duration parameter. This is a clean-break implementation with no backward compatibility - the old binary signature has been entirely removed.

## Changes Made

1. **Core Primitive Replacement**: Replaced `self.task` Z3 function with `self.task_rel` using ternary signature `(WorldStateSort, IntSort, WorldStateSort) -> BoolSort`

2. **Frame Constraint Updates**: 
   - Lawful constraint now uses `task_rel(..., z3.IntVal(1), ...)` for unit duration
   - Task restriction constraint includes duration quantification

3. **Model Injection Refactoring**: `inject_z3_model_values()` now enumerates over duration dimension `range(-M + 1, M)`

4. **Iteration Module Updates**: `_calculate_bimodal_differences()` tracks task relations with duration, using key format `"state1--[duration]-->state2"`

5. **Test Suite Updates**: Updated `test_inject_task_constraints` to use ternary `task_rel` API

6. **Documentation**: Added migration note to module docstring and updated inline comments

## Files Modified

- `code/src/model_checker/theory_lib/bimodal/semantic.py` - Primary changes:
  - Added module-level migration note docstring
  - Replaced `self.task` with `self.task_rel` in `define_primitives()`
  - Added helper methods: `is_valid_duration()`, `build_task_rel_at()`
  - Updated lawful constraint (line ~390) to use explicit duration=1
  - Updated task restriction constraint (line ~468) to quantify over duration
  - Updated `inject_z3_model_values()` to enumerate durations
  - Updated `print_model_differences()` for new format

- `code/src/model_checker/theory_lib/bimodal/iterate.py` - Updated:
  - `_calculate_bimodal_differences()` to use `task_rel` with duration enumeration
  - `display_model_differences()` to print "TaskRel" instead of "Task"

- `code/src/model_checker/theory_lib/bimodal/tests/integration/test_injection.py` - Updated:
  - `test_inject_task_constraints()` to use ternary `task_rel` API
  - Added assertion that old `task` attribute no longer exists

## Verification

- Build: N/A (Python - no compilation required)
- Tests: 136 bimodal tests PASSED
- Files verified: All modifications confirmed
- No remaining references to old `task` function in bimodal codebase

## ProofChecker Alignment

The implementation aligns with the Lean ProofChecker's semantics:
- `task_rel` signature matches `taskRel : S -> Q -> S -> Prop` (Frame.lean:72)
- Duration type uses `IntSort()` matching the time domain
- Duration bounds `(-M + 1, M)` ensure transitions stay within frame's time domain

## Notes

- Constraint count increases from O(N^2) to O(N^2 * D) where D = 2*M - 1
- For typical M=2, this is a 3x increase (manageable)
- Task 92 will add additional frame constraint axioms (nullity_identity, forward_comp, converse) that depend on this ternary signature
