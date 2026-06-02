# Phase 2 Handoff: Task Description Rewrites for Tasks 100-105

**Task**: 106
**Phase**: 2 - Rewrite Task Descriptions for Tasks 100-105
**Status**: COMPLETED
**Timestamp**: 2026-06-01

## What Was Done

Rewrote all 6 task descriptions (100-105) in `specs/TODO.md` incorporating research findings from reports 02 and 03 and ADR decisions from Phase 1.

## Key Changes Per Task

- **Task 100**: Added expanded gate ("43 examples pass AND all unit tests in theory_lib/bimodal/tests/unit/ pass"), explicit keep-list, hard-coupling fixes with line numbers (theory_lib/__init__.py:52, builder/example.py:34, builder/runner.py:82,206).
- **Task 101**: Clarified directory structure is preserved (no core/ rename), added package name confirmation (bmlogic-oracle / bmlogic_oracle), entry point format, placeholder stub requirement.
- **Task 102**: Added temporal_depth() as required deliverable, Syntax programmatic constructor requirement, 6-tag field names, G/H boundary caveat.
- **Task 103**: Added ternary task_rel extraction loop, boundary buffer M = max(depth+2, 3), boundary_safe/temporal_depth/time_bound output fields, Z3 isolation strategy (fresh BimodalSemantics + isolated_z3_context).
- **Task 104**: Added explicit "do NOT remove" list (tests, examples.py, operators.py, extract_model_elements, print_* methods).
- **Task 105**: Added oracle pipeline test (test_oracle_interface.py), boundary regression tests, ternary serialization validation, temporal_depth reporting verification.

## Task 99 Note

Task 99 was already archived as "abandoned" with note "Absorbed by task 106 architecture review." No additional action needed.

## Notes for Phase 3

Phase 3 creates 4 new tasks (107-110) in TODO.md and state.json. Use next_project_number=107 from state.json. After phase 3, next_project_number must be updated to 111.
