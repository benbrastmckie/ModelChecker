# Phase 3 Handoff: New Tasks 107-110

**Task**: 106
**Phase**: 3 - Create New Tasks from Research Gaps
**Status**: COMPLETED
**Timestamp**: 2026-06-01

## What Was Done

Created 4 new task entries in `specs/TODO.md` (prepended at top) and 4 new active_project entries in `specs/state.json`. Updated `next_project_number` from 107 to 111.

## New Tasks Created

| Task | Name | Effort | Dependencies |
|------|------|--------|--------------|
| 107 | Boundary effect analysis and temporal_depth mitigation | medium | 102 |
| 108 | Soundness regression test suite for boundary and shift-closure edge cases | small | 103 |
| 109 | Cross-oracle differential testing infrastructure | medium | 103 |
| 110 | Frame class validation for Base frame | small | 100 |

## Notes for Phase 4

Phase 4 verifies and documents the dependency graph. Per the ADR dependency graph, the wave structure is:
- Wave 1: 100
- Wave 2: 101, 102, 110
- Wave 3: 103, 107
- Wave 4: 104, 108
- Wave 5: 105, 109

All dependency fields in TODO.md should already match this structure. Phase 4 verifies consistency and appends the dependency graph to the ADR (already present in the ADR from Phase 1).
