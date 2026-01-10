# Research Summary: Fix /todo Command Task Removal Logic

**Task**: 215  
**Date**: 2025-12-28  
**Status**: Complete

## Key Findings

Root cause confirmed: /todo command Stage 4 "PrepareUpdates" specification lacks explicit task block structure definition. Current specification states "Remove [COMPLETED] tasks" without defining complete task structure (heading + body lines). AI agent interprets this as removing only heading lines, leaving orphaned metadata scattered throughout TODO.md. Found 129+ lines of orphaned content in .opencode/specs/TODO.md across multiple removed tasks.

## Solution

Update Stage 4 specification with explicit block identification logic: task block starts at `^### \d+\.` heading, ends at next heading/section/EOF, includes all body lines between boundaries. Add validation to detect orphaned content post-removal. Specification enhancement approach recommended (2-3 hours) over Python/bash script alternatives.

## Implementation Estimate

2-3 hours for specification enhancement with comprehensive testing across 7 test cases covering single/multiple completed tasks, EOF boundaries, section boundaries, nested lists, and mixed COMPLETED/ABANDONED statuses.

## Artifacts

- Full Report: .opencode/specs/215_fix_todo_task_removal/reports/research-001.md
- 7 test cases defined with validation checklists
- 3 implementation approaches analyzed (specification, Python, bash)
- Explicit block removal algorithm provided
