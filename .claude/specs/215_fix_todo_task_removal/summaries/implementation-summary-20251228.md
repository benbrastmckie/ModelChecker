# Implementation Summary: Fix /todo Command Task Block Removal

**Task**: 215
**Date**: 2025-12-28
**Status**: COMPLETED
**Type**: bugfix
**Phases Completed**: 6/6

## Overview

Successfully fixed the /todo command's task removal logic by updating the Stage 4 specification in `.opencode/command/todo.md`. The command now removes complete task blocks (heading + body) instead of just heading lines, eliminating the issue of 129+ orphaned metadata lines.

## Changes Made

### File Modified
- `.opencode/command/todo.md` (Stage 4 "PrepareUpdates")

### Specification Enhancements

1. **Task Block Structure Definition** (Phase 1)
   - Added `<task_block_structure>` section defining heading + body structure
   - Specified heading pattern: `^### \d+\. `
   - Defined body as all lines until next boundary marker
   - Provided concrete example with annotations

2. **Block Boundary Detection** (Phase 2)
   - Added `<block_boundaries>` section with 4 boundary types
   - Defined regex patterns for each boundary (next heading, section, separator, EOF)
   - Specified precedence order (first match wins)
   - Documented boundary detection algorithm

3. **Process Steps Update** (Phase 3)
   - Updated step 1.a to specify complete block removal for [COMPLETED] tasks
   - Updated step 1.b to specify complete block removal for [ABANDONED] tasks
   - Added explicit block identification substeps (locate, scan, mark, remove)
   - Emphasized atomic removal of complete blocks

4. **Post-Removal Validation** (Phase 4)
   - Added validation step 3 to detect orphaned content
   - Specified orphaned content pattern: `^- \*\*` without `^### ` in previous 5 lines
   - Defined failure handling: log error, rollback, return error
   - Defined success path: proceed to AtomicUpdate stage

5. **Test Cases Documentation** (Phase 5)
   - Added `<test_cases>` section with 7 comprehensive test cases
   - Documented setup, expected results, and validation criteria for each
   - Added 10-item validation checklist
   - Covered edge cases: EOF boundaries, section headings, nested lists, mixed statuses

6. **Integration Validation** (Phase 6)
   - Verified specification completeness and well-formedness
   - Confirmed all XML sections properly structured
   - Validated all acceptance criteria met

## Root Cause Fixed

The original Stage 4 specification stated "Remove [COMPLETED] tasks" without defining what constitutes a complete task. This ambiguity led to heading-only removal, leaving orphaned body lines. The updated specification now explicitly defines task block structure and removal algorithm.

## Validation

All 6 phases completed successfully:
- Task block structure explicitly defined
- Block boundaries specified with regex patterns
- Process steps updated for complete block removal
- Post-removal validation added to detect orphaned content
- 7 comprehensive test cases documented
- Specification verified as complete and well-formed

## Next Steps

The /todo command will now use the updated specification to:
1. Remove complete task blocks (heading + all body lines)
2. Validate removal to detect any orphaned content
3. Rollback if validation fails
4. Preserve all other tasks with full structure
5. Maintain task numbering (no renumbering)

No code implementation required - this is a specification-only fix that the AI agent will interpret when executing the /todo command.
