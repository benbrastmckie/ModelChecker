# Implementation Plan: Fix /todo Command Task Block Removal

**Project Number**: 215  
**Type**: bugfix  
**Priority**: High  
**Complexity**: Medium  
**Estimated Hours**: 2.5  
**Phases**: 6

---

## Overview

Fix the /todo command's task removal logic to remove complete task blocks (heading + body) instead of just heading lines. Currently, the command removes only task heading lines (e.g., "### 192. Fix...") without removing associated body metadata (Status, Priority, Description, Acceptance Criteria, etc.), leaving 129+ lines of orphaned content scattered in TODO.md.

**Root Cause**: Stage 4 "PrepareUpdates" specification lacks explicit task block structure definition. Current spec states "Remove [COMPLETED] tasks" without defining what constitutes a complete task (heading + body lines).

**Solution**: Update Stage 4 specification with explicit block identification logic, boundary detection patterns, and atomic removal of complete task blocks.

---

## Research Inputs

**From**: `.opencode/specs/215_fix_todo_task_removal/reports/research-001.md`

**Key Findings**:
1. Task structure: Heading line (`^### \d+\. `) + Body lines (all content until next boundary)
2. Task block boundaries: Start = `^### \d+\. `, End = next `^### \d+\. ` or `^## ` or `^---$` or EOF
3. Current removal: Heading only (incomplete)
4. Required removal: Complete block (heading + all body lines)
5. Impact: 129+ orphaned lines in `.opencode/specs/TODO.md`

**Solution Approach**: Specification enhancement (Approach 1) recommended for minimal disruption and fastest implementation.

**Testing Requirements**: 7 comprehensive test cases covering single/multiple tasks, EOF boundaries, section headings, nested lists, mixed statuses.

---

## Phase Breakdown

### Phase 1: Task Block Structure Definition [COMPLETED]

**Started**: 2025-12-28
**Completed**: 2025-12-28
**Estimated Time**: 30 minutes

**Objective**: Define explicit task block structure in Stage 4 specification with clear examples.

**Tasks**:
1. Add `<task_block_structure>` section to Stage 4 in `.opencode/command/todo.md`
2. Define heading pattern: `^### \d+\. Task title`
3. Define body: All lines until next boundary marker
4. Provide concrete example showing heading + body + boundary

**Deliverables**:
- Updated Stage 4 with `<task_block_structure>` XML section
- Clear definition: "A complete task block consists of heading + all body lines until boundary"
- Example task block showing structure

**Acceptance Criteria**:
- [ ] `<task_block_structure>` section added to Stage 4
- [ ] Heading pattern defined: `^### \d+\. `
- [ ] Body definition: "All lines until next boundary"
- [ ] Concrete example provided with annotations
- [ ] Unambiguous structure definition

**Files Modified**:
- `.opencode/command/todo.md` (Stage 4)

---

### Phase 2: Block Boundary Detection [COMPLETED]

**Started**: 2025-12-28
**Completed**: 2025-12-28
**Estimated Time**: 30 minutes

**Objective**: Specify explicit boundary detection patterns and precedence order.

**Tasks**:
1. Add `<block_boundaries>` section defining 4 boundary types
2. Specify regex patterns for each boundary type:
   - Next task heading: `^### \d+\. `
   - Section heading: `^## `
   - Horizontal rule: `^---$`
   - End of file: EOF
3. Define precedence order (first match wins)
4. Provide algorithm for boundary detection

**Deliverables**:
- `<block_boundaries>` XML section with 4 boundary patterns
- Regex patterns for each boundary type
- Precedence order specification
- Boundary detection algorithm

**Acceptance Criteria**:
- [ ] All 4 boundary types defined with regex patterns
- [ ] Precedence order specified (next heading > section > separator > EOF)
- [ ] Algorithm describes forward scan from heading to boundary
- [ ] Edge cases documented (task at EOF, task before section)

**Files Modified**:
- `.opencode/command/todo.md` (Stage 4)

---

### Phase 3: Process Steps Update [COMPLETED]

**Started**: 2025-12-28
**Completed**: 2025-12-28
**Estimated Time**: 30 minutes

**Objective**: Update Stage 4 process steps to specify atomic block removal instead of heading-only removal.

**Tasks**:
1. Rewrite step 1.a "Remove [COMPLETED] tasks" to specify block removal
2. Rewrite step 1.b "Remove [ABANDONED] tasks" to specify block removal
3. Add explicit block identification substeps:
   - Locate task heading line
   - Scan forward to find end boundary
   - Mark lines [heading, boundary-1] for removal
4. Specify atomic removal: "Remove all marked line ranges"
5. Add preservation notes for numbering and structure

**Deliverables**:
- Updated process step 1.a with block removal substeps
- Updated process step 1.b with block removal substeps
- Explicit algorithm for identifying complete blocks
- Atomic removal specification

**Acceptance Criteria**:
- [ ] Step 1.a specifies complete block removal (not just heading)
- [ ] Step 1.b specifies complete block removal (not just heading)
- [ ] Block identification substeps provided (locate, scan, mark, remove)
- [ ] Atomic removal emphasized
- [ ] Preservation requirements maintained (numbering, other tasks)

**Files Modified**:
- `.opencode/command/todo.md` (Stage 4, process section)

---

### Phase 4: Post-Removal Validation [COMPLETED]

**Started**: 2025-12-28
**Completed**: 2025-12-28
**Estimated Time**: 30 minutes

**Objective**: Add validation logic to detect orphaned content after task removal.

**Tasks**:
1. Add step 3 "Validate updates in memory" to Stage 4 process
2. Define orphaned content detection:
   - Scan for lines matching `^- \*\*` (metadata lines)
   - Check if preceded by `^### ` heading within 5 lines
   - Flag as orphaned if no heading found
3. Specify validation failure handling:
   - Log error with line numbers
   - Rollback removal
   - Return error to user
4. Add success path: validation passes → proceed to AtomicUpdate stage

**Deliverables**:
- Validation step 3 added to Stage 4 process
- Orphaned content detection algorithm
- Validation failure handling specification
- Success path specification

**Acceptance Criteria**:
- [ ] Validation step added after task removal
- [ ] Orphaned content detection pattern specified: `^- \*\*` without `^### ` in previous 5 lines
- [ ] Failure handling: log, rollback, return error
- [ ] Success path: proceed to next stage
- [ ] Validation prevents partial/incomplete removals

**Files Modified**:
- `.opencode/command/todo.md` (Stage 4, add validation step)

---

### Phase 5: Test Cases Documentation [COMPLETED]

**Started**: 2025-12-28
**Completed**: 2025-12-28
**Estimated Time**: 30 minutes

**Objective**: Document comprehensive test cases in Stage 4 specification.

**Tasks**:
1. Add `<test_cases>` section to Stage 4
2. Document 7 test cases from research:
   - TC1: Single completed task
   - TC2: Multiple completed tasks interspersed
   - TC3: Completed task at EOF
   - TC4: Completed task before section heading
   - TC5: Mixed COMPLETED and ABANDONED
   - TC6: Task with nested lists
   - TC7: Empty TODO (no completed tasks)
3. For each test case: setup, expected result, validation criteria
4. Add validation checklist (10 checks)

**Deliverables**:
- `<test_cases>` XML section with 7 test cases
- Each test case documented with setup/expected/validation
- Validation checklist (no orphaned lines, complete removal, structure preserved)

**Acceptance Criteria**:
- [ ] All 7 test cases documented from research
- [ ] Each test case has setup description
- [ ] Each test case has expected result
- [ ] Each test case has validation criteria
- [ ] Validation checklist provided (10 items)
- [ ] Edge cases covered (EOF, sections, nested lists)

**Files Modified**:
- `.opencode/command/todo.md` (Stage 4, add test cases section)

---

### Phase 6: Integration Testing and Validation [COMPLETED]

**Started**: 2025-12-28
**Completed**: 2025-12-28
**Estimated Time**: 30 minutes

**Objective**: Test updated specification with /todo command on sample TODO.md files.

**Tasks**:
1. Create test TODO.md samples for each of 7 test cases
2. Run /todo command on each sample
3. Validate results against acceptance criteria:
   - No orphaned metadata lines
   - Complete task blocks removed
   - Other tasks preserved
   - Numbering preserved
4. Document any issues discovered
5. Fix specification if validation fails
6. Retest until all tests pass

**Deliverables**:
- 7 test TODO.md sample files
- Test execution results
- Validation report
- Any specification fixes required

**Acceptance Criteria**:
- [ ] 7 test samples created
- [ ] All test samples executed with /todo command
- [ ] All validation checks pass (no orphaned lines, complete removal)
- [ ] No regressions in other /todo functionality
- [ ] Specification fixes applied if needed
- [ ] Final validation: all 7 tests pass

**Files Modified**:
- `.opencode/command/todo.md` (potential fixes based on testing)

---

## Success Criteria

The implementation will be considered successful when:

1. **Specification Complete**:
   - [ ] Task block structure defined explicitly
   - [ ] Block boundaries specified with regex patterns
   - [ ] Process steps updated for complete block removal
   - [ ] Post-removal validation added
   - [ ] Test cases documented

2. **Functionality Verified**:
   - [ ] /todo command removes complete task blocks (heading + body)
   - [ ] No orphaned metadata lines remain after archival
   - [ ] All [COMPLETED] and [ABANDONED] tasks fully removed
   - [ ] All other tasks preserved with complete structure
   - [ ] Task numbering preserved (no renumbering)
   - [ ] Section headings preserved
   - [ ] Validation detects orphaned content

3. **Testing Complete**:
   - [ ] All 7 test cases pass
   - [ ] Manual testing on real TODO.md confirms clean removal
   - [ ] No regression in other /todo functionality (archival, state updates, directory moves)

---

## Risk Assessment

**Low Risk**:
- Specification-only change (no code implementation)
- Clear documentation reduces interpretation ambiguity
- Validation step prevents partial failures

**Medium Risk**:
- AI agent interpretation of updated specification
  - *Mitigation*: Explicit examples, unambiguous language, test validation
- Edge cases not covered in test cases
  - *Mitigation*: 7 comprehensive test cases covering all scenarios

**Fallback**:
- If specification approach fails: Implement Python script (Approach 2 from research, 4.5 hours)

---

## Dependencies

**Internal**:
- None - specification-only update

**External**:
- None

**Blocking**:
- None

---

## Notes

- **No Code Implementation**: This is a specification-only fix updating `.opencode/command/todo.md`
- **Research Foundation**: Based on comprehensive research (task 215 research-001.md, 671 lines)
- **Approach Selection**: Specification enhancement (Approach 1) chosen over Python/bash scripts for minimal disruption
- **Estimated Effort**: Research estimated 2-3 hours, plan conservatively estimates 2.5 hours with 6 phases
- **Validation Critical**: Post-removal validation is essential to prevent partial failures
- **Testing Coverage**: 7 test cases cover all edge cases identified in research

---

## References

1. Research Report: `.opencode/specs/215_fix_todo_task_removal/reports/research-001.md`
2. Research Summary: `.opencode/specs/215_fix_todo_task_removal/summaries/research-summary.md`
3. Command Specification: `.opencode/command/todo.md`
4. Status Markers: `.opencode/context/core/standards/status-markers.md`
5. Artifact Management: `.opencode/context/core/system/artifact-management.md`
