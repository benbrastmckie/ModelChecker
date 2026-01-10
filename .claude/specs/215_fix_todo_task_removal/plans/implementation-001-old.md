# Implementation Plan: Fix /todo Command Task Block Removal

**Task Number**: 215  
**Task Title**: Fix /todo command to remove both heading and body for completed/abandoned tasks  
**Plan Version**: 001  
**Created**: 2025-12-28  
**Status**: [NOT STARTED]  
**Language**: markdown  
**Estimated Effort**: 2.5 hours  
**Priority**: High

**Research Integration**: Integrated research findings from task 215 research identifying root cause (incomplete task block definition in Stage 4 specification) and solution (explicit block structure definition with boundary detection patterns).

---

## Overview

### Problem Statement

The /todo command's Stage 4 "PrepareUpdates" specification lacks explicit task block structure definition. Current spec states "Remove [COMPLETED] tasks" and "Remove [ABANDONED] tasks" without defining what constitutes a complete "task" (heading + body). This causes the AI agent to remove only heading lines (### NNN. Title), leaving all body lines (metadata like Status, Priority, Description, Acceptance Criteria, etc.) orphaned in TODO.md.

**Impact**: 129+ lines of orphaned content found in TODO.md after /todo command executions, creating clutter and confusion.

**Root Cause**: Specification ambiguity - "Remove [COMPLETED] tasks" is interpreted as "remove heading lines with [COMPLETED] status" rather than "remove complete task blocks (heading + all body content)".

### Scope

**In Scope**:
- Update Stage 4 "PrepareUpdates" specification in .opencode/command/todo.md
- Add explicit task block structure definition (heading + body)
- Add task block boundary detection patterns (next heading, section, separator, EOF)
- Add atomic removal specification (complete block, not just heading)
- Add post-removal validation to detect orphaned content
- Test with 7 test cases covering edge cases

**Out of Scope**:
- Changing task numbering behavior (already correct - no renumbering)
- Modifying archival workflow (Stage 3, 5, 6 - already correct)
- Changing status marker definitions (status-markers.md - already correct)
- Implementing the fix (this is specification update only)

### Constraints

**Technical**:
- Must preserve all existing Stage 4 functionality
- Must maintain backward compatibility with existing TODO.md format
- Must not break task numbering preservation
- Must not affect other stages (1-3, 5-7)
- Changes must be specification-only (no code implementation)

**Time**:
- Target completion: 2.5 hours total
- Must provide clear, unambiguous specification
- Must include comprehensive validation criteria

### Definition of Done

- [ ] Stage 4 specification updated with explicit task block structure definition
- [ ] Task block boundary detection patterns documented
- [ ] Atomic removal specification added (heading + body)
- [ ] Post-removal validation specification added
- [ ] 7 test cases documented in validation section
- [ ] Specification is clear and unambiguous
- [ ] No existing functionality broken
- [ ] Documentation updated

---

## Goals and Non-Goals

### Goals

1. **Explicit Block Definition**: Define task block structure as heading line + all body lines until next boundary
2. **Boundary Detection**: Specify patterns for detecting task block boundaries (next heading, section, separator, EOF)
3. **Atomic Removal**: Specify removal of complete blocks (heading + body) as atomic operation
4. **Validation**: Add post-removal validation to detect orphaned content
5. **Test Coverage**: Document 7 test cases covering edge cases

### Non-Goals

1. **Implementation**: Not implementing the fix (specification update only)
2. **Archival Changes**: Not modifying archival workflow (Stages 3, 5, 6)
3. **Status Changes**: Not changing status marker definitions
4. **Format Changes**: Not changing TODO.md format or structure

---

## Risks and Mitigations

### Risk 1: Specification Ambiguity Remains

**Severity**: High  
**Probability**: Medium  
**Impact**: AI agent still misinterprets specification

**Description**: Updated specification might still be ambiguous, leading to incorrect implementation.

**Mitigation**:
- Use explicit regex patterns for boundary detection
- Provide concrete examples of task blocks
- Include negative examples (what NOT to remove)
- Add validation criteria with specific patterns

**Contingency**: If ambiguity detected during implementation, iterate on specification with additional clarification.

### Risk 2: Edge Cases Not Covered

**Severity**: Medium  
**Probability**: Low  
**Impact**: Some task blocks not removed correctly

**Description**: Specification might miss edge cases like tasks at EOF, tasks before section headings, or tasks with nested lists.

**Mitigation**:
- Document 7 comprehensive test cases
- Include edge cases: EOF, section headings, nested lists
- Specify behavior for each edge case explicitly

**Contingency**: Add additional test cases as edge cases are discovered.

### Risk 3: Breaking Existing Functionality

**Severity**: High  
**Probability**: Low  
**Impact**: Other stages or workflows broken

**Description**: Changes to Stage 4 might inadvertently affect other stages or break existing functionality.

**Mitigation**:
- Limit changes to Stage 4 only
- Preserve all existing Stage 4 functionality
- Add validation to ensure no regressions
- Document what must NOT change

**Contingency**: Rollback specification changes if regressions detected.

---

## Implementation Phases

### Phase 1: Add Task Block Structure Definition [NOT STARTED]

**Estimated Effort**: 0.5 hours

**Objective**: Add explicit task block structure definition to Stage 4 specification.

**Tasks**:
1. Add new subsection "Task Block Structure" to Stage 4
2. Define task block components (heading + body)
3. Specify heading line pattern: `^### \d+\. `
4. Specify body line definition: all lines until next boundary
5. Provide concrete examples of task blocks

**Implementation**:

Add to Stage 4 after `<process>` section:

```markdown
<task_block_structure>
  A task block consists of:
    1. Heading line: ^### \d+\. {title}
    2. Body lines: All content lines until next task block boundary
  
  Task block boundaries (in order of precedence):
    1. Next task heading: ^### \d+\.
    2. Next section heading: ^##
    3. Horizontal separator: ^---$
    4. End of file (EOF)
  
  Example task block:
    ### 208. Fix /implement and /research routing
    - **Effort**: 2-3 hours
    - **Status**: [COMPLETED]
    - **Started**: 2025-12-28
    - **Completed**: 2025-12-28
    - **Priority**: High
    - **Language**: markdown
    - **Description**: Fix routing logic...
    - **Acceptance Criteria**:
      - [x] research.md Stage 2 includes validation
      - [x] implement.md Stage 2 includes routing logic
    
    [Next boundary: ### 205. or ## or --- or EOF]
  
  Complete block removal:
    - Remove heading line (### 208. Fix...)
    - Remove ALL body lines (- **Effort**: through last acceptance criterion)
    - Stop at next boundary (do NOT remove boundary line)
</task_block_structure>
```

**Acceptance Criteria**:
- Task block structure clearly defined
- Heading pattern specified with regex
- Body definition clear and unambiguous
- Boundary patterns specified with precedence
- Concrete example provided

**Dependencies**: None

**Deliverables**:
- Updated Stage 4 with task_block_structure section

---

### Phase 2: Add Block Boundary Detection Specification [NOT STARTED]

**Estimated Effort**: 0.5 hours

**Objective**: Specify how to detect task block boundaries for complete removal.

**Tasks**:
1. Add "Block Boundary Detection" subsection to Stage 4
2. Specify detection algorithm with regex patterns
3. Document boundary precedence order
4. Provide examples for each boundary type
5. Specify edge case handling (EOF, section headings)

**Implementation**:

Add to Stage 4 after task_block_structure:

```markdown
<block_boundary_detection>
  Algorithm for detecting task block end:
    1. Start at task heading line (^### \d+\. )
    2. Scan subsequent lines until boundary found
    3. Boundary patterns (check in order):
       a. Next task heading: ^### \d+\.
       b. Next section heading: ^## [^#]
       c. Horizontal separator: ^---$
       d. End of file (EOF)
    4. Block ends at line BEFORE boundary
    5. Boundary line is NOT part of block
  
  Regex patterns:
    - Task heading: r'^### \d+\. '
    - Section heading: r'^## [^#]'
    - Separator: r'^---$'
    - EOF: End of file (no more lines)
  
  Examples:
    
    Example 1 (Next task boundary):
      ### 208. Task A [COMPLETED]
      - **Status**: [COMPLETED]
      - **Description**: ...
      ### 209. Task B [NOT STARTED]  <-- Boundary (NOT removed)
      
      Remove: Lines "### 208..." through "- **Description**: ..."
      Keep: Line "### 209. Task B..."
    
    Example 2 (Section heading boundary):
      ### 208. Task A [COMPLETED]
      - **Status**: [COMPLETED]
      ## Medium Priority  <-- Boundary (NOT removed)
      
      Remove: Lines "### 208..." through "- **Status**: ..."
      Keep: Line "## Medium Priority"
    
    Example 3 (Separator boundary):
      ### 208. Task A [COMPLETED]
      - **Status**: [COMPLETED]
      ---  <-- Boundary (NOT removed)
      
      Remove: Lines "### 208..." through "- **Status**: ..."
      Keep: Line "---"
    
    Example 4 (EOF boundary):
      ### 208. Task A [COMPLETED]
      - **Status**: [COMPLETED]
      [EOF]  <-- Boundary
      
      Remove: Lines "### 208..." through "- **Status**: ..."
      No next line to keep
  
  Edge case handling:
    - Task at EOF: Remove through last line of file
    - Task before section: Remove through line before section heading
    - Empty lines in body: Include in block (remove with block)
    - Nested lists: Include in block (remove with block)
</block_boundary_detection>
```

**Acceptance Criteria**:
- Detection algorithm clearly specified
- Regex patterns provided for all boundaries
- Boundary precedence documented
- 4 examples covering all boundary types
- Edge cases explicitly handled

**Dependencies**: Phase 1 (task block structure defined)

**Deliverables**:
- Updated Stage 4 with block_boundary_detection section

---

### Phase 3: Update Process Steps for Atomic Removal [NOT STARTED]

**Estimated Effort**: 0.5 hours

**Objective**: Update Stage 4 process steps to specify atomic block removal instead of heading-only removal.

**Tasks**:
1. Update process step 1.a to specify block removal
2. Update process step 1.b to specify block removal
3. Add reference to task_block_structure and block_boundary_detection
4. Clarify that heading + body are removed together
5. Ensure numbering preservation language is clear

**Implementation**:

Update Stage 4 `<process>` section:

```markdown
<process>
  1. Create updated TODO.md content:
     a. Remove [COMPLETED] task blocks (heading + all body lines)
        - Identify task heading with [COMPLETED] status
        - Detect task block boundary using block_boundary_detection
        - Remove complete block atomically (heading through last body line)
        - Preserve boundary line (next heading, section, separator)
     b. Remove [ABANDONED] task blocks (heading + all body lines)
        - Identify task heading with [ABANDONED] status
        - Detect task block boundary using block_boundary_detection
        - Remove complete block atomically (heading through last body line)
        - Preserve boundary line (next heading, section, separator)
     c. Preserve all other task blocks (complete blocks, not just headings)
        - Keep [NOT STARTED], [IN PROGRESS], [RESEARCHED], [PLANNED], [BLOCKED]
        - Preserve complete blocks (heading + body)
     d. Preserve task numbering (do not renumber)
        - Gaps in numbering are acceptable and expected
        - See numbering_preservation section
  2. Create updated state.json content:
     a. Move archived tasks from active_projects to completed_projects (with archival metadata)
     b. Preserve entries for remaining active tasks
     c. Update repository_health metrics (reduce active_tasks count)
     d. Add recent_activities entries for each archived task
  3. Validate updates in memory
     - Verify no orphaned body lines remain (see post_removal_validation)
     - Verify all [COMPLETED] and [ABANDONED] blocks removed
     - Verify all other blocks preserved
     - Verify task numbering preserved
</process>
```

**Acceptance Criteria**:
- Process steps explicitly reference block removal
- Atomic removal specified (heading + body together)
- References to task_block_structure and block_boundary_detection added
- Validation step added
- Numbering preservation maintained

**Dependencies**: Phase 2 (boundary detection specified)

**Deliverables**:
- Updated Stage 4 process section

---

### Phase 4: Add Post-Removal Validation Specification [NOT STARTED]

**Estimated Effort**: 0.5 hours

**Objective**: Add validation specification to detect orphaned content after removal.

**Tasks**:
1. Add "Post-Removal Validation" subsection to Stage 4
2. Specify orphaned content detection patterns
3. Define validation success criteria
4. Specify error handling for validation failures
5. Provide examples of orphaned content

**Implementation**:

Add to Stage 4 after block_boundary_detection:

```markdown
<post_removal_validation>
  After removing [COMPLETED] and [ABANDONED] task blocks, validate that no
  orphaned body lines remain in TODO.md.
  
  Orphaned content detection:
    1. Scan TODO.md for metadata patterns outside task blocks
    2. Orphaned patterns (should NOT exist):
       - Lines matching r'^- \*\*' without preceding task heading
       - Lines matching r'^  - \[[ x]\]' without preceding task heading
       - Task metadata (Status, Priority, Effort, etc.) without task heading
    
    3. Valid context for metadata patterns:
       - Must have preceding task heading (^### \d+\. ) within last 50 lines
       - Must not have intervening section heading (^## )
       - Must not have intervening separator (^---$)
    
    4. Validation algorithm:
       a. Track current task heading (or None if outside task block)
       b. For each line:
          - If task heading: Set current_task = task_number
          - If section heading or separator: Set current_task = None
          - If metadata pattern and current_task is None: ORPHANED CONTENT DETECTED
       c. If orphaned content detected: Validation FAILED
       d. If no orphaned content: Validation PASSED
  
  Validation success criteria:
    - Zero lines matching orphaned patterns
    - All metadata lines have valid task heading context
    - No gaps between task heading and body
  
  Error handling on validation failure:
    - Log error: "Orphaned content detected after task removal"
    - List orphaned line numbers and content
    - Recommend manual review of TODO.md
    - Do NOT proceed with atomic update (Stage 5)
    - Return error to user with details
  
  Examples of orphaned content:
    
    Example 1 (Orphaned metadata after incomplete removal):
      ## High Priority
      - **Effort**: 2-3 hours  <-- ORPHANED (no task heading)
      - **Status**: [COMPLETED]  <-- ORPHANED
      ### 209. Valid Task
      - **Status**: [NOT STARTED]  <-- VALID (has task heading)
    
    Example 2 (Orphaned acceptance criteria):
      ## Medium Priority
      - **Acceptance Criteria**:  <-- ORPHANED
        - [x] Criterion 1  <-- ORPHANED
        - [x] Criterion 2  <-- ORPHANED
      ### 210. Valid Task
    
    Example 3 (Valid metadata - no orphans):
      ## High Priority
      ### 208. Task A
      - **Status**: [NOT STARTED]  <-- VALID
      - **Acceptance Criteria**:  <-- VALID
        - [ ] Criterion 1  <-- VALID
      ### 209. Task B
      - **Status**: [IN PROGRESS]  <-- VALID
</post_removal_validation>
```

**Acceptance Criteria**:
- Validation algorithm clearly specified
- Orphaned content patterns defined with regex
- Success criteria documented
- Error handling specified
- 3 examples provided (2 orphaned, 1 valid)

**Dependencies**: Phase 3 (process steps updated)

**Deliverables**:
- Updated Stage 4 with post_removal_validation section

---

### Phase 5: Add Test Cases and Documentation [NOT STARTED]

**Estimated Effort**: 0.5 hours

**Objective**: Document comprehensive test cases and update related documentation.

**Tasks**:
1. Add 7 test cases to validation section
2. Update quality_standards section with validation reference
3. Update validation section with post-removal validation
4. Ensure all test cases cover edge cases from research
5. Document expected behavior for each test case

**Implementation**:

Add to `<validation>` section at end of file:

```markdown
<test_cases>
  Test Case 1: Single completed task
    Input:
      ### 208. Task A [COMPLETED]
      - **Status**: [COMPLETED]
      - **Description**: Test task
      ### 209. Task B [NOT STARTED]
    
    Expected output:
      ### 209. Task B [NOT STARTED]
    
    Validation: No orphaned lines, task 209 preserved
  
  Test Case 2: Multiple completed tasks interspersed with active tasks
    Input:
      ### 207. Task A [NOT STARTED]
      - **Status**: [NOT STARTED]
      ### 208. Task B [COMPLETED]
      - **Status**: [COMPLETED]
      ### 209. Task C [NOT STARTED]
      - **Status**: [NOT STARTED]
      ### 210. Task D [COMPLETED]
      - **Status**: [COMPLETED]
      ### 211. Task E [NOT STARTED]
    
    Expected output:
      ### 207. Task A [NOT STARTED]
      - **Status**: [NOT STARTED]
      ### 209. Task C [NOT STARTED]
      - **Status**: [NOT STARTED]
      ### 211. Task E [NOT STARTED]
    
    Validation: Tasks 208, 210 removed completely, tasks 207, 209, 211 preserved
  
  Test Case 3: Completed task at EOF
    Input:
      ### 207. Task A [NOT STARTED]
      - **Status**: [NOT STARTED]
      ### 208. Task B [COMPLETED]
      - **Status**: [COMPLETED]
      - **Description**: Last task
      [EOF]
    
    Expected output:
      ### 207. Task A [NOT STARTED]
      - **Status**: [NOT STARTED]
      [EOF]
    
    Validation: Task 208 removed through EOF, task 207 preserved
  
  Test Case 4: Completed task before section heading
    Input:
      ## High Priority
      ### 208. Task A [COMPLETED]
      - **Status**: [COMPLETED]
      ## Medium Priority
      ### 209. Task B [NOT STARTED]
    
    Expected output:
      ## High Priority
      ## Medium Priority
      ### 209. Task B [NOT STARTED]
    
    Validation: Task 208 removed, section headings preserved
  
  Test Case 5: Mixed COMPLETED and ABANDONED tasks
    Input:
      ### 207. Task A [COMPLETED]
      - **Status**: [COMPLETED]
      ### 208. Task B [ABANDONED]
      - **Status**: [ABANDONED]
      ### 209. Task C [NOT STARTED]
    
    Expected output:
      ### 209. Task C [NOT STARTED]
    
    Validation: Both COMPLETED and ABANDONED tasks removed
  
  Test Case 6: Task with nested lists (acceptance criteria)
    Input:
      ### 208. Task A [COMPLETED]
      - **Status**: [COMPLETED]
      - **Acceptance Criteria**:
        - [x] Criterion 1
        - [x] Criterion 2
          - Sub-item 1
          - Sub-item 2
        - [x] Criterion 3
      ### 209. Task B [NOT STARTED]
    
    Expected output:
      ### 209. Task B [NOT STARTED]
    
    Validation: Entire task 208 removed including nested lists
  
  Test Case 7: Empty TODO.md (no completed tasks)
    Input:
      ### 207. Task A [NOT STARTED]
      - **Status**: [NOT STARTED]
      ### 208. Task B [IN PROGRESS]
      - **Status**: [IN PROGRESS]
    
    Expected output:
      ### 207. Task A [NOT STARTED]
      - **Status**: [NOT STARTED]
      ### 208. Task B [IN PROGRESS]
      - **Status**: [IN PROGRESS]
    
    Validation: No changes, all tasks preserved
</test_cases>
```

Update `<validation>` mid_flight section:

```markdown
<mid_flight>
  - Archival context prepared (archive entries, move operations)
  - TODO.md and state.json updates prepared in memory
  - archive/state.json updates prepared in memory
  - Task blocks identified with complete boundaries
  - Block removal prepared (heading + body)
  - Post-removal validation passed (no orphaned content)
  - Validation passed (well-formed JSON, valid paths)
  - Backups created
</mid_flight>
```

**Acceptance Criteria**:
- 7 test cases documented with input/output/validation
- All edge cases from research covered
- Validation section updated with post-removal validation
- Expected behavior clear for each test case

**Dependencies**: Phase 4 (validation specification added)

**Deliverables**:
- Updated validation section with test cases
- Updated mid_flight validation

---

## Testing and Validation

### Unit Testing

**Scope**: Verify specification clarity and completeness

**Test Cases**:
1. **Task Block Structure**: Definition is clear and unambiguous
2. **Boundary Detection**: Patterns are complete and correct
3. **Atomic Removal**: Process steps specify complete block removal
4. **Validation**: Post-removal validation detects orphaned content

**Success Criteria**:
- All sections clearly written
- No ambiguous language
- All patterns specified with regex
- All edge cases covered

### Integration Testing

**Scope**: Verify specification integrates with existing stages

**Test Cases**:
1. **Stage 1-3 Compatibility**: Changes don't affect earlier stages
2. **Stage 5-7 Compatibility**: Changes don't affect later stages
3. **Numbering Preservation**: Specification maintains numbering preservation
4. **Archival Workflow**: Specification doesn't break archival

**Success Criteria**:
- No conflicts with other stages
- All existing functionality preserved
- Numbering preservation maintained
- Archival workflow intact

### System Testing

**Scope**: Verify specification completeness for implementation

**Test Cases**:
1. **7 Test Cases**: All test cases have clear expected behavior
2. **Edge Cases**: All edge cases from research covered
3. **Error Handling**: Validation failure handling specified
4. **Examples**: Concrete examples provided for all concepts

**Success Criteria**:
- Specification is implementable without ambiguity
- All test cases pass when implemented
- Edge cases handled correctly
- Error handling comprehensive

### Validation Criteria

**Correctness**:
- [ ] Task block structure correctly defined
- [ ] Boundary detection patterns correct
- [ ] Atomic removal specified correctly
- [ ] Validation algorithm correct

**Completeness**:
- [ ] All boundary types covered
- [ ] All edge cases covered
- [ ] All test cases documented
- [ ] Error handling specified

**Clarity**:
- [ ] No ambiguous language
- [ ] Concrete examples provided
- [ ] Regex patterns specified
- [ ] Expected behavior clear

---

## Artifacts and Outputs

### Specification Artifacts

1. **Updated todo.md**
   - Location: `.opencode/command/todo.md`
   - Changes: Stage 4 updated with 5 new sections
   - Lines added: ~250 lines

2. **Specification Sections Added**:
   - task_block_structure (30 lines)
   - block_boundary_detection (80 lines)
   - Updated process (40 lines)
   - post_removal_validation (60 lines)
   - test_cases (100 lines)

### Documentation Artifacts

1. **Updated TODO.md** (this file)
   - Mark task 215 as COMPLETED
   - Add completion date and summary

2. **Implementation Summary**
   - Location: `specs/215_fix_todo_command_task_block_removal/summaries/implementation-summary-{date}.md`
   - Content: Summary of specification changes

### Research Artifacts (Already Complete)

1. **Research Report**
   - Location: `specs/215_fix_todo_command_task_block_removal/reports/research-001.md`
   - Status: Complete

2. **Research Summary**
   - Location: `specs/215_fix_todo_command_task_block_removal/summaries/research-summary.md`
   - Status: Complete

---

## Rollback and Contingency

### Rollback Plan

If specification changes cause issues:

**Step 1: Identify Issue**
- Determine which section is problematic
- Document the specific ambiguity or error

**Step 2: Revert Changes**
- Use git to revert to pre-update state
- Command: `git checkout HEAD -- .opencode/command/todo.md`

**Step 3: Restore Original State**
- Restore original Stage 4 specification
- Ensure no partial changes remain

**Step 4: Document Issue**
- Update task 215 with issue details
- Document what went wrong and why

### Contingency Plans

**Contingency 1: Specification Still Ambiguous**

If AI agent still misinterprets specification:

**Alternative Approach**:
- Add more concrete examples
- Use step-by-step algorithm format
- Add pseudocode for boundary detection
- Provide negative examples (what NOT to do)

**Contingency 2: Edge Cases Missed**

If additional edge cases discovered:

**Mitigation**:
- Add new test cases to test_cases section
- Update boundary detection with new patterns
- Document edge case handling explicitly

**Contingency 3: Breaking Changes Detected**

If changes break existing functionality:

**Mitigation**:
- Isolate breaking change
- Revert specific section
- Find alternative specification approach
- Add compatibility notes

### Success Criteria for Rollback Decision

Rollback if:
- Specification creates ambiguity or confusion
- Implementation based on spec fails multiple test cases
- Breaking changes to other stages detected
- Critical functionality lost

Do NOT rollback if:
- Minor wording improvements needed
- Additional examples would help
- Edge cases need clarification
- Documentation updates needed

---

## Dependencies and Prerequisites

### Internal Dependencies

1. **status-markers.md** (SATISFIED)
   - Status marker definitions exist
   - [COMPLETED] and [ABANDONED] statuses defined
   - Status: Complete and correct

2. **TODO.md Format** (SATISFIED)
   - Task heading format: ### NNN. Title
   - Section heading format: ## Section
   - Separator format: ---
   - Status: Stable and documented

3. **Existing Stage 4** (SATISFIED)
   - Current Stage 4 specification exists
   - Process steps defined
   - Status: Functional but incomplete

### External Dependencies

None. All dependencies are internal to the project.

### Blocking Issues

None. All prerequisites are satisfied.

---

## Success Metrics

### Quantitative Metrics

1. **Specification Completeness**: 100% (all sections added)
2. **Test Case Coverage**: 7 test cases (all edge cases covered)
3. **Lines Added**: ~250 lines of specification
4. **Regex Patterns**: 4 patterns (heading, section, separator, metadata)
5. **Examples**: 10+ examples (task blocks, boundaries, validation)

### Qualitative Metrics

1. **Clarity**: Specification is clear and unambiguous
2. **Implementability**: Specification can be implemented without questions
3. **Completeness**: All edge cases and error conditions covered
4. **Maintainability**: Specification is well-organized and documented

### Acceptance Criteria

**Must Have**:
- [ ] Task block structure defined
- [ ] Boundary detection specified
- [ ] Atomic removal specified
- [ ] Validation specified
- [ ] 7 test cases documented

**Should Have**:
- [ ] Concrete examples for all concepts
- [ ] Regex patterns for all boundaries
- [ ] Error handling specified
- [ ] Edge cases documented

**Nice to Have**:
- [ ] Pseudocode for algorithms
- [ ] Negative examples (what NOT to do)
- [ ] Additional test cases beyond 7

---

## Timeline and Milestones

### Estimated Timeline

**Total Effort**: 2.5 hours

**Phase Breakdown**:
- Phase 1: Add Task Block Structure Definition - 0.5 hours
- Phase 2: Add Block Boundary Detection Specification - 0.5 hours
- Phase 3: Update Process Steps for Atomic Removal - 0.5 hours
- Phase 4: Add Post-Removal Validation Specification - 0.5 hours
- Phase 5: Add Test Cases and Documentation - 0.5 hours

### Milestones

**Milestone 1: Task Block Structure Defined** (0.5 hours)
- task_block_structure section added
- Heading and body patterns specified
- Examples provided

**Milestone 2: Boundary Detection Specified** (1 hour cumulative)
- block_boundary_detection section added
- 4 boundary patterns documented
- 4 examples provided

**Milestone 3: Process Steps Updated** (1.5 hours cumulative)
- Process section updated with atomic removal
- References to new sections added
- Validation step added

**Milestone 4: Validation Specified** (2 hours cumulative)
- post_removal_validation section added
- Orphaned content detection specified
- Error handling documented

**Milestone 5: Test Cases Documented** (2.5 hours cumulative)
- 7 test cases added
- Validation section updated
- Documentation complete

---

## Notes and Assumptions

### Assumptions

1. **TODO.md Format Stable**: Task heading format (### NNN.) will not change
2. **Status Markers Stable**: [COMPLETED] and [ABANDONED] markers will not change
3. **AI Agent Capability**: AI agent can implement regex-based boundary detection
4. **No Breaking Changes**: Specification changes won't break existing workflows

### Known Limitations

1. **Specification Only**: This plan only updates specification, not implementation
2. **No Code Changes**: No actual code or script changes included
3. **Manual Testing Required**: Test cases must be manually executed after implementation
4. **No Automated Validation**: Post-removal validation must be implemented separately

### Future Work

1. **Automated Testing**: Create automated tests for /todo command
2. **Validation Tool**: Create standalone tool to validate TODO.md structure
3. **Linting**: Add linter to detect orphaned content in TODO.md
4. **Documentation**: Add /todo command usage guide with examples

### References

1. **Task 215 Research Report**: `specs/215_fix_todo_command_task_block_removal/reports/research-001.md`
2. **Task 215 Research Summary**: `specs/215_fix_todo_command_task_block_removal/summaries/research-summary.md`
3. **Current todo.md**: `.opencode/command/todo.md`
4. **status-markers.md**: `.opencode/context/core/standards/status-markers.md`

---

**Plan Status**: [NOT STARTED]  
**Next Action**: Begin Phase 1 - Add Task Block Structure Definition  
**Estimated Completion**: 2.5 hours from start
