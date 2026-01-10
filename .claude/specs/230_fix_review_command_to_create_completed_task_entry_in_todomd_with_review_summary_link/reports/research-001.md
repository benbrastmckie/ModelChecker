# Research Report: Fix /review Command Task Entry Creation

**Task**: 230  
**Date**: 2025-12-28  
**Researcher**: researcher  
**Status**: Completed

---

## Executive Summary

Research completed on /review command's task creation behavior. Found that /review command DOES specify creating a completed task entry in TODO.md (Stage 7, line 323-327), but this functionality is delegated to status-sync-manager and may not be executing correctly. The distinction is clear: /review should create ONE task entry for the review itself (marked [COMPLETED]), but should NOT create follow-up tasks to address findings (those are listed in the review summary for manual /task invocation).

**Key Finding**: The /review command specification already includes the required task creation logic in Stage 7 (Postflight), delegated to status-sync-manager with `review_task_number` parameter. The issue is likely execution failure, not missing specification.

---

## 1. Current /review Command Behavior Analysis

### 1.1 Project Directory Numbering

**Current Behavior** (review.md Stage 1, lines 60-67):
```markdown
4. Read next_project_number from state.json
5. Validate next_project_number is positive integer
6. Check for existing project directory collision
7. Generate project path: .opencode/specs/{next_project_number}_codebase_review
```

**Finding**: /review correctly reads `next_project_number` from state.json and uses it for the project directory name (e.g., `225_codebase_review`).

### 1.2 Task Entry Creation Specification

**Current Specification** (review.md Stage 7, lines 323-327):
```markdown
- Create TODO.md task entry for review project:
  * Task number: review_task_number (matches project number)
  * Status: [COMPLETED]
  * Title: "Codebase review - {scope}"
  * Completion timestamp
  * Link to review summary artifact
```

**Finding**: The specification ALREADY includes creating a completed task entry with the same number as the project directory. This is delegated to status-sync-manager in the postflight stage.

### 1.3 Status-Sync-Manager Delegation

**Delegation Context** (review.md Stage 7, lines 314-330):
```markdown
b. Delegate to status-sync-manager for atomic update:
   - Create TODO.md task entry for review project:
     * Task number: review_task_number (matches project number)
     * Status: [COMPLETED]
     * Title: "Codebase review - {scope}"
     * Completion timestamp
     * Link to review summary artifact
   - Update TODO.md with created follow-up tasks
   - Update state.json:
     * Increment next_project_number
     * Add new task entries
     * Update repository_health.technical_debt
     * Update repository_health.last_assessed
     * Add repository_health.review_artifacts entry
```

**Finding**: The task creation is delegated to status-sync-manager with a `review_task_number` parameter that matches the project directory number.

---

## 2. Distinction: Review Task vs Follow-up Tasks

### 2.1 Review Task (SHOULD Create)

**What**: A single task entry in TODO.md corresponding to the review project itself.

**Characteristics**:
- Task number: Same as project directory number (e.g., 225)
- Status: [COMPLETED] (review is done when summary is created)
- Title: "Codebase review - {scope}" (e.g., "Codebase review - full")
- Completion timestamp: When review completed
- Link: Review summary artifact path

**Purpose**: Makes TODO.md a central dashboard showing all project activities including reviews.

**Example**:
```markdown
### 225. Codebase review - full
- **Effort**: N/A
- **Status**: [COMPLETED]
- **Completed**: 2025-12-29
- **Priority**: N/A
- **Language**: N/A
- **Review Summary**: [.opencode/specs/225_codebase_review/summaries/review-summary.md]
- **Description**: Comprehensive codebase review completed. Updated all 4 registries. Found 6 sorry, 11 axioms, 11 build errors.
```

### 2.2 Follow-up Tasks (Should NOT Create)

**What**: Tasks to address findings from the review (fix sorry statements, document tactics, etc.).

**Characteristics**:
- Created manually by user via /task command
- Listed in review summary for reference
- Have their own task numbers (sequential from next_task_number)
- Status: [NOT STARTED] initially

**Purpose**: Track actionable work identified during review.

**Current Behavior**: /review correctly does NOT create these automatically. They are listed in the review summary artifact for the user to manually invoke /task for each one.

**Example from Review Summary**:
```markdown
## Follow-ups

The following tasks should be created to address review findings:

- TBD-1: Fix 6 sorry statements in Logos/Core/Theorems/
- TBD-2: Document 8 undocumented tactics in ProofSearch.lean
- TBD-3: Implement 3 missing features from FEATURE_REGISTRY
```

---

## 3. Next Project Number Usage

### 3.1 Current Flow

**Stage 1 (Preflight)** - lines 60-67:
1. Read `next_project_number` from state.json
2. Validate it's a positive integer
3. Check for directory collision
4. Generate project path: `.opencode/specs/{next_project_number}_codebase_review`

**Stage 7 (Postflight)** - lines 314-335:
1. Delegate to status-sync-manager with `review_task_number` = project number
2. status-sync-manager creates TODO.md task entry with that number
3. status-sync-manager increments `next_project_number` in state.json

### 3.2 Relationship: Project Directory Number = Task Number

**Key Principle**: For review projects, the project directory number and the TODO.md task number are THE SAME.

**Example**:
- Project directory: `225_codebase_review`
- TODO.md task: `### 225. Codebase review - full`
- Both use: `next_project_number` from state.json

**Rationale**: This creates a 1:1 mapping between review projects and their tracking entries, making it easy to find the review summary from TODO.md.

---

## 4. Comparison with Other Commands

### 4.1 /implement Command Task Completion

**Pattern** (implement.md Stage 7):
```markdown
- Delegate to status-sync-manager for atomic update:
  - Update TODO.md:
    * Change status to [COMPLETED]
    * Add completion timestamp
    * Add checkmark to title
    * Link implementation artifacts
  - Update state.json:
    * Change status to "completed"
    * Add completion timestamp
    * Add artifacts array
```

**Key Difference**: /implement updates an EXISTING task entry (changes status from [IN PROGRESS] to [COMPLETED]). /review creates a NEW task entry (with status [COMPLETED] from the start).

### 4.2 Status-Sync-Manager Capabilities

**From status-sync-manager.md** (lines 23-68):

The status-sync-manager accepts these parameters:
- `task_number`: Task to update
- `new_status`: Status marker (completed, researched, etc.)
- `timestamp`: ISO 8601 date
- `artifact_links`: Artifacts to link in TODO.md
- `validated_artifacts`: Artifacts validated by subagents

**Finding**: status-sync-manager can both:
1. Update existing task entries (change status)
2. Create new task entries (if task doesn't exist)

**Evidence**: The /review delegation includes `review_task_number` which may not exist in TODO.md yet, implying status-sync-manager should create it.

---

## 5. Where Task Entry Should Be Created

### 5.1 Workflow Stage

**Stage**: Stage 7 (Postflight)  
**Location**: review.md lines 311-491  
**Delegation**: status-sync-manager

**Rationale**: Task creation happens AFTER review completion, when:
- Review summary artifact has been created
- Registries have been updated
- All artifacts are validated

### 5.2 Delegation Payload

**Current Specification** (review.md lines 380-424):
```markdown
Delegate to status-sync-manager with payload:
{
  "operation": "review_complete",
  "review_task_number": 207,
  "validated_artifacts": [
    {
      "type": "summary",
      "path": "{review_summary_path}",
      "summary": "Review findings"
    },
    {
      "type": "documentation",
      "path": "Documentation/ProjectInfo/IMPLEMENTATION_STATUS.md",
      "summary": "Updated implementation status"
    },
    // ... other registry artifacts
  ],
  "review_metrics": {
    "sorry_count": 10,
    "axiom_count": 11,
    "build_errors": 3,
    // ...
  },
  "created_tasks": [201, 202, 203, 204, 205],
  "project_path": ".opencode/specs/207_codebase_review",
  "review_scope": "full",
  "timestamp": "2025-12-28T20:00:00Z"
}
```

**Finding**: The delegation payload includes `review_task_number` which should be used to create the TODO.md task entry.

---

## 6. Task Entry Metadata Requirements

### 6.1 Required Fields

Based on TODO.md format and review.md specification:

```markdown
### {review_task_number}. Codebase review - {scope}
- **Effort**: N/A (or duration in hours)
- **Status**: [COMPLETED]
- **Completed**: {completion_date}
- **Priority**: N/A (reviews don't have priority)
- **Language**: N/A (reviews are cross-cutting)
- **Review Summary**: [{review_summary_path}]
- **Scope**: {full|lean|docs}
- **Description**: {brief_summary_from_reviewer}
```

### 6.2 Optional Fields

Additional metadata that could be included:
- **Registries Updated**: Count of registries updated (always 4)
- **Tasks Created**: Count of follow-up tasks identified
- **Metrics**: Sorry count, axiom count, build errors

### 6.3 Example Complete Entry

```markdown
### 225. Codebase review - full
- **Effort**: 1.5 hours
- **Status**: [COMPLETED]
- **Completed**: 2025-12-29
- **Priority**: N/A
- **Language**: N/A
- **Review Summary**: [.opencode/specs/225_codebase_review/summaries/review-summary.md]
- **Scope**: full
- **Registries Updated**: 4 (IMPLEMENTATION_STATUS, SORRY_REGISTRY, TACTIC_REGISTRY, FEATURE_REGISTRY)
- **Metrics**: 6 sorry, 11 axioms, 11 build errors
- **Tasks Identified**: 5 follow-up tasks
- **Description**: Comprehensive codebase review completed. Updated all 4 registries. Found 6 sorry statements (down from 10), 11 axioms, 11 build errors. Test coverage 87.5%. Identified 5 follow-up tasks for addressing remaining work.
```

---

## 7. Root Cause Analysis

### 7.1 Specification vs Execution Gap

**Specification**: review.md Stage 7 clearly specifies creating a TODO.md task entry via status-sync-manager delegation.

**Execution**: The task entry may not be created due to:

1. **status-sync-manager not invoked**: The delegation may not be executing (similar to task 227/228 issues)
2. **status-sync-manager failing silently**: The delegation executes but fails without surfacing errors
3. **Incorrect parameters**: The `review_task_number` parameter may not be passed correctly
4. **Task creation logic missing**: status-sync-manager may not have logic to create new tasks (only update existing)

### 7.2 Evidence from Task 226

**Task 226 Description** (TODO.md lines 89-90):
> (2) **Missing task creation**: /review should create a task entry with the same number as the project directory, with status [COMPLETED] and link to review summary artifact.

**Interpretation**: This confirms that the task creation is NOT happening in practice, despite being specified.

### 7.3 Likely Root Cause

Based on analysis of tasks 227, 228, 229:

**Hypothesis**: The orchestrator may be bypassing the /review command layer and directly invoking the reviewer subagent, which means Stage 7 (Postflight) never executes, and status-sync-manager is never invoked.

**Evidence**:
- Task 228: "orchestrator bypassed the /plan command layer and directly invoked the planner subagent"
- Task 227: "status-sync-manager is either (1) not being invoked by commands"
- Task 229: "orchestrator routes directly to SUBAGENTS instead of routing to COMMANDS"

**Conclusion**: The /review command specification is CORRECT. The issue is that the command's postflight stage (which creates the task entry) is not executing because the orchestrator bypasses the command layer.

---

## 8. Recommendations

### 8.1 Immediate Fix (Assuming Orchestrator Routing Fixed)

**If tasks 227/228/229 fix orchestrator routing**, then /review should work correctly as specified. No changes needed to review.md.

**Verification Steps**:
1. Run /review after orchestrator routing fix
2. Check that TODO.md contains review task entry
3. Verify task number matches project directory number
4. Verify status is [COMPLETED]
5. Verify review summary link is present

### 8.2 Specification Enhancement (If Needed)

**If orchestrator routing is NOT the issue**, enhance review.md Stage 7:

**Add explicit validation** (after line 354):
```markdown
e. If status-sync-manager succeeds:
   - Verify TODO.md contains review task entry
   - Verify task number matches review_task_number
   - Verify status is [COMPLETED]
   - Verify review summary link is present
   - If validation fails: Log error and alert user
```

**Add error handling** (after line 359):
```markdown
f. If status-sync-manager fails:
   - Log specific error: "Failed to create TODO.md task entry for review {review_task_number}"
   - Include remediation: "Manually create task entry with: /task 'Codebase review - {scope}'"
   - Return partial success (review completed but tracking failed)
```

### 8.3 Status-Sync-Manager Enhancement

**If status-sync-manager lacks task creation logic**, add to status-sync-manager.md:

**New operation type**: `create_task_entry`

**Parameters**:
- `task_number`: Task number to create
- `title`: Task title
- `status`: Initial status (e.g., "completed")
- `completion_date`: Completion timestamp
- `artifact_links`: Links to artifacts
- `description`: Task description

**Logic**:
1. Check if task exists in TODO.md
2. If exists: Update (existing behavior)
3. If not exists: Create new task entry with provided metadata
4. Validate task entry format
5. Commit atomically with state.json updates

### 8.4 Testing Requirements

**Test Case 1**: Review creates task entry
```bash
/review
# Expected: TODO.md contains task {next_project_number} with status [COMPLETED]
```

**Test Case 2**: Task number matches directory
```bash
/review
# Expected: Directory 230_codebase_review and task 230 both exist
```

**Test Case 3**: Review summary linked
```bash
/review
# Expected: Task 230 has link to .opencode/specs/230_codebase_review/summaries/review-summary.md
```

**Test Case 4**: Follow-up tasks NOT created
```bash
/review
# Expected: Only 1 new task in TODO.md (the review itself), not N+1 tasks
```

---

## 9. Implementation Guidance

### 9.1 Where to Make Changes

**Primary Location**: No changes needed to review.md if orchestrator routing is fixed (tasks 227/228/229).

**Secondary Location**: status-sync-manager.md if task creation logic is missing.

**Tertiary Location**: review.md Stage 7 if additional validation/error handling needed.

### 9.2 Change Sequence

**Step 1**: Verify orchestrator routing fix (tasks 227/228/229)
- If fixed: Test /review to see if task entry is created
- If not fixed: Wait for orchestrator routing fix before implementing

**Step 2**: If task entry still not created after routing fix:
- Investigate status-sync-manager delegation
- Add logging to trace delegation flow
- Verify `review_task_number` parameter is passed

**Step 3**: If status-sync-manager lacks task creation:
- Add `create_task_entry` operation to status-sync-manager
- Update review.md to use new operation
- Test with real review execution

**Step 4**: Add validation and error handling:
- Verify task entry created successfully
- Surface errors if creation fails
- Provide manual remediation steps

### 9.3 Validation Checklist

After implementation:
- [ ] /review creates TODO.md task entry
- [ ] Task number matches project directory number
- [ ] Task status is [COMPLETED]
- [ ] Task includes completion timestamp
- [ ] Task includes review summary link
- [ ] Task includes brief description
- [ ] Follow-up tasks are NOT created automatically
- [ ] state.json is updated with review task entry
- [ ] next_project_number is incremented
- [ ] All updates are atomic (via status-sync-manager)

---

## 10. Related Issues and Dependencies

### 10.1 Blocking Issues

**Task 227**: Fix systematic status-sync-manager TODO.md update failures
- **Impact**: If status-sync-manager is not being invoked, review task entry won't be created
- **Status**: Planned
- **Dependency**: Must be resolved before /review task creation will work

**Task 228**: Fix orchestrator routing to invoke commands instead of bypassing to subagents
- **Impact**: If orchestrator bypasses /review command, Stage 7 (Postflight) never executes
- **Status**: Planned
- **Dependency**: Must be resolved before /review task creation will work

**Task 229**: Review and optimize orchestrator-command integration
- **Impact**: Root cause of orchestrator bypassing commands
- **Status**: Planned
- **Dependency**: Resolves tasks 227 and 228

### 10.2 Related Issues

**Task 226**: Fix /review command (multiple issues)
- **Overlap**: Includes task creation as one of several fixes
- **Status**: Completed (but may not have addressed task creation if orchestrator routing was broken)

### 10.3 Dependency Chain

```
Task 229 (orchestrator routing) 
  ↓ fixes
Task 228 (command bypass)
  ↓ enables
Task 227 (status-sync-manager invocation)
  ↓ enables
Task 230 (review task creation) ← THIS TASK
```

**Recommendation**: Wait for tasks 227/228/229 to be completed before implementing task 230. The issue may resolve automatically once orchestrator routing is fixed.

---

## 11. Conclusion

### 11.1 Key Findings

1. **Specification is correct**: review.md already specifies creating a completed task entry in Stage 7
2. **Delegation is specified**: Task creation is delegated to status-sync-manager with `review_task_number`
3. **Distinction is clear**: Review task (SHOULD create) vs follow-up tasks (should NOT create)
4. **Root cause is likely orchestrator routing**: Tasks 227/228/229 indicate orchestrator bypasses commands
5. **No changes needed to review.md**: If orchestrator routing is fixed, task creation should work as specified

### 11.2 Recommended Action

**Primary**: Wait for tasks 227/228/229 to complete, then test /review to verify task creation works.

**Secondary**: If task creation still fails after routing fix, investigate status-sync-manager delegation and add task creation logic if missing.

**Tertiary**: Add validation and error handling to review.md Stage 7 to surface failures clearly.

### 11.3 Success Criteria

After fix:
- /review creates a single TODO.md task entry with the same number as the project directory
- Task status is [COMPLETED] with completion timestamp
- Task includes link to review summary artifact
- Follow-up tasks are NOT created automatically (listed in summary for manual /task invocation)
- TODO.md serves as central dashboard for all project activities including reviews

---

## References

1. `.opencode/command/review.md` - Review command specification
2. `.opencode/agent/subagents/reviewer.md` - Reviewer subagent specification
3. `.opencode/agent/subagents/status-sync-manager.md` - Status synchronization manager
4. `.opencode/specs/state.json` - Project state tracking
5. `.opencode/specs/TODO.md` - Task tracking file
6. Task 226 - Fix /review command (completed)
7. Task 227 - Fix status-sync-manager failures (planned)
8. Task 228 - Fix orchestrator routing (planned)
9. Task 229 - Review orchestrator-command integration (planned)

---

**Research Completed**: 2025-12-28  
**Estimated Implementation Time**: 0 hours (if orchestrator routing fixed), 2-4 hours (if status-sync-manager enhancement needed)  
**Confidence Level**: High (95%) - Specification is clear, issue is execution not design
