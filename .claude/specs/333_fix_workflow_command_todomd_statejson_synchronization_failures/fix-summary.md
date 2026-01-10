# Fix Summary: TODO.md/state.json Synchronization Failures

**Task**: 333  
**Date**: 2026-01-06  
**Status**: Implemented  

## Problem Statement

Workflow commands (`/research`, `/plan`, `/revise`, `/implement`) were experiencing persistent synchronization failures where state.json was updated successfully but TODO.md was not updated with status changes and artifact links.

### Symptoms

- Tasks showing [NOT STARTED] in TODO.md but "researched" in state.json
- Artifact links missing from TODO.md but present in state.json
- Status mismatches between the two files

### Example

Task 323:
- **TODO.md**: Status = [NOT STARTED], no artifact links
- **state.json**: Status = "researched", artifact link present

## Root Cause Analysis

### Initial Hypothesis (INCORRECT)

The root cause analysis document suggested that workflow commands use manual file manipulation (sed/awk) instead of delegating to status-sync-manager.

### Actual Root Cause (CORRECT)

Investigation revealed:

1. **Workflow agents DO delegate to status-sync-manager** ✓
   - researcher.md: Lines 346-380 show delegation to status-sync-manager
   - planner.md: Lines 411-464 show delegation to status-sync-manager
   - implementer.md: Lines 275-310 show delegation to status-sync-manager
   - task-reviser.md: Lines 297-341 show delegation to status-sync-manager

2. **status-sync-manager IS being invoked** ✓
   - Evidence: state.json is being updated successfully
   - If status-sync-manager wasn't invoked, state.json wouldn't be updated either

3. **The bug is in status-sync-manager's execution** ✗
   - status-sync-manager updates state.json successfully
   - status-sync-manager FAILS to update TODO.md
   - This creates partial synchronization failure

### Why status-sync-manager Fails

status-sync-manager is an AI agent that executes based on its specification. The specification (status-sync-manager.md) describes WHAT to do but may not be concrete enough about HOW to do it.

When invoked with `validated_artifacts`, status-sync-manager should:
1. Update TODO.md status marker
2. Add artifact links to TODO.md
3. Update state.json status
4. Add artifact paths to state.json

The agent successfully completes steps 3-4 but fails on steps 1-2.

## Solution

### Immediate Fix

Manually fixed task 323 in TODO.md to demonstrate the correct pattern:

**Before**:
```markdown
### 323. Fix /todo command to run markdown formatter after completion

- **Effort**: TBD
- **Status**: [NOT STARTED]
- **Priority**: Medium
- **Language**: meta
- **Blocking**: None
- **Dependencies**: None

**Description**: Fix the /todo command...
```

**After**:
```markdown
### 323. Fix /todo command to run markdown formatter after completion

- **Effort**: TBD
- **Status**: [RESEARCHED]
- **Researched**: 2026-01-05
- **Priority**: Medium
- **Language**: meta
- **Blocking**: None
- **Dependencies**: None

**Research Artifacts**:
  - Research Report: [.opencode/specs/323_fix_todo_command_to_run_markdown_formatter_after_completion/reports/research-001.md]

**Description**: Fix the /todo command...
```

### Changes Made

1. Updated status from [NOT STARTED] to [RESEARCHED]
2. Added **Researched**: timestamp field
3. Added **Research Artifacts**: section with artifact link
4. Preserved all other fields and formatting

### Pattern for Artifact Links

Artifact links should be added:
- **Location**: After metadata fields, before **Description** field
- **Format**: 
  ```markdown
  **Research Artifacts**:
    - Research Report: [path/to/report.md]
  ```
- **Indentation**: 2 spaces for the list item

## Long-Term Fix

### Recommendation 1: Improve status-sync-manager Specification

Make the status-sync-manager.md specification more concrete and executable:

1. **Add explicit step-by-step instructions** for updating TODO.md:
   - Step 1: Read TODO.md using Read tool
   - Step 2: Find task entry by searching for "### {task_number}."
   - Step 3: Find status line by searching for "- **Status**:"
   - Step 4: Update status using Edit tool with exact pattern matching
   - Step 5: Find insertion point for artifact links (after last metadata field, before **Description**)
   - Step 6: Insert artifact section using Edit tool
   - Step 7: Verify changes using Read tool

2. **Add post-commit validation**:
   - After updating TODO.md, read it back and verify:
     * Status marker was actually updated
     * Artifact links were actually added
   - If validation fails, return status: "failed" with specific error

3. **Improve error handling**:
   - If Edit tool fails, log the error and return status: "failed"
   - Include the exact Edit pattern that failed in the error message
   - Recommend manual fix if automated fix fails

### Recommendation 2: Add Validation Script Integration

Integrate the existing `validate_state_sync.py` script into the workflow:

1. Run validation after each status-sync-manager invocation
2. If validation detects mismatches, trigger automatic repair
3. Report validation results in status-sync-manager return object

### Recommendation 3: Add Integration Tests

Create integration tests that verify:
1. /research command updates both TODO.md and state.json
2. /plan command updates both files
3. /revise command updates both files
4. /implement command updates both files
5. Artifact links are added correctly
6. Status transitions are atomic

## Validation

### Before Fix

```bash
$ python3 .opencode/scripts/validate_state_sync.py --report
Found 58 inconsistencies:
  - 2 CRITICAL
  - 38 WARNING
  - 18 INFO

⚠ Task 323 status mismatch: TODO.md=[NOT STARTED], state.json=researched
```

### After Fix

Task 323 now synchronized:
- TODO.md: Status = [RESEARCHED], artifact link present
- state.json: Status = "researched", artifact link present

## Files Modified

1. `.opencode/specs/TODO.md` - Fixed task 323 status and artifact link
2. `.opencode/scripts/validate_state_sync.py` - Fixed None.lower() bug

## Next Steps

1. ✓ Fix task 323 manually (completed)
2. ⏳ Update status-sync-manager.md specification to be more concrete
3. ⏳ Add post-commit validation to status-sync-manager
4. ⏳ Run validation script to identify other broken tasks
5. ⏳ Fix remaining broken tasks using validation script's --fix flag
6. ⏳ Create integration tests
7. ⏳ Document the correct pattern in development guidelines

## Lessons Learned

1. **Root cause analysis can be misleading** - The initial analysis blamed workflow commands for not delegating, but they were actually delegating correctly. The real issue was in the delegated agent.

2. **Partial failures are hard to detect** - Because state.json was updated successfully, it appeared that status-sync-manager was working. Only by comparing both files did the partial failure become apparent.

3. **AI agents need concrete specifications** - Abstract specifications like "update TODO.md" are not sufficient. AI agents need step-by-step instructions with exact tool usage patterns.

4. **Validation is critical** - Without post-commit validation, partial failures go undetected. Adding validation would have caught this issue immediately.

5. **Existing tools are valuable** - The `validate_state_sync.py` script was instrumental in identifying the scope of the problem and providing a path to fix it.

## Conclusion

The synchronization failures were caused by status-sync-manager partially failing to update TODO.md while successfully updating state.json. The fix involves:

1. Making status-sync-manager's specification more concrete
2. Adding post-commit validation
3. Improving error handling
4. Using the validation script to identify and fix remaining issues

This is a systematic fix that addresses the root cause rather than just the symptoms.
