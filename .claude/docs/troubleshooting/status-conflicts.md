# Status Conflicts and Recovery Procedures

This document provides troubleshooting guidance for workflow status conflicts and edge cases.

## Table of Contents

1. [Concurrent Execution](#concurrent-execution)
2. [Stale In-Progress Status](#stale-in-progress-status)
3. [Invalid Status Transitions](#invalid-status-transitions)
4. [Rollback Failures](#rollback-failures)
5. [Timeout Recovery](#timeout-recovery)

---

## Edge Case 1: Concurrent Execution {#concurrent-execution}

### Symptoms

- Two users (or sessions) run the same workflow command on the same task simultaneously
- Error message: "Task X is already being [researched|planned|implemented]"
- Race condition warnings in logs

### Root Cause

Multiple processes attempting to update task status at the same time. The first process successfully updates status to in-progress marker (e.g., `[RESEARCHING]`), and the second process detects this and aborts.

### Manual Recovery Steps

1. **Identify which process is active:**
   ```bash
   # Check for recent status updates in state.json
   jq -r --arg num "TASK_NUMBER" '.active_projects[] | select(.project_number == ($num | tonumber)) | .last_updated' .claude/specs/state.json
   ```

2. **Wait for active process to complete:**
   - If timestamp is recent (<1 hour): Wait for process to finish
   - If timestamp is old (>1 hour): Likely stale status, proceed to recovery

3. **If stale status detected:**
   ```bash
   # Use /task --sync to reset status
   /task --sync TASK_NUMBER
   ```

4. **Re-run command after status reset:**
   ```bash
   /research TASK_NUMBER  # or /plan, /implement, /revise
   ```

### Prevention Tips

- **Single-user environment**: Avoid running multiple workflow commands on same task
- **Multi-user environment**: Coordinate task assignments to prevent overlap
- **CI/CD pipelines**: Use task locking mechanisms or sequential execution
- **Check status first**: Run `/task TASK_NUMBER` to check current status before starting work

---

## Edge Case 2: Stale In-Progress Status {#stale-in-progress-status}

### Symptoms

- Task status stuck at `[RESEARCHING]`, `[PLANNING]`, `[REVISING]`, or `[IMPLEMENTING]`
- No active process running for this task
- Error message: "Task X is already being [researched|planned|implemented]"
- Timestamp in state.json is old (>1 hour or >24 hours)

### Root Cause

Workflow command crashed, timed out, or was interrupted before completing postflight stage. Status was updated to in-progress marker in preflight but never updated to completion marker in postflight.

### Manual Recovery Steps

1. **Verify no active process:**
   ```bash
   # Check system processes (if applicable)
   ps aux | grep -i "research\|plan\|implement"
   
   # Check timestamp in state.json
   jq -r --arg num "TASK_NUMBER" '.active_projects[] | select(.project_number == ($num | tonumber)) | .last_updated' .claude/specs/state.json
   ```

2. **Check for partial artifacts:**
   ```bash
   # List artifacts in task directory
   ls -la .claude/specs/TASK_NUMBER_*/
   
   # Check for incomplete reports/plans/summaries
   find .claude/specs/TASK_NUMBER_*/ -type f -name "*.md"
   ```

3. **Determine recovery strategy:**
   
   **Option A: Resume work (if artifacts exist and are usable)**
   ```bash
   # Manually reset status to allow resumption
   /task --sync TASK_NUMBER
   
   # Re-run command (will resume from partial state if supported)
   /implement TASK_NUMBER --resume  # for implementation
   # or
   /research TASK_NUMBER  # will create new research report
   ```
   
   **Option B: Reset and start fresh (if artifacts are incomplete/corrupt)**
   ```bash
   # Use /task --sync to reset status
   /task --sync TASK_NUMBER
   
   # Remove partial artifacts if needed
   rm -rf .claude/specs/TASK_NUMBER_*/reports/research-*.md  # example
   
   # Re-run command from scratch
   /research TASK_NUMBER
   ```

4. **Verify status reset:**
   ```bash
   # Check status in TODO.md
   grep -A 5 "^### TASK_NUMBER\." .claude/specs/TODO.md
   
   # Check status in state.json
   jq -r --arg num "TASK_NUMBER" '.active_projects[] | select(.project_number == ($num | tonumber)) | .status' .claude/specs/state.json
   ```

### Prevention Tips

- **Monitor long-running commands**: Set realistic timeouts for workflow commands
- **Use /task --sync regularly**: Periodically check for and fix stale statuses
- **Graceful interruption**: If you need to cancel a command, use Ctrl+C and then run `/task --sync` to reset status
- **Automated cleanup**: Consider running `/task --sync` daily to detect stale statuses

---

## Edge Case 3: Invalid Status Transitions {#invalid-status-transitions}

### Symptoms

- Attempting to run workflow command on task with unexpected status
- Example: Running `/research` on task with status `[RESEARCHED]`
- Error message: "Task X already researched. Use /plan to continue workflow"

### Root Cause

User attempting to re-run a workflow stage that has already completed, or attempting to skip required stages in the workflow.

### Manual Recovery Steps

1. **Understand the workflow sequence:**
   ```
   [NOT STARTED] → /research → [RESEARCHED]
                              ↓
                         /plan → [PLANNED]
                              ↓
                         /implement → [COMPLETED]
   
   Plan revision branch:
   [PLANNED] → /revise → [REVISED] → /implement → [COMPLETED]
   ```

2. **Check current task status:**
   ```bash
   /task TASK_NUMBER
   ```

3. **Determine appropriate next step:**
   
   - **If status is `[RESEARCHED]`**: Use `/plan TASK_NUMBER` to continue
   - **If status is `[PLANNED]`**: Use `/implement TASK_NUMBER` to continue
   - **If status is `[REVISED]`**: Use `/implement TASK_NUMBER` to continue
   - **If status is `[COMPLETED]`**: Task is done, no further action needed
   - **If status is `[BLOCKED]`**: Resolve blocker first, then continue

4. **If you need to re-run a completed stage:**
   
   **Option A: Use --force flag (advanced users only)**
   ```bash
   /research TASK_NUMBER --force  # Override status validation
   ```
   
   **Option B: Reset status manually**
   ```bash
   # Use /task --sync to reset to earlier status
   /task --sync TASK_NUMBER
   
   # Re-run workflow from beginning
   /research TASK_NUMBER
   ```

### Prevention Tips

- **Follow workflow sequence**: Always follow the standard workflow sequence
- **Check status first**: Run `/task TASK_NUMBER` to check current status before running commands
- **Use /revise for plan updates**: Don't re-run `/plan`, use `/revise` instead
- **Understand status markers**: Familiarize yourself with status lifecycle (see `.claude/context/core/workflows/status-transitions.md`)

---

## Edge Case 4: Rollback Failures {#rollback-failures}

### Symptoms

- status-sync-manager reports rollback failure
- Files in inconsistent state (TODO.md updated but state.json not, or vice versa)
- Error message: "Rollback failed: unable to restore previous state"

### Root Cause

Two-phase commit rollback failed due to file system issues, permission errors, or disk space problems. This is rare but can happen if files are locked or disk is full.

### Manual Recovery Steps

1. **Identify which files are inconsistent:**
   ```bash
   # Check TODO.md status
   grep -A 5 "^### TASK_NUMBER\." .claude/specs/TODO.md | grep -E "\[(RESEARCHING|PLANNING|IMPLEMENTING|RESEARCHED|PLANNED|COMPLETED)\]"
   
   # Check state.json status
   jq -r --arg num "TASK_NUMBER" '.active_projects[] | select(.project_number == ($num | tonumber)) | .status' .claude/specs/state.json
   ```

2. **Determine correct status:**
   - Check git history to see last known good state:
     ```bash
     git log --oneline -10 -- .claude/specs/TODO.md .claude/specs/state.json
     git show HEAD:.claude/specs/TODO.md | grep -A 5 "^### TASK_NUMBER\."
     ```
   
   - Check for artifacts to determine actual completion state:
     ```bash
     ls -la .claude/specs/TASK_NUMBER_*/
     ```

3. **Manually synchronize files:**
   
   **Option A: Use /task --sync command (recommended)**
   ```bash
   /task --sync TASK_NUMBER  # Detects and fixes inconsistencies
   ```
   
   **Option B: Manual git revert (if /task --sync fails)**
   ```bash
   # Revert to last known good state
   git checkout HEAD -- .claude/specs/TODO.md .claude/specs/state.json
   
   # Re-run workflow command
   /research TASK_NUMBER  # or appropriate command
   ```
   
   **Option C: Manual file editing (last resort)**
   ```bash
   # Edit TODO.md to match state.json
   vim .claude/specs/TODO.md
   # Find task entry and update status marker
   
   # Or edit state.json to match TODO.md
   vim .claude/specs/state.json
   # Update "status" field for task
   
   # Verify consistency
   /task --sync TASK_NUMBER
   ```

4. **Verify synchronization:**
   ```bash
   # Check both files have same status
   grep -A 5 "^### TASK_NUMBER\." .claude/specs/TODO.md
   jq -r --arg num "TASK_NUMBER" '.active_projects[] | select(.project_number == ($num | tonumber))' .claude/specs/state.json
   ```

### Prevention Tips

- **Monitor disk space**: Ensure adequate disk space before running workflow commands
- **Check file permissions**: Verify write permissions on .claude/specs/ directory
- **Avoid manual edits**: Don't manually edit TODO.md or state.json while commands are running
- **Use /task --sync regularly**: Run `/task --sync` to detect and fix inconsistencies early

---

## Edge Case 5: Timeout Recovery {#timeout-recovery}

### Symptoms

- Workflow command times out (e.g., after 30 minutes for /plan, 2 hours for /implement)
- Error message: "Command timed out after Xs"
- Task status stuck at in-progress marker (`[RESEARCHING]`, `[PLANNING]`, `[IMPLEMENTING]`)
- Partial artifacts may exist

### Root Cause

Command execution exceeded configured timeout. This can happen for complex tasks, slow systems, or when external tools (e.g., Lean compiler) take longer than expected.

### Manual Recovery Steps

1. **Check for partial artifacts:**
   ```bash
   # List all artifacts in task directory
   find .claude/specs/TASK_NUMBER_*/ -type f -name "*.md"
   
   # Check file sizes and timestamps
   ls -lh .claude/specs/TASK_NUMBER_*/
   ```

2. **Determine if work is salvageable:**
   
   **If partial artifacts are usable:**
   ```bash
   # For /implement with --resume support
   /task --sync TASK_NUMBER  # Reset status
   /implement TASK_NUMBER --resume  # Resume from last completed phase
   ```
   
   **If partial artifacts are incomplete:**
   ```bash
   # Reset status and start fresh
   /task --sync TASK_NUMBER
   
   # Remove incomplete artifacts
   rm -rf .claude/specs/TASK_NUMBER_*/reports/research-*.md  # example
   
   # Re-run command with increased timeout (if possible)
   /research TASK_NUMBER  # Will use default timeout
   ```

3. **For long-running tasks, consider breaking down:**
   ```bash
   # Instead of implementing entire task at once:
   /implement TASK_NUMBER "Focus on Phase 1 only"
   # Then manually update plan and continue with Phase 2
   /implement TASK_NUMBER "Focus on Phase 2 only"
   ```

4. **Verify status after recovery:**
   ```bash
   /task TASK_NUMBER
   ```

### Prevention Tips

- **Break down large tasks**: Split complex tasks into smaller subtasks
- **Increase timeouts**: Modify command timeout in command file if needed (requires admin access)
- **Use --resume flag**: For /implement, use --resume to continue from last completed phase
- **Monitor progress**: For long-running commands, check progress periodically
- **Optimize workflows**: Review and optimize slow operations (e.g., Lean compilation, large file operations)

---

## General Recovery Workflow

For any status conflict or edge case:

1. **Assess the situation:**
   - Check current status: `/task TASK_NUMBER`
   - Check timestamps: `jq -r '.active_projects[] | select(.project_number == TASK_NUMBER)' .claude/specs/state.json`
   - Check for artifacts: `ls -la .claude/specs/TASK_NUMBER_*/`

2. **Use /task --sync command (first line of defense):**
   ```bash
   /task --sync TASK_NUMBER  # Automated detection and repair
   ```

3. **If /task --sync doesn't resolve:**
   - Consult specific edge case section above
   - Follow manual recovery steps
   - Check git history for last known good state

4. **Verify resolution:**
   - Check status consistency: `/task TASK_NUMBER`
   - Verify artifacts exist and are valid
   - Re-run workflow command if needed

5. **Document the issue:**
   - If you encounter a new edge case not documented here, please add it
   - Include symptoms, root cause, and recovery steps

---

## Getting Help

If you encounter a status conflict not covered in this document:

1. **Check git history:**
   ```bash
   git log --oneline -20 -- .claude/specs/TODO.md .claude/specs/state.json
   ```

2. **Check for error logs:**
   ```bash
   # If error logging is implemented
   cat .claude/logs/errors.json
   ```

3. **Create a backup before manual intervention:**
   ```bash
   cp .claude/specs/TODO.md .claude/specs/TODO.md.backup
   cp .claude/specs/state.json .claude/specs/state.json.backup
   ```

4. **Document the new edge case:**
   - Add to this document
   - Include symptoms, root cause, recovery steps, prevention tips

---

## Related Documentation

- `.claude/context/core/system/state-management.md` - State management architecture
- `.claude/context/core/workflows/status-transitions.md` - Status lifecycle diagram
- `.claude/context/core/standards/status-markers.md` - Status marker definitions
- `.claude/agent/subagents/status-sync-manager.md` - Atomic synchronization implementation
