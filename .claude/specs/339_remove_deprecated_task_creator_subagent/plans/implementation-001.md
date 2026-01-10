# Implementation Plan: Remove Deprecated task-creator Subagent

- **Task**: 339 - Remove deprecated task-creator subagent
- **Status**: [NOT STARTED]
- **Effort**: 1 hour
- **Priority**: Medium
- **Dependencies**: Task 338 (must complete first)
- **Research Inputs**: task-creator.md deprecation notice (deprecated 2026-01-05)
- **Artifacts**: 
  - plans/implementation-001.md (this file)
- **Standards**:
  - .opencode/context/core/formats/plan-format.md
  - .opencode/context/core/standards/status-markers.md
- **Type**: general
- **Lean Intent**: false

## Overview

Remove deprecated task-creator.md subagent file after verifying no other commands depend on it. The task-creator was deprecated on 2026-01-05 with replacement being status-sync-manager (operation: create_task). Task 338 updates /task command to use status-sync-manager directly, making task-creator obsolete.

## Goals & Non-Goals

**Goals**:
- Verify no commands depend on task-creator
- Remove .opencode/agent/subagents/task-creator.md file
- Update documentation that references task-creator
- Clean up any related context files

**Non-Goals**:
- Updating /task command (done in task 338)
- Creating deprecation policy (separate task 341)
- Removing other deprecated agents (if any)

## Risks & Mitigations

| Risk | Mitigation |
|------|-----------|
| Other commands depend on task-creator | Grep all command files for "task-creator" before removal |
| Documentation references task-creator | Search all .md files for references and update |
| Breaking existing workflows | Verify task 338 completed successfully first |

## Implementation Phases

### Phase 1: Verify No Dependencies [NOT STARTED]
- **Goal:** Ensure no commands or agents depend on task-creator
- **Tasks:**
  - [ ] Grep all command files for "task-creator":
    * grep -r "task-creator" .opencode/command/
    * Verify only /task command references it (should be updated by task 338)
  - [ ] Grep all agent files for "task-creator":
    * grep -r "task-creator" .opencode/agent/
    * Verify no agents delegate to task-creator
  - [ ] Check context files for references:
    * grep -r "task-creator" .opencode/context/
    * Document any references found
  - [ ] Verify task 338 completed:
    * Check /task command no longer delegates to task-creator
    * Verify /task command uses status-sync-manager directly
- **Timing:** 15 minutes

### Phase 2: Update Documentation [NOT STARTED]
- **Goal:** Remove or update all documentation references to task-creator
- **Tasks:**
  - [ ] Search all .md files for "task-creator":
    * find .opencode -name "*.md" -exec grep -l "task-creator" {} \;
  - [ ] For each reference found:
    * If describing architecture: Update to mention status-sync-manager
    * If describing workflow: Update to show direct delegation
    * If historical: Add note "(deprecated 2026-01-05)"
  - [ ] Update AGENTS.md if it lists task-creator:
    * Remove from active agents list
    * Add to deprecated agents section (if exists)
- **Timing:** 20 minutes

### Phase 3: Remove task-creator.md [NOT STARTED]
- **Goal:** Delete the deprecated subagent file
- **Tasks:**
  - [ ] Verify task 338 completed successfully
  - [ ] Verify no dependencies found in Phase 1
  - [ ] Remove file:
    * rm .opencode/agent/subagents/task-creator.md
  - [ ] Verify removal:
    * Confirm file no longer exists
    * Test /task command still works
- **Timing:** 5 minutes

### Phase 4: Test and Validate [NOT STARTED]
- **Goal:** Verify system works without task-creator
- **Tasks:**
  - [ ] Test /task command:
    * /task "Test task after removal"
    * Verify task created successfully
    * Verify no errors about missing task-creator
  - [ ] Test all /task flags:
    * --divide, --recover, --sync, --abandon
    * Verify all work correctly
  - [ ] Check logs for any task-creator references:
    * Verify no errors or warnings about missing agent
- **Timing:** 20 minutes

## Testing & Validation

- [ ] No commands depend on task-creator
- [ ] No agents depend on task-creator
- [ ] Documentation updated or references removed
- [ ] task-creator.md file removed
- [ ] /task command works correctly after removal
- [ ] All /task flags work correctly
- [ ] No errors or warnings in logs

## Artifacts & Outputs

- Removed .opencode/agent/subagents/task-creator.md
- Updated documentation files (if any references found)
- Test results confirming system works without task-creator

## Rollback/Contingency

If removal causes issues:
- Restore task-creator.md from git
- Investigate which component still depends on it
- Update that component first
- Retry removal after dependencies resolved
