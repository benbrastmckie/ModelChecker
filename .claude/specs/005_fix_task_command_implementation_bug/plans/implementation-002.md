# Implementation Plan: Task #5

**Task**: Fix /task command implementation bug
**Version**: 002
**Created**: 2026-01-11
**Revision of**: implementation-001.md
**Reason**: Expand scope to align all three .claude/ agent systems (ModelChecker, Global config, and ProofChecker as reference)

## Revision Summary

The original plan (v001) focused only on verifying that the fix was already applied to ModelChecker. This revised plan expands the scope to:

1. Verify alignment across all three `.claude/` systems
2. Address task #11 from global config (same bug fix)
3. Ensure all systems match the ProofChecker reference implementation

### Previous Plan Status
- Phase 1: [NOT STARTED] - Was verification only
- Phase 2: [NOT STARTED] - Was documentation only

### Key Changes
1. **Expanded scope**: Now covers ModelChecker + Global config (task #11), using ProofChecker as reference
2. **Added alignment verification**: Compare all three task.md files for consistency
3. **Added cross-task coordination**: This task now subsumes global config task #11

## Overview

Research confirmed the security fix (restricted allowed-tools, CRITICAL section, FORBIDDEN ACTIONS) is applied in all three locations:

| Location | File | Status |
|----------|------|--------|
| ModelChecker | `.claude/commands/task.md` | Fix applied |
| ProofChecker | `.claude/commands/task.md` | Fix applied (reference) |
| Global config | `~/.config/.claude/commands/task.md` | Fix applied |

The implementation will verify complete alignment and document findings. No code changes are expected since all three already have the fix.

## Phases

### Phase 1: Verification of Security Fix Components

**Estimated effort**: 10 minutes
**Status**: [COMPLETED]

**Objectives**:
1. Verify all three systems have the three fix components
2. Document any differences between implementations

**Files to verify**:
- `/home/benjamin/Projects/ModelChecker/.claude/commands/task.md`
- `/home/benjamin/Projects/ProofChecker/.claude/commands/task.md`
- `/home/benjamin/.config/.claude/commands/task.md`

**Steps**:
1. Confirm `allowed-tools` restricts to `.claude/specs/*` paths in all three
2. Confirm CRITICAL section (lines 12-25) present in all three
3. Confirm Constraints section with HARD STOP and FORBIDDEN ACTIONS in all three
4. Document differences (e.g., jq detail level, zero-padding, timestamp fields)

**Verification**:
- Checklist of all three components verified in each location

---

### Phase 2: Document Alignment Status

**Estimated effort**: 10 minutes
**Status**: [COMPLETED]

**Objectives**:
1. Create alignment comparison table
2. Document intentional differences (local customizations vs bugs)

**Files to create**:
- `.claude/specs/005_fix_task_command_implementation_bug/summaries/alignment-comparison.md`

**Steps**:
1. Create table comparing all three task.md implementations
2. Categorize differences:
   - Security fix components (should be identical)
   - Local customizations (expected to differ)
3. Note that task #11 in global config is now satisfied

**Verification**:
- Alignment document created with clear comparison

---

### Phase 3: Completion and Cross-Task Update

**Estimated effort**: 5 minutes
**Status**: [NOT STARTED]

**Objectives**:
1. Mark ModelChecker task #5 as completed
2. Note relationship to global config task #11
3. Create implementation summary

**Files to update**:
- `.claude/specs/state.json`
- `.claude/specs/TODO.md`

**Files to create**:
- `.claude/specs/005_fix_task_command_implementation_bug/summaries/implementation-summary-20260111.md`

**Steps**:
1. Create implementation summary documenting:
   - All three systems verified to have the fix
   - Task #11 in global config can be marked complete
   - No code changes were needed
2. Update task #5 status to COMPLETED
3. Git commit with appropriate message

**Verification**:
- Summary file created
- Task status updated in both state.json and TODO.md
- Git commit successful

---

## Dependencies

- Global config task #11 shares the same fix - this task effectively verifies both
- ProofChecker serves as reference implementation (already fixed in commit 4bab1a4)

## Risks and Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Differences found between implementations | Low | Low | Document as intentional customizations |
| Missing fix component in one location | Medium | Very Low | Apply fix from reference |

## Success Criteria

- [ ] All three task.md files verified to have restricted allowed-tools
- [ ] All three task.md files verified to have CRITICAL section
- [ ] All three task.md files verified to have HARD STOP constraints
- [ ] Alignment document created
- [ ] Implementation summary created
- [ ] ModelChecker task #5 marked completed
- [ ] Note added about global config task #11 status

## Rollback Plan

Not applicable - this task makes no code changes. If a fix component is found missing in any location, a new task should be created for that specific remediation.

## Notes

### Relationship to Global Config Task #11

Task #11 in `/home/benjamin/.config/.claude/specs/TODO.md` has the same objective:
> "Use /home/benjamin/.config/.claude/specs/task-command-implementation-bug.md to fix this bug in an elegant way."

Since the fix is already applied to the global config, task #11 can be marked as completed when this verification confirms the fix is in place. This task (#5) serves as verification for both.

### Intentional Differences Between Systems

The three systems have intentional local customizations:

**ModelChecker-specific**:
- 3-digit zero-padded directory names (`005_slug` vs `5_slug`)
- `directory` field in state.json entries
- Explicit timestamp field initialization (started, researched, planned, completed)
- Blocking/Dependencies fields in TODO.md entries

**ProofChecker-specific**:
- More detailed jq implementation examples for recover/divide/sync/abandon modes

These are not bugs and should be preserved as local customizations.
