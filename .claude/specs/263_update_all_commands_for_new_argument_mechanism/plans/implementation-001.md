# Implementation Plan: Update All Commands for New Argument Mechanism

**Task**: 263  
**Status**: [NOT STARTED]  
**Effort**: 3 hours  
**Priority**: Critical  
**Dependencies**: 261 (design), 262 (orchestrator update)  
**Artifacts**: Updated command files  
**Standards**: Command design, argument handling  
**Type**: meta  
**Lean Intent**: N/A (meta task)

## Overview

Update all command files in `.opencode/command/` to use the new argument passing mechanism designed in task 261. This includes updating frontmatter, documentation, and any workflow stages that reference argument handling.

## Goals

1. Update all command files to use new argument mechanism
2. Ensure consistency across all commands
3. Maintain backward compatibility where possible
4. Update examples and documentation in each command
5. Verify all commands follow the new standard

## Non-Goals

- Testing the commands (that's task 264)
- Updating subagent files (unless required by design)
- Creating new commands

## Risks & Mitigations

| Risk | Impact | Mitigation |
|------|--------|------------|
| Updates may break existing commands | High | Update one command at a time, test incrementally |
| Inconsistencies across commands | Medium | Use checklist for each command |
| Missing edge cases | Medium | Review all argument patterns |

## Implementation Phases

### Phase 1: Command Inventory [NOT STARTED]
**Estimated**: 15 minutes

**Objective**: Identify all commands that need updating

**Steps**:
1. List all command files in `.opencode/command/`
2. Categorize by command type (task-based vs direct)
3. Identify which commands use arguments
4. Create update checklist for each command

**Acceptance Criteria**:
- [ ] All command files identified
- [ ] Commands categorized by type
- [ ] Update checklist created

**Commands to Update**:
- Task-based: implement.md, research.md, plan.md, revise.md
- Direct: meta.md, review.md, todo.md, errors.md, task.md

### Phase 2: Update Task-Based Commands [NOT STARTED]
**Estimated**: 90 minutes

**Objective**: Update commands that require task numbers

**Steps**:
For each task-based command (implement, research, plan, revise):
1. Update frontmatter if needed
2. Update "Usage" section with new pattern
3. Update argument parsing documentation
4. Update examples to reflect new mechanism
5. Remove or update `$ARGUMENTS` references
6. Verify consistency with new standard

**Acceptance Criteria**:
- [ ] implement.md updated
- [ ] research.md updated
- [ ] plan.md updated
- [ ] revise.md updated
- [ ] All task-based commands consistent with new standard

### Phase 3: Update Direct Commands [NOT STARTED]
**Estimated**: 60 minutes

**Objective**: Update commands with optional or no arguments

**Steps**:
For each direct command (meta, review, todo, errors, task):
1. Update frontmatter if needed
2. Update "Usage" section if applicable
3. Update argument handling documentation
4. Update examples to reflect new mechanism
5. Remove or update `$ARGUMENTS` references
6. Verify consistency with new standard

**Acceptance Criteria**:
- [ ] meta.md updated
- [ ] review.md updated
- [ ] todo.md updated
- [ ] errors.md updated
- [ ] task.md updated
- [ ] All direct commands consistent with new standard

### Phase 4: Validation and Documentation [NOT STARTED]
**Estimated**: 15 minutes

**Objective**: Validate all updates and create summary

**Steps**:
1. Review all updated command files for consistency
2. Verify all commands follow new standard
3. Check for any broken references or outdated patterns
4. Create implementation summary documenting changes
5. Prepare test cases for task 264

**Acceptance Criteria**:
- [ ] All command files validated
- [ ] Implementation summary created
- [ ] Test cases prepared for task 264

## Testing & Validation

**Validation Checklist** (for each command):
- [ ] Frontmatter is valid YAML
- [ ] Usage section is accurate
- [ ] Examples reflect new mechanism
- [ ] No references to old `$ARGUMENTS` pattern (unless still valid)
- [ ] Consistent with command-argument-handling.md standard
- [ ] Error messages are clear and actionable

**Manual Review**:
- Read through each command file for consistency
- Verify examples are accurate and helpful
- Check that all commands use same patterns for same argument types

## Artifacts & Outputs

**Primary Artifacts**:
- `.opencode/command/implement.md` - Updated
- `.opencode/command/research.md` - Updated
- `.opencode/command/plan.md` - Updated
- `.opencode/command/revise.md` - Updated
- `.opencode/command/meta.md` - Updated
- `.opencode/command/review.md` - Updated
- `.opencode/command/todo.md` - Updated
- `.opencode/command/errors.md` - Updated
- `.opencode/command/task.md` - Updated

**Secondary Artifacts**:
- Implementation summary documenting all changes
- Test case list for task 264

## Rollback/Contingency

If updates break commands:
1. Restore affected command from backup
2. Document what failed and why
3. Revise update approach
4. Retry with corrected logic

## Success Criteria

- [ ] All command files updated with new argument mechanism
- [ ] All commands consistent with new standard
- [ ] All examples accurate and helpful
- [ ] All references to old mechanism updated or removed
- [ ] Commands ready for testing in task 264
