# Implementation Plan: Standardize Command Lifecycle Procedures (Revised)

**Project Number**: 211  
**Type**: Documentation/Standardization  
**Priority**: High  
**Complexity**: High  
**Estimated Hours**: 12  
**Phases**: 3  
**Version**: 002  
**Revision Date**: 2025-12-28

---

## Metadata

**Created**: 2025-12-28  
**Status**: [NOT STARTED]  
**Previous Plan**: .opencode/specs/211_standardize_command_lifecycle_procedures/plans/implementation-001.md  
**Revision Reason**: Add critical focus on plan status synchronization - ensure that when plans are created they say '[PLANNED]' in both the plan file and task, then update to '[IN PROGRESS]' when implementation begins, and finally to '[BLOCKED]', '[PARTIAL]', or '[COMPLETE]' after implementation completes. All three files (task in TODO.md, plan file, and state.json) must be updated in sync atomically.

**Research Inputs**: 
- .opencode/specs/211_standardize_command_lifecycle_procedures/reports/research-001.md
- .opencode/specs/211_standardize_command_lifecycle_procedures/summaries/research-summary.md

**Task Dependencies**: None  
**Blocking**: None

---

## Overview

This revised plan builds on the successful completion of Phases 1-3 from implementation-001.md (command-lifecycle.md created, 4 commands updated, 6 agents updated with 33% duplication reduction). The revision adds critical focus on **plan status synchronization** - a pattern where plan files themselves contain status markers that track implementation progress, and these markers must be synchronized atomically across three files: TODO.md task entry, plan file phases, and state.json.

**Key Insight from Revision Request**: Plan files are not static documents - they are living artifacts that track implementation progress through phase status markers. When /plan creates a plan, all phases start as [NOT STARTED]. When /implement executes, phases transition to [IN PROGRESS] as they execute, then to [COMPLETED], [BLOCKED], or [PARTIAL] when finished. This status must synchronize across TODO.md (task status), plan file (phase statuses), and state.json (project status) atomically to maintain consistency.

**Critical Gap Identified**: Current command-lifecycle.md documents status synchronization for TODO.md and state.json, but does NOT document plan file status synchronization. This revision adds comprehensive plan status synchronization documentation to command-lifecycle.md and updates /plan, /revise, and /implement commands to follow the pattern.

---

## Research Inputs

### Previous Implementation (Phases 1-3 Completed)

From implementation-summary-20251228.md:
- Phase 1: command-lifecycle.md created (808 lines) with 8-stage pattern
- Phase 2: 4 commands updated with lifecycle references (33% duplication reduction)
- Phase 3: 6 agents updated with summary validation and lifecycle references
- Phase 4: Testing deferred (documentation-only changes)

**Success Metrics Achieved**:
- Duplication reduction: 33% (1,961 → 1,320 lines)
- Single source of truth: Created (command-lifecycle.md)
- Variation documentation: 100% (8 variation tables)
- Compliance improvement: 95% → 100% (subagent-return-format.md)

### Revision Requirements

From revision request:
1. Plan files contain status markers that track implementation progress
2. When /plan creates plan: mark all phases as [NOT STARTED] initially
3. When /implement starts: update plan phases to [IN PROGRESS] as they execute
4. When /implement completes: update plan phases to [COMPLETED], [BLOCKED], or [PARTIAL]
5. All status updates must synchronize across TODO.md, plan file, and state.json atomically
6. Use status-sync-manager for atomic multi-file updates
7. Ensure command-lifecycle.md documents this plan status synchronization pattern

### Plan Status Synchronization Pattern

**Three-File Synchronization**:
1. **TODO.md task entry**: Task-level status ([PLANNED] → [IMPLEMENTING] → [COMPLETED]/[PARTIAL]/[BLOCKED])
2. **Plan file phases**: Phase-level status ([NOT STARTED] → [IN PROGRESS] → [COMPLETED]/[BLOCKED]/[PARTIAL])
3. **state.json project**: Project-level status and phase tracking

**Atomic Update Requirement**: All three files must be updated together in a single atomic operation to prevent inconsistencies. If any update fails, all must roll back.

**Status Markers in Plan Files**:
```markdown
## Phase 1: Setup [NOT STARTED]
## Phase 2: Implementation [IN PROGRESS]
## Phase 3: Testing [COMPLETED]
## Phase 4: Documentation [BLOCKED]
```

**Synchronization Points**:
- /plan creates plan: Set all phases to [NOT STARTED], task to [PLANNED]
- /implement starts phase: Update phase to [IN PROGRESS], task to [IMPLEMENTING]
- /implement completes phase: Update phase to [COMPLETED]/[BLOCKED]/[PARTIAL]
- /implement completes all phases: Update task to [COMPLETED]/[PARTIAL]/[BLOCKED]

---

## Phase 1: Enhance command-lifecycle.md with Plan Status Synchronization [NOT STARTED]

**Estimated Time**: 4 hours  
**Complexity**: Medium  
**Risk**: Low (additive documentation)

### Objectives

Add comprehensive plan status synchronization documentation to command-lifecycle.md, including three-file synchronization pattern, atomic update requirements, status marker formats, and synchronization points across /plan, /revise, and /implement commands.

### Tasks

1. **Add Plan Status Synchronization Section** (1.5 hours)
   - Create new section: "Plan Status Synchronization Pattern"
   - Document three-file synchronization requirement (TODO.md, plan file, state.json)
   - Document atomic update requirement using status-sync-manager
   - Document rollback behavior if any update fails
   - Document status marker format in plan files (phase headers with status)
   - Add examples showing synchronization across all three files

2. **Document Plan Phase Status Lifecycle** (1 hour)
   - Document phase status markers: [NOT STARTED], [IN PROGRESS], [COMPLETED], [BLOCKED], [PARTIAL]
   - Document phase status transitions during /implement execution
   - Document relationship between phase status and task status
   - Document when task status changes based on phase completion
   - Add decision tree: all phases [COMPLETED] → task [COMPLETED], any phase [BLOCKED] → task [BLOCKED], etc.

3. **Add Synchronization Points Table** (1 hour)
   - Create table showing synchronization points across commands
   - /plan creates plan: TODO.md [PLANNED], plan phases [NOT STARTED], state.json updated
   - /implement starts: TODO.md [IMPLEMENTING], first phase [IN PROGRESS], state.json updated
   - /implement progresses: Current phase [COMPLETED], next phase [IN PROGRESS], state.json updated
   - /implement completes: All phases [COMPLETED]/[BLOCKED]/[PARTIAL], task status updated, state.json updated
   - /revise creates new plan: New plan phases [NOT STARTED], task [REVISED], state.json updated

4. **Add status-sync-manager Integration** (0.5 hours)
   - Document status-sync-manager as atomic update mechanism
   - Document parameters: files to update, status markers, rollback behavior
   - Document error handling if synchronization fails
   - Add example invocation for three-file update

### Deliverable

Enhanced command-lifecycle.md with new section (~150 additional lines):
- Plan Status Synchronization Pattern (overview, requirements, examples)
- Plan Phase Status Lifecycle (markers, transitions, decision tree)
- Synchronization Points Table (5 synchronization scenarios)
- status-sync-manager Integration (atomic updates, error handling)

### Acceptance Criteria

- [ ] Plan Status Synchronization Pattern section added to command-lifecycle.md
- [ ] Three-file synchronization requirement documented (TODO.md, plan file, state.json)
- [ ] Atomic update requirement documented with status-sync-manager
- [ ] Phase status markers documented: [NOT STARTED], [IN PROGRESS], [COMPLETED], [BLOCKED], [PARTIAL]
- [ ] Phase status lifecycle documented with transitions
- [ ] Synchronization points table created with 5 scenarios
- [ ] status-sync-manager integration documented with examples
- [ ] Rollback behavior documented for failed updates
- [ ] Decision tree added for task status based on phase statuses
- [ ] Examples show synchronization across all three files
- [ ] No emojis in documentation

### Risks and Mitigation

**Risk**: status-sync-manager may not support three-file updates
**Mitigation**: Document required enhancement to status-sync-manager if needed, or document sequential update pattern with transaction semantics

**Risk**: Plan file format may not support status markers in phase headers
**Mitigation**: Verify plan.md template supports status markers, update template if needed

---

## Phase 2: Update Commands for Plan Status Synchronization [NOT STARTED]

**Estimated Time**: 5 hours  
**Complexity**: Medium  
**Risk**: Medium (functional changes to commands)

### Objectives

Update /plan, /revise, and /implement commands to implement plan status synchronization pattern, ensuring atomic updates across TODO.md, plan file, and state.json at all synchronization points.

### Tasks

1. **Update /plan Command** (1.5 hours)
   - Add Stage 7 (Postflight) step: Initialize all plan phases to [NOT STARTED]
   - Add three-file synchronization: TODO.md [PLANNED], plan phases [NOT STARTED], state.json updated
   - Document atomic update requirement in Postflight stage
   - Add validation: Verify all phases marked [NOT STARTED] before returning
   - Add error handling: If phase initialization fails, return error
   - Reference plan status synchronization section in command-lifecycle.md

2. **Update /revise Command** (1.5 hours)
   - Add Stage 7 (Postflight) step: Initialize all new plan phases to [NOT STARTED]
   - Add three-file synchronization: TODO.md [REVISED], new plan phases [NOT STARTED], state.json updated
   - Document atomic update requirement in Postflight stage
   - Add validation: Verify all new plan phases marked [NOT STARTED] before returning
   - Add error handling: If phase initialization fails, return error
   - Reference plan status synchronization section in command-lifecycle.md

3. **Update /implement Command - Phase Start** (1 hour)
   - Add Stage 7 (Postflight) step: Update current phase to [IN PROGRESS] when starting
   - Add three-file synchronization: TODO.md [IMPLEMENTING], current phase [IN PROGRESS], state.json updated
   - Document atomic update requirement
   - Add validation: Verify phase status updated before executing phase
   - Add error handling: If phase status update fails, return error
   - Reference plan status synchronization section in command-lifecycle.md

4. **Update /implement Command - Phase Completion** (1 hour)
   - Add Stage 7 (Postflight) step: Update completed phase status based on outcome
   - Add three-file synchronization: phase [COMPLETED]/[BLOCKED]/[PARTIAL], state.json updated
   - Add decision logic: Determine task status based on all phase statuses
   - Add three-file synchronization: TODO.md task status, all phase statuses, state.json updated
   - Document atomic update requirement for final synchronization
   - Add validation: Verify all statuses synchronized before returning
   - Add error handling: If final synchronization fails, return error with rollback instructions

### Deliverable

3 updated command files with plan status synchronization:
- .opencode/command/plan.md (Stage 7 enhanced with phase initialization)
- .opencode/command/revise.md (Stage 7 enhanced with phase initialization)
- .opencode/command/implement.md (Stage 7 enhanced with phase status updates)

### Acceptance Criteria

- [ ] /plan command Stage 7 initializes all plan phases to [NOT STARTED]
- [ ] /plan command performs three-file atomic update (TODO.md, plan file, state.json)
- [ ] /plan command validates phase initialization before returning
- [ ] /revise command Stage 7 initializes all new plan phases to [NOT STARTED]
- [ ] /revise command performs three-file atomic update
- [ ] /revise command validates phase initialization before returning
- [ ] /implement command updates current phase to [IN PROGRESS] when starting
- [ ] /implement command updates completed phase to [COMPLETED]/[BLOCKED]/[PARTIAL]
- [ ] /implement command determines task status based on all phase statuses
- [ ] /implement command performs three-file atomic update at phase start and completion
- [ ] All commands reference plan status synchronization section in command-lifecycle.md
- [ ] All commands include error handling for synchronization failures
- [ ] All commands validate synchronization before returning
- [ ] No emojis in command files

### Risks and Mitigation

**Risk**: Atomic three-file updates may be complex to implement
**Mitigation**: Use status-sync-manager if it supports three files, otherwise implement transaction pattern with rollback

**Risk**: Phase status updates may conflict with concurrent operations
**Mitigation**: Document locking requirement or sequential execution requirement

**Risk**: Plan file parsing may be fragile for status updates
**Mitigation**: Use robust regex patterns, add validation after updates

---

## Phase 3: Update Agents for Plan Status Synchronization [NOT STARTED]

**Estimated Time**: 3 hours  
**Complexity**: Low  
**Risk**: Low (agents delegate to commands)

### Objectives

Update planner and task-executor agents to support plan status synchronization, ensuring they create plans with [NOT STARTED] phases and update phase statuses during implementation.

### Tasks

1. **Update planner Agent** (1.5 hours)
   - Add Step 5 (Create Plan) requirement: Mark all phases as [NOT STARTED]
   - Add validation: Verify all phases marked [NOT STARTED] before returning
   - Document plan status synchronization requirement in agent spec
   - Add example showing phase status markers in plan artifact
   - Reference plan status synchronization section in command-lifecycle.md
   - Add error handling: If phase marking fails, return failed status

2. **Update task-executor Agent** (1.5 hours)
   - Add Step 3 (Execute Phase) requirement: Update phase to [IN PROGRESS] before execution
   - Add Step 4 (Process Results) requirement: Update phase to [COMPLETED]/[BLOCKED]/[PARTIAL] after execution
   - Add Step 5 (Determine Task Status) requirement: Determine task status based on all phase statuses
   - Add three-file synchronization at phase start and completion
   - Document plan status synchronization requirement in agent spec
   - Reference plan status synchronization section in command-lifecycle.md
   - Add error handling: If phase status update fails, return failed status

### Deliverable

2 updated agent files with plan status synchronization:
- .opencode/agent/subagents/planner.md (Step 5 enhanced with phase initialization)
- .opencode/agent/subagents/task-executor.md (Steps 3-5 enhanced with phase status updates)

### Acceptance Criteria

- [ ] planner agent Step 5 marks all phases as [NOT STARTED]
- [ ] planner agent validates phase marking before returning
- [ ] planner agent references plan status synchronization in command-lifecycle.md
- [ ] planner agent includes error handling for phase marking failures
- [ ] task-executor agent Step 3 updates phase to [IN PROGRESS] before execution
- [ ] task-executor agent Step 4 updates phase to [COMPLETED]/[BLOCKED]/[PARTIAL] after execution
- [ ] task-executor agent Step 5 determines task status based on all phase statuses
- [ ] task-executor agent performs three-file synchronization at phase start and completion
- [ ] task-executor agent references plan status synchronization in command-lifecycle.md
- [ ] task-executor agent includes error handling for synchronization failures
- [ ] Both agents document plan status synchronization requirement
- [ ] No emojis in agent files

### Risks and Mitigation

**Risk**: Agents may not have direct file access for plan updates
**Mitigation**: Document that agents delegate to commands for file updates, commands handle synchronization

**Risk**: Phase status determination logic may be complex
**Mitigation**: Document clear decision tree in command-lifecycle.md, reference from agents

---

## Success Criteria

### Overall Goals

1. **Plan Status Synchronization Documented**: command-lifecycle.md includes comprehensive plan status synchronization pattern
2. **Three-File Synchronization Implemented**: TODO.md, plan file, and state.json updated atomically at all synchronization points
3. **Phase Status Lifecycle Implemented**: Phases transition through [NOT STARTED] → [IN PROGRESS] → [COMPLETED]/[BLOCKED]/[PARTIAL]
4. **Commands Updated**: /plan, /revise, and /implement implement plan status synchronization
5. **Agents Updated**: planner and task-executor support plan status synchronization
6. **No Functionality Regression**: All existing functionality preserved

### Phase Completion

- [ ] Phase 1: command-lifecycle.md enhanced with plan status synchronization (~150 additional lines)
- [ ] Phase 2: /plan, /revise, /implement commands updated with synchronization logic
- [ ] Phase 3: planner and task-executor agents updated with synchronization support

### Quality Metrics

- [ ] Plan status synchronization pattern documented comprehensively
- [ ] Three-file synchronization implemented at all 5 synchronization points
- [ ] Phase status markers documented: [NOT STARTED], [IN PROGRESS], [COMPLETED], [BLOCKED], [PARTIAL]
- [ ] Atomic update requirement documented and implemented
- [ ] Error handling for synchronization failures implemented
- [ ] All commands and agents reference plan status synchronization section
- [ ] No emojis in documentation or code
- [ ] All existing functionality preserved

### Deliverables

1. .opencode/context/core/workflows/command-lifecycle.md (enhanced, ~150 additional lines)
2. .opencode/command/plan.md (updated with phase initialization)
3. .opencode/command/revise.md (updated with phase initialization)
4. .opencode/command/implement.md (updated with phase status updates)
5. .opencode/agent/subagents/planner.md (updated with phase initialization)
6. .opencode/agent/subagents/task-executor.md (updated with phase status updates)

---

## Risk Assessment

### High Risks

None identified

### Medium Risks

**Risk 1: Atomic three-file updates may be complex to implement**
- **Impact**: May require significant refactoring of status-sync-manager or commands
- **Probability**: Medium (status-sync-manager may not support three files)
- **Mitigation**: Document required enhancement to status-sync-manager, or implement transaction pattern with rollback
- **Contingency**: Implement sequential updates with validation, document as known limitation

**Risk 2: Plan file parsing for status updates may be fragile**
- **Impact**: Status updates may fail or corrupt plan files
- **Probability**: Medium (plan files have complex structure)
- **Mitigation**: Use robust regex patterns, add validation after updates, test thoroughly
- **Contingency**: Implement backup/restore mechanism for plan files before updates

### Low Risks

**Risk 3: Phase status determination logic may be complex**
- **Impact**: May require complex decision tree for task status
- **Probability**: Low (logic is straightforward: all completed → completed, any blocked → blocked, etc.)
- **Mitigation**: Document clear decision tree in command-lifecycle.md
- **Contingency**: Simplify to conservative approach (any non-completed → partial)

**Risk 4: Concurrent operations may conflict with status updates**
- **Impact**: Multiple commands updating same plan may cause conflicts
- **Probability**: Low (commands typically run sequentially)
- **Mitigation**: Document sequential execution requirement
- **Contingency**: Add file locking mechanism if needed

---

## Implementation Notes

### Key Decisions

1. **Three-file synchronization is atomic**: All three files (TODO.md, plan file, state.json) must be updated together or not at all
2. **Phase status markers in plan file headers**: Use markdown header format with status marker suffix
3. **status-sync-manager handles synchronization**: Extend status-sync-manager to support three-file updates if needed
4. **Task status determined by phase statuses**: All completed → completed, any blocked → blocked, any partial → partial, otherwise in progress
5. **Rollback on failure**: If any file update fails, roll back all updates and return error

### Design Principles

1. **Atomic Updates**: All status updates across three files must be atomic
2. **Consistency First**: Never allow inconsistent state across files
3. **Fail Safe**: If synchronization fails, roll back and return error
4. **Clear Status Lifecycle**: Phase statuses follow clear lifecycle with documented transitions
5. **Validation Always**: Validate synchronization succeeded before returning

### Integration Points

**With Existing Standards**:
- status-markers.md: Phase status markers follow same format as task status markers
- subagent-return-format.md: Agents return phase status in artifacts array
- artifact-management.md: Plan files are artifacts with status tracking
- git-commits.md: Commits include plan file updates

**With Commands**:
- /plan: Creates plan with all phases [NOT STARTED]
- /revise: Creates new plan version with all phases [NOT STARTED]
- /implement: Updates phase statuses as execution progresses

**With Agents**:
- planner: Marks all phases [NOT STARTED] when creating plan
- task-executor: Updates phase statuses during implementation

### Plan Status Synchronization Pattern

**Synchronization Point 1: /plan creates plan**
```
TODO.md:     Task status → [PLANNED]
Plan file:   All phases → [NOT STARTED]
state.json:  status → "planned", plan_artifacts updated
```

**Synchronization Point 2: /implement starts first phase**
```
TODO.md:     Task status → [IMPLEMENTING]
Plan file:   Phase 1 → [IN PROGRESS]
state.json:  status → "implementing", current_phase → 1
```

**Synchronization Point 3: /implement completes phase, starts next**
```
TODO.md:     Task status remains [IMPLEMENTING]
Plan file:   Phase 1 → [COMPLETED], Phase 2 → [IN PROGRESS]
state.json:  current_phase → 2, completed_phases updated
```

**Synchronization Point 4: /implement completes all phases**
```
TODO.md:     Task status → [COMPLETED] (or [PARTIAL]/[BLOCKED])
Plan file:   All phases → [COMPLETED] (or mixed statuses)
state.json:  status → "completed", completed timestamp
```

**Synchronization Point 5: /revise creates new plan**
```
TODO.md:     Task status → [REVISED], new plan link added
Plan file:   New plan with all phases → [NOT STARTED]
state.json:  plan_artifacts updated with new version
```

### Future Enhancements

1. **Plan status dashboard**: Visualize plan progress with phase status overview
2. **Automatic resume**: /implement automatically resumes from last [IN PROGRESS] or [NOT STARTED] phase
3. **Phase dependencies**: Document phase dependencies and validate execution order
4. **Parallel phase execution**: Support concurrent phase execution where dependencies allow

---

## References

### Research Artifacts

- Main Report: .opencode/specs/211_standardize_command_lifecycle_procedures/reports/research-001.md
- Summary: .opencode/specs/211_standardize_command_lifecycle_procedures/summaries/research-summary.md
- Previous Plan: .opencode/specs/211_standardize_command_lifecycle_procedures/plans/implementation-001.md
- Previous Implementation: .opencode/specs/211_standardize_command_lifecycle_procedures/summaries/implementation-summary-20251228.md

### Files to be Modified

- .opencode/context/core/workflows/command-lifecycle.md (enhance with plan status synchronization)
- .opencode/command/plan.md (add phase initialization)
- .opencode/command/revise.md (add phase initialization)
- .opencode/command/implement.md (add phase status updates)
- .opencode/agent/subagents/planner.md (add phase initialization)
- .opencode/agent/subagents/task-executor.md (add phase status updates)

### Related Standards

- .opencode/context/core/standards/status-markers.md (status marker format)
- .opencode/context/core/standards/subagent-return-format.md (return format)
- .opencode/context/core/system/artifact-management.md (artifact management)
- .opencode/context/core/system/git-commits.md (commit patterns)
- .opencode/context/core/system/state-schema.md (state.json schema)

### Related Tasks

- Task 191: Fix subagent delegation hang (created subagent-return-format.md)
- Task 169: Context window protection (created summary requirements)
- Task 156: Targeted git commits (created git-commits.md)
- Task 208: Fix Lean routing (enhanced routing validation)
- Task 207: Reduce implement output verbosity (summary artifacts)
