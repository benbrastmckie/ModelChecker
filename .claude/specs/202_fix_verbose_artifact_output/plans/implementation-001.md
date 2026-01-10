# Implementation Plan: Fix Verbose Artifact Output in Commands

- **Task**: 202 - Fix verbose artifact output in commands to protect primary agent context window
- **Status**: [COMPLETED]
- **Note**: Investigation revealed issue already resolved - no implementation needed
- **Effort**: 4-5 hours
- **Priority**: Medium
- **Complexity**: Low
- **Dependencies**: None
- **Research Inputs**: 
  - Main Report: .opencode/specs/202_fix_verbose_artifact_output/reports/research-001.md
  - Summary: .opencode/specs/202_fix_verbose_artifact_output/summaries/research-summary.md
- **Artifacts**: plans/implementation-001.md (this file)
- **Standards**:
  - .opencode/context/core/standards/plan.md
  - .opencode/context/core/standards/status-markers.md
  - .opencode/context/core/system/artifact-management.md
  - .opencode/context/core/standards/subagent-return-format.md
- **Language**: markdown
- **Lean Intent**: false

## Overview

Research identified that verbose artifact output is localized to two legacy subagents (task-executor and batch-task-orchestrator) that were created before subagent-return-format.md was standardized. These subagents return 100-1000+ lines of verbose internal tracking details instead of concise summaries, bloating the primary agent's context window. The fix requires updating both subagents to follow the subagent-return-format.md standard, reducing output by 90-95% while maintaining full artifact creation. Commands (/research, /plan, /implement) are already correctly specified; only the legacy subagents need updates.

## Goals & Non-Goals

**Goals**:
- Update task-executor to follow subagent-return-format.md standard (100+ lines → ~10 lines)
- Update batch-task-orchestrator to follow subagent-return-format.md standard (1000+ lines → ~50 lines)
- Create batch-summary.md artifact for detailed batch execution results
- Protect primary agent context window from verbose artifact bloat
- Maintain all existing artifact creation functionality
- Achieve 90-95% reduction in returned output size

**Non-Goals**:
- Changing command files (already correct)
- Updating newer subagents (already follow standard)
- Modifying artifact content or quality
- Changing workflow logic or execution paths

## Risks & Mitigations

- **Risk**: Breaking existing /implement command workflows that depend on verbose return format
  - **Mitigation**: Test with both single task and task range execution; verify all status updates and artifact links work correctly

- **Risk**: Losing important diagnostic information by removing verbose fields
  - **Mitigation**: Create batch-summary.md artifact to preserve all details; only remove from inline return

- **Risk**: Incomplete standardization leaving edge cases with verbose output
  - **Mitigation**: Follow subagent-return-format.md exactly; validate all return paths

- **Risk**: Regression in TODO.md or state.json status updates
  - **Mitigation**: Test status-sync-manager integration; verify atomic updates work with new format

## Research Inputs

Research completed on 2025-12-27 identified the following key findings:

1. **Root Cause**: task-executor and batch-task-orchestrator return verbose output (100-1000+ lines) instead of following subagent-return-format.md standard
2. **Commands are correct**: /research, /plan, /implement all specify concise returns
3. **Newer subagents are correct**: researcher, lean-research-agent, planner follow standard
4. **Scope of fix**: Update 2 subagent files only
5. **Impact**: 90-95% context window reduction after fix

**Files to Update**:
- .opencode/agent/subagents/task-executor.md (lines 559-706: return format)
- .opencode/agent/subagents/batch-task-orchestrator.md (lines 344-398: return format)

**Recommended Approach**: Full standardization (4-5 hours) over quick fix (1.25 hours) to avoid technical debt

## Implementation Phases

### Phase 1: Fix task-executor Return Format [NOT APPLICABLE]

**Investigation Finding**: task-executor.md already follows subagent-return-format.md standard (lines 219-366). Return format is already concise and compliant. No changes needed.

- **Goal**: Update task-executor to return concise summary following subagent-return-format.md standard
- **Tasks**:
  - [ ] Read current task-executor.md return format (lines 559-706)
  - [ ] Replace custom return format with subagent-return-format.md standard structure
  - [ ] Remove verbose fields: todo_status_tracking, workflow_executed, coordinator_results (extract summary only)
  - [ ] Add standard status enum (completed|partial|failed|blocked)
  - [ ] Add concise summary field (2-5 sentences, max 100 tokens)
  - [ ] Add standard metadata block (session_id, duration, agent_type, delegation info)
  - [ ] Keep artifacts array (already correct format)
  - [ ] Condense next_steps to 1-2 sentences
  - [ ] Update return construction logic in workflow stage 10 to match new format
  - [ ] Verify all return paths use new format
- **Timing**: 1.25 hours
- **Acceptance Criteria**:
  - task-executor returns ~10 lines instead of 100+ lines
  - Return format matches subagent-return-format.md exactly
  - No verbose internal tracking in return
  - Coordinator results summarized to one sentence
  - All required fields present (status, summary, artifacts, metadata)

### Phase 2: Fix batch-task-orchestrator Return Format and Create Batch Summary Artifact [NOT APPLICABLE]

**Investigation Finding**: batch-task-orchestrator.md file does not exist in current codebase. File not found at `.opencode/agent/subagents/batch-task-orchestrator.md`. Research report may be based on outdated information or planned but unimplemented feature.

- **Goal**: Update batch-task-orchestrator to return aggregate stats and create batch-summary.md artifact for details
- **Tasks**:
  - [ ] Read current batch-task-orchestrator.md return format (lines 344-398)
  - [ ] Design batch-summary.md artifact structure (dependency analysis, wave results, per-task details)
  - [ ] Implement batch summary artifact generation logic in workflow
  - [ ] Replace custom return format with subagent-return-format.md standard structure
  - [ ] Remove verbose fields: full task_results, dependency_analysis, wave_results (move to artifact)
  - [ ] Add standard status enum (completed|partial)
  - [ ] Add concise summary covering batch execution (tasks completed/failed/blocked, waves, duration)
  - [ ] Add batch-summary.md artifact to artifacts array
  - [ ] Add batch_summary object with aggregate stats (total_tasks, completed, failed, blocked, waves, artifacts_created)
  - [ ] Add standard metadata block
  - [ ] Condense errors to only failed task errors (concise format)
  - [ ] Update return construction logic in workflow final stage
  - [ ] Verify batch summary artifact created correctly
- **Timing**: 2.25 hours
- **Acceptance Criteria**:
  - batch-task-orchestrator returns ~50 lines instead of 1000+ lines for 10 tasks
  - Return format matches subagent-return-format.md exactly
  - batch-summary.md artifact created with full details
  - Artifact referenced in return, not duplicated inline
  - Aggregate stats provide quick overview without verbose details

### Phase 3: Testing and Validation [NOT APPLICABLE]

**Investigation Finding**: No implementation changes made, so no testing needed. Current subagents already compliant with standards.

- **Goal**: Verify both subagents work correctly with new return formats and achieve context window reduction
- **Tasks**:
  - [ ] Test /implement with single task (no plan) - verify task-executor return format
  - [ ] Verify TODO.md status updated to [COMPLETED] correctly
  - [ ] Verify state.json updated correctly
  - [ ] Verify artifacts created and linked correctly
  - [ ] Test /implement with task range (3 tasks) - verify batch-task-orchestrator return format
  - [ ] Verify batch-summary.md artifact created
  - [ ] Verify all 3 tasks updated in TODO.md correctly
  - [ ] Measure context window reduction (before/after line counts)
  - [ ] Verify no regression in artifact creation or quality
  - [ ] Test error handling (failed task, blocked task)
- **Timing**: 0.75 hours
- **Acceptance Criteria**:
  - Single task execution returns ~10 lines (90% reduction from 100+ lines)
  - Batch execution returns ~50 lines (95% reduction from 1000+ lines)
  - All status updates work correctly
  - All artifacts created correctly
  - No regression in functionality

### Phase 4: Documentation Updates [NOT APPLICABLE]

**Investigation Finding**: No implementation changes made, so no documentation updates needed. Recommend updating or archiving research report to reflect current state.

- **Goal**: Document batch summary pattern and update subagent-return-format.md with batch example
- **Tasks**:
  - [ ] Update artifact-management.md with batch summary artifact pattern
  - [ ] Add batch summary example to artifact-management.md
  - [ ] Update subagent-return-format.md with batch-task-orchestrator example
  - [ ] Document batch_summary object structure in subagent-return-format.md
  - [ ] Add migration notes for other batch-style subagents
  - [ ] Verify documentation clarity and completeness
- **Timing**: 0.5 hours
- **Acceptance Criteria**:
  - artifact-management.md documents batch summary pattern
  - subagent-return-format.md includes batch example
  - Documentation clear and complete
  - Future batch subagents can follow documented pattern

## Testing & Validation

**Unit Tests**:
- [ ] task-executor return format validation (all required fields present)
- [ ] batch-task-orchestrator return format validation (all required fields present)
- [ ] batch-summary.md artifact structure validation

**Integration Tests**:
- [ ] /implement with single task (no plan) - end-to-end workflow
- [ ] /implement with task range (3 tasks) - batch execution workflow
- [ ] Error handling (failed task, blocked task)

**Context Window Validation**:
- [ ] Measure task-executor output: before (100+ lines) vs after (~10 lines)
- [ ] Measure batch-task-orchestrator output: before (1000+ lines for 10 tasks) vs after (~50 lines)
- [ ] Verify 90-95% reduction achieved

**Regression Tests**:
- [ ] TODO.md status updates work correctly
- [ ] state.json updates work correctly
- [ ] Artifact creation and linking work correctly
- [ ] Git commits work correctly
- [ ] Plan file updates work correctly (for tasks with plans)

## Artifacts & Outputs

**Modified Files**:
- .opencode/agent/subagents/task-executor.md (return format section updated)
- .opencode/agent/subagents/batch-task-orchestrator.md (return format section updated)
- .opencode/context/core/system/artifact-management.md (batch summary pattern added)
- .opencode/context/core/standards/subagent-return-format.md (batch example added)

**New Artifacts**:
- .opencode/specs/batch_{timestamp}/summaries/batch-summary.md (created by batch-task-orchestrator)

**Implementation Summary**:
- .opencode/specs/202_fix_verbose_artifact_output/summaries/implementation-summary-YYYYMMDD.md

## Rollback/Contingency

**If implementation fails or causes regressions**:

1. **Immediate Rollback**:
   - Revert task-executor.md to previous return format
   - Revert batch-task-orchestrator.md to previous return format
   - Revert documentation changes
   - Test /implement command to verify rollback successful

2. **Alternative: Quick Fix**:
   - If full standardization proves too complex, implement quick fix instead:
   - task-executor: Remove only todo_status_tracking and workflow_executed fields (0.5h)
   - batch-task-orchestrator: Replace full task_results with summary array (0.75h)
   - Achieves 80% reduction with lower risk
   - Leaves technical debt for future cleanup

3. **Partial Implementation**:
   - If one subagent works but other fails, deploy working subagent only
   - Document remaining work for failed subagent
   - Create follow-up task for completion

**Validation Before Deployment**:
- Test both single task and batch execution thoroughly
- Verify no breaking changes to command workflows
- Confirm context window reduction achieved
- Ensure all acceptance criteria met

## Success Criteria

**Primary Success Criteria**:
- [ ] task-executor returns ~10 lines instead of 100+ lines (90% reduction)
- [ ] batch-task-orchestrator returns ~50 lines instead of 1000+ lines for 10 tasks (95% reduction)
- [ ] Both subagents follow subagent-return-format.md standard exactly
- [ ] Primary agent context window protected from verbose artifact bloat
- [ ] All existing functionality preserved (no regressions)

**Secondary Success Criteria**:
- [ ] batch-summary.md artifact pattern documented and reusable
- [ ] Documentation updated with batch examples
- [ ] Testing confirms 90-95% context window reduction
- [ ] Error handling works correctly with new format

**Completion Definition**:
All acceptance criteria met, all tests passing, documentation updated, and /implement command verified working with both single task and batch execution using new concise return formats.
