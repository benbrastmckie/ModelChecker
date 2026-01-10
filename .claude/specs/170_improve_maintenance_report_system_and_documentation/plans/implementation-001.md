# Implementation Plan: Improve Maintenance Report System and Documentation

- **Task**: 170 - Improve maintenance report system and documentation
- **Status**: [COMPLETED]
- **Effort**: 3 hours
- **Priority**: Low
- **Dependencies**: None
- **Research Inputs**: 
  - Main Report: .opencode/specs/170_improve_maintenance_report_system_and_documentation/reports/research-001.md
  - Key Findings: /review command exists but lacks status-sync-manager integration, project state.json creation, and comprehensive state file updates. Research identified 6 priority improvements with 5-7 hour total effort.
- **Artifacts**: 
  - plans/implementation-001.md (this file)
- **Standards**:
  - .opencode/context/core/standards/plan.md
  - .opencode/context/core/standards/status-markers.md
  - .opencode/context/core/system/artifact-management.md
  - .opencode/context/core/standards/tasks.md
- **Language**: markdown
- **Lean Intent**: false

## Overview

The /review command currently creates review summary artifacts and updates registries but lacks integration with status-sync-manager for atomic state updates and does not create project state.json files. This plan implements 4 critical improvements to align /review with other workflow commands (/research, /plan, /implement): (1) integrate status-sync-manager for atomic updates across TODO.md, state.json, and project state.json, (2) add project state.json lazy creation, (3) update repository_health metrics from reviewer return, and (4) clarify task creation patterns. These changes ensure consistency across the maintenance workflow and deliver atomic update guarantees.

## Goals & Non-Goals

**Goals:**
- Integrate /review command with status-sync-manager for atomic state updates
- Add project state.json lazy creation to /review workflow
- Update repository_health metrics (technical_debt, last_assessed) from reviewer return
- Clarify task creation batching pattern in /review Stage 6
- Update reviewer.md documentation with state file expectations
- Ensure /review follows same patterns as /research, /plan, /implement

**Non-Goals:**
- Changing /todo command responsibilities (cleanup operations only)
- Adding maintenance/state.json updates (deferred to future work)
- Modifying review summary artifact format (already compliant)
- Changing reviewer.md core workflow (only documentation updates)

## Risks & Mitigations

**Risk 1: Breaking Changes to /review Workflow**
- Likelihood: Medium
- Impact: High
- Mitigation: Test /review workflow thoroughly before deployment, add rollback mechanism to status-sync-manager, document migration path for existing review projects

**Risk 2: State File Corruption**
- Likelihood: Low
- Impact: High
- Mitigation: Use two-phase commit with backup, validate JSON before writing, add self-healing for corrupted state files

**Risk 3: Task Creation Failures**
- Likelihood: Medium
- Impact: Medium
- Mitigation: Continue on task creation failure (don't abort review), log failed task descriptions for manual creation, include failed task count in review summary

## Implementation Phases

### Phase 1: Update /review.md Stage 7 with status-sync-manager integration [COMPLETED]

- **Completed**: 2025-12-28T12:00:00Z
- **Goal:** Integrate /review command with status-sync-manager for atomic state updates across TODO.md, state.json, and project state.json
- **Tasks:**
  - [ ] Read current /review.md Stage 7 (Postflight) section
  - [ ] Replace manual state.json updates with status-sync-manager delegation
  - [ ] Add validated_artifacts parameter from reviewer return
  - [ ] Add review_metrics parameter from reviewer return
  - [ ] Add created_tasks parameter from CreateTasks stage
  - [ ] Document two-phase commit pattern (prepare, validate, backup, write or rollback)
  - [ ] Add atomicity guarantee documentation (TODO.md + state.json + project state.json)
  - [ ] Add error handling for status-sync-manager failures with rollback
  - [ ] Verify no manual TODO.md or state.json updates remain in Stage 7
- **Timing:** 1 hour
- **Acceptance Criteria:**
  - Stage 7 delegates all updates to status-sync-manager
  - No manual state file updates in /review.md
  - Two-phase commit pattern documented
  - Error handling with rollback added

### Phase 2: Add project state.json creation to /review workflow [COMPLETED]

- **Completed**: 2025-12-28T12:30:00Z
- **Goal:** Enable /review to create project state.json lazily when reviewer writes first artifact, following same pattern as /research and /plan
- **Tasks:**
  - [ ] Read current reviewer.md Step 4 (artifact creation)
  - [ ] Add project state.json lazy creation trigger when writing review summary
  - [ ] Define project state.json schema for review projects (type: "review", scope, metrics, registries_updated)
  - [ ] Update /review.md Stage 7 to include project state.json in atomic update
  - [ ] Add project state.json validation to status-sync-manager delegation
  - [ ] Document project state.json structure in /review.md
  - [ ] Add example project state.json to /review.md documentation
- **Timing:** 1 hour
- **Acceptance Criteria:**
  - Project state.json created lazily when reviewer writes first artifact
  - Schema includes type, status, scope, created, completed, artifacts, metrics, registries_updated
  - Project state.json included in status-sync-manager atomic update
  - Example documented in /review.md

### Phase 3: Update repository_health metrics from reviewer return [COMPLETED]

- **Completed**: 2025-12-28T12:45:00Z
- **Goal:** Update state.json repository_health section with metrics from reviewer return (sorry_count, axiom_count, build_errors, last_assessed)
- **Tasks:**
  - [ ] Read current state.json repository_health schema
  - [ ] Update /review.md Stage 7 to extract metrics from reviewer return
  - [ ] Add repository_health.technical_debt update (sorry_count, axiom_count, build_errors)
  - [ ] Add repository_health.last_assessed timestamp update
  - [ ] Add repository_health.review_artifacts array update (already exists, verify)
  - [ ] Include repository_health updates in status-sync-manager delegation
  - [ ] Document repository_health update pattern in /review.md
  - [ ] Add example repository_health update to /review.md
- **Timing:** 30 minutes
- **Acceptance Criteria:**
  - repository_health.technical_debt updated from reviewer metrics
  - repository_health.last_assessed updated with review timestamp
  - repository_health.review_artifacts array updated (verified)
  - Updates included in status-sync-manager atomic update

### Phase 4: Clarify task creation pattern in /review Stage 6 [COMPLETED]

- **Completed**: 2025-12-28T13:00:00Z
- **Goal:** Document clear task creation pattern in /review.md Stage 6 (CreateTasks) with error handling and batching strategy
- **Tasks:**
  - [ ] Read current /review.md Stage 6 (CreateTasks) section
  - [ ] Document task creation loop (one /task invocation per identified task)
  - [ ] Add error handling specification (continue on failure, log error)
  - [ ] Document task numbering (sequential, no gaps)
  - [ ] Document task linking (link to review findings in description)
  - [ ] Add task creation failure handling (log failed tasks, include count in summary)
  - [ ] Add example task creation loop to /review.md
  - [ ] Document decision: Create ALL identified tasks (no batching)
- **Timing:** 30 minutes
- **Acceptance Criteria:**
  - Task creation pattern documented (one /task per identified task)
  - Error handling specified (continue on failure, log error)
  - Task linking pattern documented
  - Example task creation loop added

### Phase 5: Update reviewer.md documentation with state file expectations [COMPLETED]

- **Completed**: 2025-12-28T13:15:00Z
- **Goal:** Update reviewer.md to document state file update expectations and integration with /review command
- **Tasks:**
  - [ ] Read current reviewer.md integration_notes section
  - [ ] Add note about /review command's responsibility for state file updates
  - [ ] Document metrics return format for state.json integration
  - [ ] Document identified_tasks return format for task creation
  - [ ] Add example return object with metrics and identified_tasks
  - [ ] Document project state.json lazy creation trigger
  - [ ] Verify reviewer.md return format matches subagent-return-format.md
- **Timing:** 30 minutes
- **Acceptance Criteria:**
  - State file update responsibilities documented
  - Metrics return format documented
  - identified_tasks return format documented
  - Example return object added

### Phase 6: Testing and validation [COMPLETED]

- **Completed**: 2025-12-28T13:30:00Z
- **Goal:** Test /review workflow with status-sync-manager integration and validate atomic updates
- **Tasks:**
  - [ ] Test /review command with full scope (creates review summary, updates registries, creates tasks)
  - [ ] Verify status-sync-manager atomic update (TODO.md + state.json + project state.json)
  - [ ] Verify project state.json created lazily with correct schema
  - [ ] Verify repository_health metrics updated from reviewer return
  - [ ] Verify task creation loop works with error handling
  - [ ] Test rollback on status-sync-manager failure (simulate write failure)
  - [ ] Verify no partial updates (all files updated or none)
  - [ ] Verify review summary artifact created following summary.md standard
  - [ ] Verify registries updated (IMPLEMENTATION_STATUS.md, SORRY_REGISTRY.md, TACTIC_REGISTRY.md, FEATURE_REGISTRY.md)
- **Timing:** 1 hour
- **Acceptance Criteria:**
  - /review workflow completes successfully
  - Atomic updates verified (all files updated or none)
  - Project state.json created with correct schema
  - repository_health metrics updated correctly
  - Task creation works with error handling
  - Rollback works on failure

## Testing & Validation

- [ ] /review command completes successfully with status-sync-manager integration
- [ ] TODO.md updated with created tasks
- [ ] state.json updated with repository_health metrics and review_artifacts
- [ ] Project state.json created lazily with correct schema
- [ ] repository_health.technical_debt updated from reviewer metrics
- [ ] repository_health.last_assessed updated with review timestamp
- [ ] Task creation loop creates all identified tasks
- [ ] Error handling works (continue on task creation failure)
- [ ] Rollback works on status-sync-manager failure
- [ ] No partial updates (atomic guarantee verified)
- [ ] Review summary artifact created following summary.md standard
- [ ] Registries updated (4 registries)
- [ ] Git commit created with all changes

## Artifacts & Outputs

- **Plans:**
  - .opencode/specs/170_improve_maintenance_report_system_and_documentation/plans/implementation-001.md (this file)

- **Updated Files:**
  - .opencode/command/review.md (Stage 6 and Stage 7 updates)
  - .opencode/agent/subagents/reviewer.md (documentation updates)

- **Test Artifacts:**
  - Test review project directory with state.json
  - Test state.json with updated repository_health
  - Test TODO.md with created tasks

## Rollback/Contingency

If status-sync-manager integration causes issues:
1. Revert /review.md Stage 7 to manual state.json updates
2. Remove project state.json creation from reviewer.md
3. Remove repository_health metric updates
4. Document rollback in git commit message
5. Create follow-up task to investigate and fix status-sync-manager issues

If task creation failures are too frequent:
1. Add batching logic to Stage 6 (create high-priority tasks only)
2. Document manual task creation process for failed tasks
3. Add task creation retry mechanism
4. Create follow-up task to improve /task command reliability

## Notes

**Research Integration:**
- Research report identified 6 priority improvements with 5-7 hour total effort
- This plan implements Priority 1-4 (HIGH and MEDIUM) for 3-hour scope
- Priority 5-6 (LOW) deferred to future work (maintenance/state.json updates, additional documentation)
- Research found /review is only workflow command not using status-sync-manager
- Research confirmed /review should follow same patterns as /research, /plan, /implement

**Scope Decisions:**
- Focused on critical improvements (status-sync-manager, project state.json, repository_health)
- Deferred maintenance/state.json updates (Priority 5) to future work
- Deferred additional reviewer.md documentation (Priority 6) to future work
- Total effort: 3 hours (matches task estimate)

**Key Patterns from Research:**
- All workflow commands use status-sync-manager for atomic updates
- All workflow commands create project state.json lazily
- All workflow commands update state.json appropriately
- /review is the only command that creates tasks from reports
- Task creation pattern: one /task invocation per identified task, continue on failure
