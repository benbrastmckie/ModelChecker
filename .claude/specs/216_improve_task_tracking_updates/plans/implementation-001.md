# Implementation Plan: Systematically Improve Task Tracking File Update Procedures

**Project Number**: 216  
**Type**: System Enhancement/Standardization  
**Priority**: High  
**Complexity**: Medium  
**Estimated Hours**: 10-12  
**Phases**: 4  

---

## Metadata

**Created**: 2025-12-28  
**Status**: [COMPLETED]  
**Research Inputs**: 
- .opencode/specs/216_improve_task_tracking_updates/reports/research-001.md
- .opencode/specs/216_improve_task_tracking_updates/summaries/research-summary.md

**Task Dependencies**: Task 211 (Completed)  
**Blocking**: None

---

## Overview

Systematically improve task tracking file update procedures across all workflow commands (/research, /plan, /revise, /implement) by enhancing the existing status-sync-manager with artifact validation, plan metadata tracking, and project state.json creation capabilities. Research identified 7 critical gaps including: project state.json never created (violates state-schema.md), artifact links added without validation, plan file phase updates not atomic, and plan metadata/version history not tracked. The recommended hybrid architecture (enhanced status-sync-manager + distributed validation) provides full atomicity guarantees with lowest implementation complexity (+205 lines total) while ensuring all tracking files are updated consistently and atomically.

**Key Insight**: A robust status-sync-manager with two-phase commit already exists but is significantly underutilized (~40% coverage). Commands perform manual updates outside atomic transactions, creating risks of partial updates and inconsistent state. Enhancing status-sync-manager and delegating all updates through it will guarantee atomicity across TODO.md, state.json, project state.json, and plan files.

---

## Research Inputs

### Critical Gaps Identified (7)

1. **Project state.json never created**: Violates state-schema.md specification, no project-level state tracking
2. **Artifact links added without validation**: Risk of broken links if artifact creation fails
3. **Plan file phase updates not atomic**: Risk of TODO.md/state.json divergence from plan file
4. **Plan metadata not tracked**: Phase count, estimated hours, complexity missing from state.json
5. **Plan version history not tracked**: Cannot reconstruct plan evolution across revisions
6. **Implementation summaries not tracked**: Not added to state.json artifacts array
7. **Resume logic reads plan file directly**: Tight coupling, fragile implementation

### Architectural Limitations (4)

1. **status-sync-manager underutilized**: ~40% coverage, exists but bypassed by manual updates
2. **Commands perform manual updates**: Outside atomic transactions, breaking atomicity guarantees
3. **No artifact validation**: Files may not exist before linking
4. **No project state.json implementation**: Schema defined but never created

### Recommended Architecture

**Hybrid: Enhanced status-sync-manager + Distributed Validation**

**Rationale**:
- Lowest complexity: +205 lines total (vs +310 centralized, +530 distributed)
- Full atomicity: Two-phase commit across TODO.md, state.json, project state.json, plan files
- Clear separation: Coordination (status-sync-manager) vs Validation (subagents)
- Best extensibility: New artifact types add validation, not coordination logic
- Guaranteed consistency: Automatic rollback on failure

**Architecture Components**:
- **status-sync-manager**: Coordination, atomicity, rollback, project state.json creation
- **Subagents**: Artifact validation, metadata extraction (researcher, planner, implementer, lean-implementation-agent)
- **Commands**: Delegation to status-sync-manager (remove manual updates)

### Files Requiring Updates (11 files)

**Core Enhancement**:
- .opencode/agent/subagents/status-sync-manager.md (+140 lines)

**Subagent Validation**:
- .opencode/agent/subagents/researcher.md (+36 lines)
- .opencode/agent/subagents/planner.md (+36 lines)
- .opencode/agent/subagents/implementer.md (+36 lines)
- .opencode/agent/subagents/lean-implementation-agent.md (+37 lines)

**Command Delegation**:
- .opencode/command/research.md (-20 lines)
- .opencode/command/plan.md (-20 lines)
- .opencode/command/revise.md (-20 lines)
- .opencode/command/implement.md (-20 lines)

**Documentation**:
- .opencode/context/core/workflows/command-lifecycle.md (+50 lines)
- .opencode/context/core/system/state-schema.md (+40 lines)

---

## Phase 1: Enhance status-sync-manager [COMPLETED]

**Started**: 2025-12-28
**Completed**: 2025-12-28

**Estimated Time**: 4 hours  
**Complexity**: Medium  
**Risk**: Medium (core coordination logic changes)

### Objectives

Enhance status-sync-manager with artifact validation protocol, plan metadata tracking, project state.json lazy creation, and plan version history tracking to provide comprehensive atomic update capabilities.

### Tasks

1. **Add Artifact Validation Protocol** (1 hour)
   - Define validation interface for subagents to implement
   - Add pre-commit validation step to two-phase commit
   - Validate artifact files exist on disk before linking
   - Validate artifact files are non-empty (size > 0)
   - Add validation failure handling with automatic rollback
   - Document validation protocol in status-sync-manager.md

2. **Add Plan Metadata Tracking** (1 hour)
   - Add plan_metadata field to state.json updates
   - Extract phase_count, estimated_hours, complexity from plan file
   - Store metadata in state.json during plan/revise operations
   - Update state-schema.md with plan_metadata field schema
   - Add metadata extraction helper function
   - Document metadata tracking in status-sync-manager.md

3. **Add Project state.json Lazy Creation** (1.5 hours)
   - Implement lazy creation on first artifact write
   - Use state-schema.md template for initial structure
   - Add project state.json to two-phase commit transaction
   - Create .opencode/specs/{task_number}_{slug}/state.json
   - Populate with project_name, project_number, type, phase, status
   - Add creation timestamp and last_updated timestamp
   - Document lazy creation policy in state-schema.md

4. **Add Plan Version History Tracking** (0.5 hours)
   - Add plan_versions array to state.json
   - Track version, path, created, reason for each plan
   - Append to array on /revise (preserve history)
   - Update plan_path to latest version
   - Document version history schema in state-schema.md
   - Add version history examples to status-sync-manager.md

### Deliverable

Enhanced status-sync-manager.md with 4 new capabilities:
- Artifact validation protocol (validate before commit)
- Plan metadata tracking (phase_count, estimated_hours, complexity)
- Project state.json lazy creation (on first artifact write)
- Plan version history tracking (plan_versions array)

**File Changes**:
- .opencode/agent/subagents/status-sync-manager.md (+140 lines)
  - New section: Artifact Validation Protocol (~35 lines)
  - New section: Plan Metadata Tracking (~30 lines)
  - New section: Project State Creation (~45 lines)
  - New section: Plan Version History (~30 lines)

### Acceptance Criteria

- [ ] Artifact validation protocol defined with clear interface
- [ ] Pre-commit validation step added to two-phase commit
- [ ] Artifact existence and non-empty checks implemented
- [ ] Plan metadata extraction implemented (phase_count, estimated_hours, complexity)
- [ ] Plan metadata stored in state.json during plan/revise operations
- [ ] Project state.json lazy creation implemented
- [ ] Project state.json added to two-phase commit transaction
- [ ] Project state.json template follows state-schema.md
- [ ] Plan version history tracking implemented
- [ ] plan_versions array appends on /revise (preserves history)
- [ ] All enhancements documented in status-sync-manager.md
- [ ] Usage examples added for each new capability
- [ ] No emojis in documentation

### Risks and Mitigation

**Risk**: Two-phase commit complexity increases with 4 new capabilities  
**Mitigation**: Implement incrementally, test each capability independently before integration

**Risk**: Project state.json creation may fail if directory doesn't exist  
**Mitigation**: Ensure lazy directory creation happens before state.json write, add error handling

**Risk**: Plan metadata extraction may fail if plan format varies  
**Mitigation**: Use robust parsing with fallback to defaults, document expected format

---

## Phase 2: Update Subagents with Validation [COMPLETED]

**Started**: 2025-12-28
**Completed**: 2025-12-28

**Estimated Time**: 2 hours  
**Complexity**: Low  
**Risk**: Low (isolated validation additions)

### Objectives

Add artifact validation to researcher, planner, implementer, and lean-implementation-agent subagents to validate artifacts before returning to commands, enabling status-sync-manager to guarantee artifact existence before linking.

### Tasks

1. **Update researcher.md with Artifact Validation** (0.5 hours)
   - Add validation step before returning (Step 6)
   - Validate research-001.md exists and is non-empty
   - Validate research-summary.md exists and is non-empty
   - Validate summary within token limit (<100 tokens, ~400 chars)
   - Return validation result in metadata
   - Add validation failure handling (return failed status)
   - Document validation requirements

2. **Update planner.md with Artifact Validation and Metadata Extraction** (0.5 hours)
   - Add validation step before returning (Step 6)
   - Validate implementation-NNN.md exists and is non-empty
   - Extract phase_count from plan file (count ### Phase headings)
   - Extract estimated_hours from plan metadata
   - Extract complexity from plan metadata (if present)
   - Return validation result + metadata in return object
   - Add validation failure handling (return failed status)
   - Document validation and metadata extraction requirements

3. **Update implementer.md with Artifact Validation** (0.5 hours)
   - Add validation step before returning (Step 6)
   - Validate implementation files exist (from artifacts array)
   - Validate implementation-summary-{date}.md exists and is non-empty
   - Validate summary within token limit (<100 tokens, ~400 chars)
   - Return validation result in metadata
   - Add validation failure handling (return failed status)
   - Document validation requirements

4. **Update lean-implementation-agent.md with Artifact Validation** (0.5 hours)
   - Add validation step before returning (Step 6)
   - Validate Lean files exist and compile (via lean-lsp-mcp if available)
   - Validate implementation-summary-{date}.md exists and is non-empty
   - Validate summary within token limit (<100 tokens, ~400 chars)
   - Return validation result in metadata
   - Add validation failure handling (return failed status)
   - Document validation requirements

### Deliverable

4 updated subagent files with artifact validation:
- .opencode/agent/subagents/researcher.md (+36 lines)
- .opencode/agent/subagents/planner.md (+36 lines)
- .opencode/agent/subagents/implementer.md (+36 lines)
- .opencode/agent/subagents/lean-implementation-agent.md (+37 lines)

**Validation Pattern** (consistent across all subagents):
```xml
<validation>
  Before returning (Step 6):
  - [ ] Verify all artifacts created successfully
  - [ ] Verify artifact files exist on disk
  - [ ] Verify artifact files are non-empty (size > 0)
  - [ ] Verify summary artifact within token limit (<100 tokens)
  - [ ] Extract metadata (if applicable: plan metadata)
  - [ ] Return validation result in metadata field
  
  If validation fails:
  - Log validation error with details
  - Return status: "failed"
  - Include error in errors array with type "validation_failed"
  - Recommendation: "Fix artifact creation and retry"
</validation>
```

### Acceptance Criteria

- [ ] researcher.md has artifact validation for research-001.md and research-summary.md
- [ ] planner.md has artifact validation for implementation-NNN.md
- [ ] planner.md extracts plan metadata (phase_count, estimated_hours, complexity)
- [ ] implementer.md has artifact validation for implementation files and summary
- [ ] lean-implementation-agent.md has artifact validation for Lean files and summary
- [ ] All subagents validate summary within token limit
- [ ] All subagents return validation result in metadata
- [ ] All subagents handle validation failure gracefully (return failed status)
- [ ] Validation pattern consistent across all 4 subagents
- [ ] Documentation explains validation requirements
- [ ] No emojis in subagent files

### Risks and Mitigation

**Risk**: Validation may break existing workflows if artifacts not created  
**Mitigation**: Research confirms all subagents already create required artifacts, validation just enforces

**Risk**: Plan metadata extraction may fail on non-standard plan formats  
**Mitigation**: Use robust parsing with fallback to defaults, log warnings for missing metadata

**Risk**: Token limit calculation may be imprecise  
**Mitigation**: Use character count approximation (100 tokens ≈ 400 characters), document conversion

---

## Phase 3: Update Commands to Delegate All Updates [COMPLETED]

**Started**: 2025-12-28
**Completed**: 2025-12-28

**Estimated Time**: 2 hours  
**Complexity**: Low  
**Risk**: Low (removing manual updates, delegating to status-sync-manager)

### Objectives

Remove manual TODO.md/state.json/plan file updates from all 4 workflow commands and delegate all updates to status-sync-manager, ensuring atomic updates across all tracking files.

### Tasks

1. **Update /research Command** (0.5 hours)
   - Remove manual artifact linking code (Stage 7 Postflight)
   - Pass artifact_links to status-sync-manager in update call
   - Add validation delegation: verify researcher returned validation success
   - Update documentation to reference status-sync-manager delegation
   - Verify git commit still includes all updated files
   - Net change: -20 lines (remove manual updates, add delegation)

2. **Update /plan Command** (0.5 hours)
   - Remove manual plan linking code (Stage 7 Postflight)
   - Pass plan_path and plan_metadata to status-sync-manager in update call
   - Add validation delegation: verify planner returned validation success + metadata
   - Update documentation to reference status-sync-manager delegation
   - Verify git commit still includes all updated files
   - Net change: -20 lines (remove manual updates, add delegation)

3. **Update /revise Command** (0.5 hours)
   - Remove manual plan link update code (Stage 7 Postflight)
   - Pass new plan_path, plan_version, and revision_reason to status-sync-manager
   - Add validation delegation: verify planner returned validation success + metadata
   - Update documentation to reference status-sync-manager delegation
   - Verify git commit still includes all updated files
   - Net change: -20 lines (remove manual updates, add delegation)

4. **Update /implement Command** (0.5 hours)
   - Remove manual plan phase update code (Stage 1 Preflight, Stage 7 Postflight)
   - Pass plan_path and phase_statuses to status-sync-manager in update calls
   - Add validation delegation: verify implementer/lean-implementation-agent returned validation success
   - Update documentation to reference status-sync-manager delegation
   - Verify git commit still includes all updated files (including plan file)
   - Net change: -20 lines (remove manual updates, add delegation)

### Deliverable

4 updated command files with delegated updates:
- .opencode/command/research.md (-20 lines)
- .opencode/command/plan.md (-20 lines)
- .opencode/command/revise.md (-20 lines)
- .opencode/command/implement.md (-20 lines)

**Total reduction**: 80 lines of manual update code removed

**Delegation Pattern** (consistent across all commands):
```xml
<stage id="7" name="Postflight">
  <status_update>
    Delegate to status-sync-manager:
      - task_number: {number}
      - new_status: {status}
      - timestamp: {ISO8601}
      - session_id: {session_id}
      - artifact_links: {validated_artifacts}  # From subagent validation
      - plan_metadata: {metadata}              # From planner (if applicable)
      - plan_version: {version}                # From revise (if applicable)
      - phase_statuses: {statuses}             # From implement (if applicable)
    
    status-sync-manager performs two-phase commit:
      - Phase 1: Prepare, validate, backup
      - Phase 2: Write all files or rollback all
    
    Atomicity guaranteed across:
      - TODO.md
      - state.json
      - project state.json (lazy created if needed)
      - plan file (if applicable)
  </status_update>
</stage>
```

### Acceptance Criteria

- [ ] /research command delegates artifact linking to status-sync-manager
- [ ] /plan command delegates plan linking and metadata to status-sync-manager
- [ ] /revise command delegates plan version update to status-sync-manager
- [ ] /implement command delegates plan phase updates to status-sync-manager
- [ ] All commands verify subagent validation success before delegating
- [ ] All commands pass validated artifacts to status-sync-manager
- [ ] All manual TODO.md/state.json/plan file updates removed
- [ ] Git commits still include all updated files
- [ ] Documentation updated to reference delegation pattern
- [ ] Delegation pattern consistent across all 4 commands
- [ ] No emojis in command files
- [ ] All existing functionality preserved

### Risks and Mitigation

**Risk**: Delegation may miss command-specific update logic  
**Mitigation**: Careful review of manual update code before removal, preserve any command-specific logic

**Risk**: Git commits may not include all files if delegation changes file list  
**Mitigation**: Verify git-workflow-manager still receives complete file list from status-sync-manager

**Risk**: Validation failures may break workflows  
**Mitigation**: Ensure validation failures return clear error messages with recovery instructions

---

## Phase 4: Testing and Documentation [COMPLETED]

**Started**: 2025-12-28
**Completed**: 2025-12-28

**Estimated Time**: 2 hours  
**Complexity**: Medium  
**Risk**: Medium (may reveal edge cases)

### Objectives

Validate all 4 commands work correctly with enhanced status-sync-manager, verify atomicity guarantees, test validation failures, and update documentation with new update protocol.

### Tasks

1. **Integration Testing** (1 hour)
   - Test /research → /plan → /implement workflow end-to-end
   - Verify all tracking files updated atomically (TODO.md, state.json, project state.json)
   - Verify artifact validation catches missing files
   - Verify plan metadata tracked correctly in state.json
   - Test /revise workflow and verify plan version history
   - Test failure scenarios (artifact missing, validation failure)
   - Verify atomicity: rollback on failure (no partial updates)
   - Test resume logic with phase_statuses from state.json

2. **Documentation Updates** (1 hour)
   - Update command-lifecycle.md Stage 7 with update protocol (+50 lines)
     - Add "Update Procedures" subsection
     - Document validation protocol
     - Document atomicity guarantees
     - Add delegation pattern examples
   - Update state-schema.md with new field schemas (+40 lines)
     - Add plan_metadata field schema
     - Add plan_versions array schema
     - Add project state.json creation guidance
     - Add field examples
   - Update status-sync-manager.md with usage examples (+60 lines already in Phase 1)
   - Verify all cross-references correct

### Test Scenarios

**Scenario 1: End-to-End Workflow with Atomicity**
```
/research 216
  → Researcher validates artifacts
  → status-sync-manager creates project state.json
  → TODO.md, state.json, project state.json updated atomically
  → Verify all 3 files consistent

/plan 216
  → Planner validates plan, extracts metadata
  → status-sync-manager stores plan_metadata in state.json
  → TODO.md, state.json, project state.json updated atomically
  → Verify plan_metadata present in state.json

/implement 216
  → Implementer validates implementation artifacts
  → status-sync-manager updates phase_statuses
  → TODO.md, state.json, project state.json, plan file updated atomically
  → Verify all 4 files consistent
```

**Scenario 2: Validation Failure Handling**
```
/research 999 (simulate artifact creation failure)
  → Researcher validation fails (artifact missing)
  → status-sync-manager aborts update (no status change)
  → TODO.md, state.json unchanged
  → Verify no partial updates

/plan 216 (simulate metadata extraction failure)
  → Planner validation succeeds but metadata extraction fails
  → status-sync-manager uses default metadata
  → TODO.md, state.json updated with defaults
  → Verify graceful degradation
```

**Scenario 3: Plan Version History**
```
/revise 216 (first revision)
  → status-sync-manager appends to plan_versions array
  → plan_path updated to new version
  → Verify plan_versions has 2 entries (original + revision)

/revise 216 (second revision)
  → status-sync-manager appends to plan_versions array
  → plan_path updated to newest version
  → Verify plan_versions has 3 entries
```

**Scenario 4: Rollback on Failure**
```
/implement 216 (simulate state.json write failure)
  → status-sync-manager prepares updates
  → state.json write fails
  → status-sync-manager rolls back TODO.md, project state.json, plan file
  → Verify all files restored to pre-update state
  → Verify no partial updates
```

### Deliverable

**Test Validation Report** documenting:
- All 4 commands tested successfully
- Atomicity verified across all tracking files
- Validation failures handled correctly
- Plan version history working
- Rollback working on failures
- No functionality regressions

**Documentation Updates**:
- .opencode/context/core/workflows/command-lifecycle.md (+50 lines)
- .opencode/context/core/system/state-schema.md (+40 lines)

### Acceptance Criteria

- [ ] /research tested with artifact validation
- [ ] /plan tested with metadata extraction
- [ ] /revise tested with version history
- [ ] /implement tested with phase status updates
- [ ] Atomicity verified: all files updated or none
- [ ] Validation failures abort updates correctly
- [ ] Rollback verified on write failures
- [ ] Plan version history tracked correctly
- [ ] Project state.json created lazily on first artifact
- [ ] command-lifecycle.md updated with update protocol
- [ ] state-schema.md updated with new field schemas
- [ ] All cross-references verified correct
- [ ] Test validation report created
- [ ] No functionality regressions identified

### Risks and Mitigation

**Risk**: Testing may reveal edge cases not covered in design  
**Mitigation**: Document all edge cases found, update implementation if needed

**Risk**: Rollback may not restore all files correctly  
**Mitigation**: Test rollback thoroughly with multiple failure scenarios

**Risk**: Documentation may become too verbose  
**Mitigation**: Use concise examples and tables, reference existing standards

---

## Success Criteria

### Overall Goals

1. **Atomicity Guaranteed**: All tracking files updated atomically via status-sync-manager two-phase commit
2. **Validation Enforced**: Artifacts validated before linking, preventing broken links
3. **Metadata Tracked**: Plan metadata (phase_count, estimated_hours, complexity) stored in state.json
4. **Version History**: Plan version history tracked in plan_versions array
5. **Project State Created**: Project state.json created lazily on first artifact write
6. **Standards Compliance**: All updates follow status-markers.md, state-schema.md, artifact-management.md
7. **No Regressions**: All existing functionality preserved

### Phase Completion

- [ ] Phase 1: status-sync-manager enhanced with 4 new capabilities (+140 lines)
- [ ] Phase 2: All 4 subagents have artifact validation (+145 lines)
- [ ] Phase 3: All 4 commands delegate updates to status-sync-manager (-80 lines)
- [ ] Phase 4: All commands tested, documentation updated (+90 lines)

### Quality Metrics

- [ ] Atomicity coverage: 100% (all updates via status-sync-manager)
- [ ] Validation coverage: 100% (all artifacts validated before linking)
- [ ] Metadata tracking: 100% (plan metadata stored in state.json)
- [ ] Version history: 100% (all plan revisions tracked)
- [ ] Project state creation: 100% (created on first artifact write)
- [ ] Test coverage: All 4 commands tested with multiple scenarios
- [ ] Documentation quality: All sections complete, no emojis, clear examples

### Deliverables

1. .opencode/agent/subagents/status-sync-manager.md (enhanced, +140 lines)
2. .opencode/agent/subagents/researcher.md (validation added, +36 lines)
3. .opencode/agent/subagents/planner.md (validation + metadata, +36 lines)
4. .opencode/agent/subagents/implementer.md (validation added, +36 lines)
5. .opencode/agent/subagents/lean-implementation-agent.md (validation added, +37 lines)
6. .opencode/command/research.md (delegation, -20 lines)
7. .opencode/command/plan.md (delegation, -20 lines)
8. .opencode/command/revise.md (delegation, -20 lines)
9. .opencode/command/implement.md (delegation, -20 lines)
10. .opencode/context/core/workflows/command-lifecycle.md (update protocol, +50 lines)
11. .opencode/context/core/system/state-schema.md (field schemas, +40 lines)
12. Test validation report

**Net Change**: +205 lines total (285 added - 80 removed)

---

## Risk Assessment

### High Risks

None identified

### Medium Risks

**Risk 1: Two-phase commit complexity increases with new capabilities**
- **Impact**: May introduce bugs in atomic update logic
- **Probability**: Medium (adding 4 new capabilities to existing logic)
- **Mitigation**: Implement incrementally, test each capability independently
- **Contingency**: Rollback to current implementation if atomicity breaks

**Risk 2: Testing may reveal edge cases in validation logic**
- **Impact**: May require additional fixes beyond planned work
- **Probability**: Medium (validation is new functionality)
- **Mitigation**: Comprehensive test scenarios covering all validation paths
- **Contingency**: Add Phase 5 for fixes if needed (budget 2 additional hours)

### Low Risks

**Risk 3: Plan metadata extraction may fail on non-standard formats**
- **Impact**: Metadata may be missing or incorrect in state.json
- **Probability**: Low (plan.md standard is well-defined)
- **Mitigation**: Use robust parsing with fallback to defaults
- **Contingency**: Log warnings for missing metadata, continue with defaults

**Risk 4: Project state.json creation may fail if directory doesn't exist**
- **Impact**: Lazy creation may fail, breaking atomic update
- **Probability**: Low (lazy directory creation already implemented)
- **Mitigation**: Ensure directory creation before state.json write
- **Contingency**: Add explicit directory creation check with error handling

**Risk 5: Validation failures may break existing workflows**
- **Impact**: Commands may fail where they previously succeeded
- **Probability**: Low (research confirms artifacts already created)
- **Mitigation**: Verify all subagents create required artifacts before adding validation
- **Contingency**: Make validation warnings instead of errors if needed

---

## Implementation Notes

### Key Decisions

1. **Enhance existing status-sync-manager, not create new agent**: Leverages existing two-phase commit, avoids duplication
2. **Distribute validation to subagents, not centralize**: Subagents know their artifacts best, clearer separation of concerns
3. **Use hybrid architecture (coordination + validation)**: Lowest complexity (+205 lines), full atomicity, best extensibility
4. **Track plan metadata in state.json**: Enables querying without parsing plan files
5. **Track plan version history in array**: Preserves evolution, enables reconstruction
6. **Create project state.json lazily**: Follows artifact-management.md lazy creation policy
7. **Remove all manual updates from commands**: Guarantees atomicity, single source of truth

### Design Principles

1. **Atomicity First**: All updates via status-sync-manager two-phase commit
2. **Validation Before Commit**: Artifacts validated before linking, preventing broken links
3. **Single Source of Truth**: status-sync-manager coordinates all updates
4. **Clear Separation**: Coordination (status-sync-manager) vs Validation (subagents)
5. **Graceful Degradation**: Validation failures abort updates, clear error messages
6. **Extensibility**: New artifact types add validation, not coordination logic

### Integration Points

**With Existing Standards**:
- status-markers.md: Status transition validation
- state-schema.md: State file schemas, field naming conventions
- artifact-management.md: Lazy directory creation, artifact requirements
- command-lifecycle.md: 8-stage command pattern, postflight procedures
- subagent-return-format.md: Standardized return format with validation results

**With Commands**:
- Commands delegate all updates to status-sync-manager
- Commands verify subagent validation success before delegating
- Commands pass validated artifacts and metadata to status-sync-manager

**With Subagents**:
- Subagents validate artifacts before returning
- Subagents extract metadata (planner extracts plan metadata)
- Subagents return validation results in metadata field

### Future Enhancements

1. **Add validation for all artifact types**: Extend validation to research reports, implementation files
2. **Add state.json schema validation**: Validate state.json updates match state-schema.md
3. **Add plan file consistency validation**: Verify plan phase count matches expected phases
4. **Create update monitoring dashboard**: Track update success/failure rates, identify issues
5. **Add automated rollback testing**: Verify rollback works correctly for all failure scenarios

---

## References

### Research Artifacts

- Main Report: .opencode/specs/216_improve_task_tracking_updates/reports/research-001.md
- Summary: .opencode/specs/216_improve_task_tracking_updates/summaries/research-summary.md

### Files to be Modified

**Core Enhancement**:
- .opencode/agent/subagents/status-sync-manager.md

**Subagent Validation**:
- .opencode/agent/subagents/researcher.md
- .opencode/agent/subagents/planner.md
- .opencode/agent/subagents/implementer.md
- .opencode/agent/subagents/lean-implementation-agent.md

**Command Delegation**:
- .opencode/command/research.md
- .opencode/command/plan.md
- .opencode/command/revise.md
- .opencode/command/implement.md

**Documentation**:
- .opencode/context/core/workflows/command-lifecycle.md
- .opencode/context/core/system/state-schema.md

### Related Standards

- .opencode/context/core/standards/status-markers.md
- .opencode/context/core/system/state-schema.md
- .opencode/context/core/system/artifact-management.md
- .opencode/context/core/workflows/command-lifecycle.md
- .opencode/context/core/standards/subagent-return-format.md
- .opencode/context/core/system/git-commits.md

### Related Tasks

- Task 211: Standardize command lifecycle procedures (completed, created command-lifecycle.md)
- Task 210: Fix Lean subagents to follow standards (researched, identified compliance gaps)
- Task 191: Fix subagent delegation hang (created subagent-return-format.md)
- Task 169: Context window protection (created summary requirements)
- Task 156: Targeted git commits (created git-commits.md)
