# Research Report: Fix lean-research-agent to Delegate Status Updates

**Task**: 291 - Fix lean-research-agent to delegate status updates to status-sync-manager instead of direct file manipulation  
**Started**: 2026-01-04  
**Completed**: 2026-01-04  
**Effort**: 2.5 hours (estimated)  
**Priority**: High  
**Dependencies**: Task 290 (researched)  
**Sources/Inputs**:
- `.opencode/agent/subagents/lean-research-agent.md` (lines 641-750)
- `.opencode/agent/subagents/researcher.md` (lines 331-379)
- Task 290 research report
- `.opencode/context/core/standards/subagent-return-format.md`

**Artifacts**:
- `.opencode/specs/291_fix_lean_research_agent_delegate_status_updates/reports/research-001.md`

**Standards**: status-markers.md, artifact-management.md, tasks.md, report.md, delegation.md

---

## Executive Summary

Root cause confirmed: lean-research-agent.md step_6 (lines 651-662) directly manipulates TODO.md and state.json files instead of delegating to status-sync-manager and git-workflow-manager like researcher.md does. This bypasses atomic updates and causes status synchronization failures. The fix requires replacing direct file manipulation with proper delegation pattern matching researcher.md step_4_postflight implementation.

Evidence from Task 290 demonstrates the failure: `/research 290` created research report successfully but status remained `[NOT STARTED]`, no artifact link was added to TODO.md, no state.json update occurred, and no git commit was created.

---

## Context & Scope

### Problem Statement

Task 290 identified that `/research 290` (a Lean research task) failed to update status markers despite successfully creating research artifacts. The research report was created, but:

1. TODO.md status remained `[NOT STARTED]` instead of updating to `[RESEARCHED]`
2. No artifact link was added to TODO.md
3. state.json was not updated
4. No git commit was created

### Root Cause Hypothesis

Task 291 description identifies the root cause: lean-research-agent.md directly manipulates TODO.md and state.json files (lines 651-662) instead of delegating to status-sync-manager and git-workflow-manager like researcher.md does.

### Scope

This research focuses on:
1. Confirming the root cause by comparing lean-research-agent.md and researcher.md
2. Identifying exact code locations requiring changes
3. Documenting the delegation pattern to implement
4. Estimating effort for the fix

---

## Key Findings

### Finding 1: Direct File Manipulation in lean-research-agent.md

**Location**: `.opencode/agent/subagents/lean-research-agent.md` lines 651-662

**Evidence**:
```xml
<step_6>
  <action>Validate artifact, update status markers, update state, and return standardized result</action>
  <process>
    2. Update TODO.md status marker:
       a. Find task entry in .opencode/specs/TODO.md
       b. Change status from [RESEARCHING] to [RESEARCHED]
       c. Add **Completed**: YYYY-MM-DD timestamp
       d. Add **Research Artifacts**: section with links:
          - Main Report: .opencode/specs/{task_number}_{topic}/reports/research-001.md
          - Summary: .opencode/specs/{task_number}_{topic}/summaries/research-summary.md
    3. Update state.json:
       a. Update .opencode/specs/state.json active_projects array
       b. Add/update project entry with status "researched"
       c. Add artifacts array with research report and summary paths
       d. Set created_at and updated_at timestamps (ISO 8601 format)
  </process>
</step_6>
```

**Analysis**: The specification instructs the agent to directly update TODO.md and state.json files. This is procedural documentation, not delegation. The agent is expected to perform file manipulation itself rather than delegating to status-sync-manager.

### Finding 2: Delegation Pattern in researcher.md

**Location**: `.opencode/agent/subagents/researcher.md` lines 331-379

**Evidence**:
```xml
<step_4_postflight>
  <action>Postflight: Update status to [RESEARCHED], link report, create git commit</action>
  <process>
    1. Generate completion timestamp: $(date -I)
    2. Invoke status-sync-manager to mark [RESEARCHED]:
       a. Prepare delegation context:
          - task_number: {number}
          - new_status: "researched"
          - timestamp: {date}
          - session_id: {session_id}
          - delegation_depth: {depth + 1}
          - delegation_path: [...delegation_path, "status-sync-manager"]
          - validated_artifacts: [{type, path, summary}]
       b. Invoke status-sync-manager with timeout (60s)
       c. Validate return status == "completed"
       d. Verify files_updated includes ["TODO.md", "state.json"]
       e. Verify artifact linked in TODO.md
       f. If status update fails: Log error but continue (artifact exists)
    3. Invoke git-workflow-manager to create commit:
       a. Prepare delegation context:
          - scope_files: [
              "{research_report_path}",
              ".opencode/specs/TODO.md",
              ".opencode/specs/state.json",
              ".opencode/specs/{task_number}_{slug}/state.json"
            ]
          - message_template: "task {number}: research completed"
          - task_context: {
              task_number: {number},
              description: "research completed"
            }
          - session_id: {session_id}
          - delegation_depth: {depth + 1}
          - delegation_path: [...delegation_path, "git-workflow-manager"]
       b. Invoke git-workflow-manager with timeout (120s)
       c. Validate return status (completed or failed)
       d. If status == "completed": Log commit hash
       e. If status == "failed": Log warning (non-critical, don't fail research)
    4. Log postflight completion
  </process>
</step_4_postflight>
```

**Analysis**: researcher.md properly delegates to status-sync-manager and git-workflow-manager. This ensures:
- Atomic status updates across TODO.md and state.json
- Proper artifact linking
- Git commit creation
- Error handling and validation

### Finding 3: Architectural Inconsistency

**Comparison**:

| Aspect | lean-research-agent.md | researcher.md |
|--------|------------------------|---------------|
| Status update method | Direct file manipulation | Delegation to status-sync-manager |
| Git commit | No git commit | Delegation to git-workflow-manager |
| Artifact linking | Manual TODO.md editing | Handled by status-sync-manager |
| Error handling | None specified | Validation and error logging |
| Atomicity | No guarantee | Atomic via status-sync-manager |

**Root Cause**: lean-research-agent.md was not updated when Task 275 and Task 283 standardized the delegation pattern across workflow subagents. It still uses the old direct manipulation pattern.

### Finding 4: Summary Artifact Requirement

**Location**: `.opencode/agent/subagents/lean-research-agent.md` lines 647-649, 664, 686-688, 764-766

**Evidence**:
```xml
c. Verify summary artifact created (summaries/research-summary.md)
d. Verify summary artifact is <100 tokens (~400 chars)
e. Verify summary artifact is 3-5 sentences

5. List research report artifact AND summary artifact
```

**Analysis**: lean-research-agent.md requires creation of a separate summary artifact file (`summaries/research-summary.md`). This contradicts the standard workflow where:
- researcher.md creates ONLY the research report (`reports/research-001.md`)
- Summary is metadata in the return object, NOT a separate file
- This is per subagent-return-format.md: summary field is <100 tokens in JSON return

**Impact**: This requirement adds unnecessary complexity and violates the single-artifact principle for research tasks.

---

## Detailed Analysis

### Phase 1: Replace Direct TODO.md Updates with status-sync-manager Delegation

**Current Implementation** (lines 651-657):
```xml
2. Update TODO.md status marker:
   a. Find task entry in .opencode/specs/TODO.md
   b. Change status from [RESEARCHING] to [RESEARCHED]
   c. Add **Completed**: YYYY-MM-DD timestamp
   d. Add **Research Artifacts**: section with links:
      - Main Report: .opencode/specs/{task_number}_{topic}/reports/research-001.md
      - Summary: .opencode/specs/{task_number}_{topic}/summaries/research-summary.md
```

**Required Change**:
Replace with delegation pattern from researcher.md lines 335-348:
```xml
2. Invoke status-sync-manager to mark [RESEARCHED]:
   a. Prepare delegation context:
      - task_number: {number}
      - new_status: "researched"
      - timestamp: {date}
      - session_id: {session_id}
      - delegation_depth: {depth + 1}
      - delegation_path: [...delegation_path, "status-sync-manager"]
      - validated_artifacts: [{type, path, summary}]
   b. Invoke status-sync-manager with timeout (60s)
   c. Validate return status == "completed"
   d. Verify files_updated includes ["TODO.md", "state.json"]
   e. Verify artifact linked in TODO.md
   f. If status update fails: Log error but continue (artifact exists)
```

**Benefits**:
- Atomic updates to TODO.md and state.json
- Automatic artifact linking
- Proper error handling
- Consistent with other workflow subagents

### Phase 2: Replace Direct state.json Updates with status-sync-manager Delegation

**Current Implementation** (lines 658-662):
```xml
3. Update state.json:
   a. Update .opencode/specs/state.json active_projects array
   b. Add/update project entry with status "researched"
   c. Add artifacts array with research report and summary paths
   d. Set created_at and updated_at timestamps (ISO 8601 format)
```

**Required Change**:
Remove this section entirely. status-sync-manager handles both TODO.md and state.json atomically (as invoked in Phase 1).

**Benefits**:
- Eliminates duplicate logic
- Ensures consistency between TODO.md and state.json
- Reduces complexity

### Phase 3: Add git-workflow-manager Delegation

**Current Implementation**: No git commit creation

**Required Change**:
Add delegation pattern from researcher.md lines 349-368:
```xml
3. Invoke git-workflow-manager to create commit:
   a. Prepare delegation context:
      - scope_files: [
          "{research_report_path}",
          ".opencode/specs/TODO.md",
          ".opencode/specs/state.json",
          ".opencode/specs/{task_number}_{slug}/state.json"
        ]
      - message_template: "task {number}: research completed"
      - task_context: {
          task_number: {number},
          description: "research completed"
        }
      - session_id: {session_id}
      - delegation_depth: {depth + 1}
      - delegation_path: [...delegation_path, "git-workflow-manager"]
   b. Invoke git-workflow-manager with timeout (120s)
   c. Validate return status (completed or failed)
   d. If status == "completed": Log commit hash
   e. If status == "failed": Log warning (non-critical, don't fail research)
```

**Benefits**:
- Automatic git commit creation
- Consistent commit messages
- Proper error handling (non-critical failure)

### Phase 4: Update step_6 Documentation

**Current Implementation**: step_6 documents direct file manipulation

**Required Change**:
Update step_6 to reflect delegation pattern:
- Rename to `step_6_postflight` for consistency
- Update action description
- Update process documentation
- Remove `<status_marker_update>` and `<state_update>` sections (handled by status-sync-manager)
- Add `<git_failure_handling>` section

### Phase 5: Remove Summary Artifact Requirement

**Current Implementation** (lines 647-649, 664, 686-688, 764-766):
```xml
c. Verify summary artifact created (summaries/research-summary.md)
d. Verify summary artifact is <100 tokens (~400 chars)
e. Verify summary artifact is 3-5 sentences

5. List research report artifact AND summary artifact
```

**Required Change**:
Remove all references to summary artifact:
- Line 647-649: Remove summary artifact validation
- Line 664: Remove "List research report artifact AND summary artifact"
- Line 686-688: Remove summary artifact from example
- Line 764-766: Remove summary artifact from return format

**Rationale**:
- researcher.md creates ONLY research report (reports/research-001.md)
- Summary is metadata in JSON return object, NOT a separate file
- This aligns with subagent-return-format.md specification
- Reduces complexity and artifact count

---

## Code Examples

### Before (lean-research-agent.md lines 651-662)

```xml
2. Update TODO.md status marker:
   a. Find task entry in .opencode/specs/TODO.md
   b. Change status from [RESEARCHING] to [RESEARCHED]
   c. Add **Completed**: YYYY-MM-DD timestamp
   d. Add **Research Artifacts**: section with links:
      - Main Report: .opencode/specs/{task_number}_{topic}/reports/research-001.md
      - Summary: .opencode/specs/{task_number}_{topic}/summaries/research-summary.md
3. Update state.json:
   a. Update .opencode/specs/state.json active_projects array
   b. Add/update project entry with status "researched"
   c. Add artifacts array with research report and summary paths
   d. Set created_at and updated_at timestamps (ISO 8601 format)
```

### After (matching researcher.md pattern)

```xml
2. Invoke status-sync-manager to mark [RESEARCHED]:
   a. Prepare delegation context:
      - task_number: {number}
      - new_status: "researched"
      - timestamp: {date}
      - session_id: {session_id}
      - delegation_depth: {depth + 1}
      - delegation_path: [...delegation_path, "status-sync-manager"]
      - validated_artifacts: [{type, path, summary}]
   b. Invoke status-sync-manager with timeout (60s)
   c. Validate return status == "completed"
   d. Verify files_updated includes ["TODO.md", "state.json"]
   e. Verify artifact linked in TODO.md
   f. If status update fails: Log error but continue (artifact exists)
3. Invoke git-workflow-manager to create commit:
   a. Prepare delegation context:
      - scope_files: [
          "{research_report_path}",
          ".opencode/specs/TODO.md",
          ".opencode/specs/state.json",
          ".opencode/specs/{task_number}_{slug}/state.json"
        ]
      - message_template: "task {number}: research completed"
      - task_context: {
          task_number: {number},
          description: "research completed"
        }
      - session_id: {session_id}
      - delegation_depth: {depth + 1}
      - delegation_path: [...delegation_path, "git-workflow-manager"]
   b. Invoke git-workflow-manager with timeout (120s)
   c. Validate return status (completed or failed)
   d. If status == "completed": Log commit hash
   e. If status == "failed": Log warning (non-critical, don't fail research)
4. Log postflight completion
```

---

## Decisions

### Decision 1: Use Exact researcher.md Pattern

**Decision**: Copy delegation pattern exactly from researcher.md step_4_postflight to lean-research-agent.md step_6.

**Rationale**:
- Proven pattern (researcher.md works correctly)
- Maintains consistency across workflow subagents
- Reduces risk of introducing new bugs
- Simplifies maintenance

**Alternatives Considered**:
- Create custom delegation pattern for Lean research
- Rejected: Adds unnecessary complexity and divergence

### Decision 2: Remove Summary Artifact Requirement

**Decision**: Remove all references to summary artifact creation and validation.

**Rationale**:
- Aligns with researcher.md behavior (single artifact)
- Follows subagent-return-format.md specification
- Reduces complexity
- Summary belongs in JSON return object, not separate file

**Alternatives Considered**:
- Keep summary artifact for Lean research tasks
- Rejected: Violates standard workflow and adds unnecessary complexity

### Decision 3: Rename step_6 to step_6_postflight

**Decision**: Rename `<step_6>` to `<step_6_postflight>` for consistency with researcher.md.

**Rationale**:
- Matches researcher.md naming convention
- Clarifies purpose (postflight operations)
- Improves consistency across subagents

**Alternatives Considered**:
- Keep step_6 name
- Rejected: Inconsistent with researcher.md and less descriptive

---

## Recommendations

### Immediate Actions

1. **Implement Phase 1-3**: Replace direct file manipulation with delegation pattern
   - Update lean-research-agent.md lines 651-662
   - Add status-sync-manager delegation
   - Add git-workflow-manager delegation
   - Estimated effort: 1.5 hours

2. **Implement Phase 4**: Update step_6 documentation
   - Rename to step_6_postflight
   - Update process documentation
   - Remove obsolete sections
   - Estimated effort: 30 minutes

3. **Implement Phase 5**: Remove summary artifact requirement
   - Remove validation checks (lines 647-649)
   - Remove artifact listing (line 664)
   - Remove example references (lines 686-688, 764-766)
   - Estimated effort: 30 minutes

### Testing Strategy

1. **Functional Test**: Run `/research {lean_task}` on a Lean task
   - Verify research report created
   - Verify TODO.md status updated to [RESEARCHED]
   - Verify state.json updated
   - Verify artifact link added to TODO.md
   - Verify git commit created

2. **Regression Test**: Verify existing Lean research tasks still work
   - Test with Task 259 (automation_tactics)
   - Verify no breaking changes

3. **Comparison Test**: Compare behavior with researcher.md
   - Run `/research {general_task}` (uses researcher.md)
   - Run `/research {lean_task}` (uses lean-research-agent.md)
   - Verify identical status update behavior

### Follow-up Tasks

1. **Task 285**: Audit and fix status update behavior in other Lean subagents
   - lean-planner.md
   - lean-implementation-agent.md
   - Ensure consistent delegation pattern

2. **Documentation Update**: Update delegation.md to document standard pattern
   - Add section on status-sync-manager delegation
   - Add section on git-workflow-manager delegation
   - Provide code examples

---

## Risks & Mitigations

### Risk 1: Breaking Existing Lean Research Tasks

**Likelihood**: Low  
**Impact**: Medium  
**Mitigation**:
- Test with existing Lean task (Task 259)
- Verify backward compatibility
- Keep backup of original lean-research-agent.md

### Risk 2: status-sync-manager Delegation Failure

**Likelihood**: Low  
**Impact**: High  
**Mitigation**:
- Add error handling (log error but continue)
- Verify status-sync-manager is working correctly
- Test delegation with simple task first

### Risk 3: git-workflow-manager Delegation Failure

**Likelihood**: Low  
**Impact**: Low (non-critical)  
**Mitigation**:
- Mark git failure as non-critical (don't fail research)
- Log warning for manual recovery
- Document manual commit process

---

## Appendix: Sources and Citations

### Primary Sources

1. **lean-research-agent.md**: `.opencode/agent/subagents/lean-research-agent.md`
   - Lines 641-750: step_6 implementation
   - Lines 651-662: Direct file manipulation code

2. **researcher.md**: `.opencode/agent/subagents/researcher.md`
   - Lines 331-379: step_4_postflight implementation
   - Delegation pattern reference

3. **Task 290 Research Report**: `.opencode/specs/290_fix_lean_research_agent_preflight_status_updates_and_artifact_linking/reports/research-001.md`
   - Evidence of status update failure
   - Root cause analysis

4. **subagent-return-format.md**: `.opencode/context/core/standards/subagent-return-format.md`
   - Summary field specification (<100 tokens)
   - Artifact format requirements

### Related Tasks

- **Task 275**: Fix workflow status updates (completed)
  - Standardized two-phase status pattern
  - Updated planner.md and implementer.md

- **Task 283**: Fix systematic status synchronization failure (completed)
  - Standardized stage naming (step_0_preflight, step_4_postflight)
  - Updated researcher.md

- **Task 285**: Audit and fix status update behavior (planned)
  - Extends Task 283 fix to Lean subagents
  - Related to this task

- **Task 290**: Fix lean-research-agent preflight status updates (researched)
  - Identified status update failure
  - Led to creation of Task 291

### Standards Referenced

- **status-markers.md**: Status marker format and transitions
- **artifact-management.md**: Artifact creation and validation
- **tasks.md**: Task structure and metadata
- **report.md**: Research report format
- **delegation.md**: Delegation patterns and context passing
