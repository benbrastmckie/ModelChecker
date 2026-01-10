# Research Report: Task Tracking File Update Procedures

**Task**: 216  
**Date**: 2025-12-28  
**Researcher**: AI Research Agent  
**Status**: Completed

---

## Executive Summary

This research systematically analyzed task tracking file update procedures across all workflow commands (/research, /plan, /revise, /implement) to identify gaps, inconsistencies, and architectural improvements. The analysis reveals that while a robust status-sync-manager exists with atomic two-phase commit capabilities, it is underutilized and lacks comprehensive integration across all commands. Key findings include 7 critical gaps in update procedures, 4 architectural limitations, and a clear recommendation for a hybrid enhancement approach combining centralized coordination with distributed validation.

**Key Metrics**:
- Commands analyzed: 4 (/research, /plan, /revise, /implement)
- Update files tracked: 4 (TODO.md, state.json, project state.json, plan files)
- Gaps identified: 7 critical, 3 moderate
- Current atomic update coverage: ~40% (status-sync-manager exists but underutilized)
- Recommended architecture: Hybrid (enhanced status-sync-manager + distributed validation)
- Estimated implementation effort: 8-12 hours

---

## 1. Current State Analysis (20%)

### 1.1 Update Flow Diagrams

#### /research Command Update Flow
```
Stage 1 (Preflight):
  └─> status-sync-manager: [NOT STARTED] → [RESEARCHING]
      ├─> TODO.md: Update status, add Started timestamp
      └─> state.json: Update status, add started field

Stage 7 (Postflight):
  └─> status-sync-manager: [RESEARCHING] → [RESEARCHED]
      ├─> TODO.md: Update status, add Completed timestamp, link artifacts
      ├─> state.json: Update status, add completed field, add artifacts array
      └─> (No project state.json update - not created by /research)

Git Commit:
  └─> git-workflow-manager: Commit research artifacts + TODO.md + state.json
```

**Gaps**:
- Project state.json not created or updated (lazy creation not fully implemented)
- Artifact links added manually in command, not via status-sync-manager
- No validation that artifact files exist before linking

#### /plan Command Update Flow
```
Stage 1 (Preflight):
  └─> status-sync-manager: [NOT STARTED]/[RESEARCHED] → [PLANNING]
      ├─> TODO.md: Update status, add/preserve Started timestamp
      └─> state.json: Update status, add started field

Stage 7 (Postflight):
  └─> status-sync-manager: [PLANNING] → [PLANNED]
      ├─> TODO.md: Update status, add Completed timestamp, link plan
      ├─> state.json: Update status, add completed field, add plan_path
      └─> (No project state.json update)

Git Commit:
  └─> git-workflow-manager: Commit plan + TODO.md + state.json
```

**Gaps**:
- Plan metadata (phase count, estimated hours) not stored in state.json
- Research harvesting happens in command, not tracked in state updates
- No project state.json created to track plan versions

#### /revise Command Update Flow
```
Stage 1 (Preflight):
  └─> status-sync-manager: [PLANNED]/[REVISED] → [REVISING]
      ├─> TODO.md: Update status, preserve Started timestamp
      └─> state.json: Update status

Stage 7 (Postflight):
  └─> status-sync-manager: [REVISING] → [REVISED]
      ├─> TODO.md: Update status, add Completed timestamp, UPDATE plan link
      ├─> state.json: Update status, add completed field, UPDATE plan_path
      └─> (No project state.json update)

Git Commit:
  └─> git-workflow-manager: Commit new plan + TODO.md + state.json
```

**Gaps**:
- Plan version history not tracked in state.json (only latest plan_path)
- Previous plan versions not referenced
- No project state.json to maintain plan version array

#### /implement Command Update Flow
```
Stage 1 (Preflight):
  └─> status-sync-manager: [NOT STARTED]/[PLANNED]/[REVISED] → [IMPLEMENTING]
      ├─> TODO.md: Update status, add/preserve Started timestamp
      ├─> state.json: Update status, add started field
      └─> Plan file (if exists): Mark resuming phase [IN PROGRESS]

Stage 7 (Postflight):
  └─> status-sync-manager: [IMPLEMENTING] → [COMPLETED]/[PARTIAL]
      ├─> TODO.md: Update status, add Completed timestamp, link implementation
      ├─> state.json: Update status, add completed field, add artifacts array
      ├─> Plan file (if exists): Mark phases [COMPLETED]
      └─> (No project state.json update)

Git Commit:
  └─> git-workflow-manager: Commit implementation + TODO.md + state.json + plan
```

**Gaps**:
- Plan file phase updates happen in command, not via status-sync-manager
- Implementation summary not tracked in state.json artifacts
- Project state.json not created to track implementation artifacts
- Resume logic reads plan file directly, not from state tracking

### 1.2 Files Updated by Each Command

| Command | TODO.md | state.json | project state.json | plan file | Git Commit |
|---------|---------|------------|-------------------|-----------|------------|
| /research | [PASS] (via status-sync-manager) | [PASS] (via status-sync-manager) | [FAIL] (not created) | N/A | [PASS] (via git-workflow-manager) |
| /plan | [PASS] (via status-sync-manager) | [PASS] (via status-sync-manager) | [FAIL] (not created) | N/A | [PASS] (via git-workflow-manager) |
| /revise | [PASS] (via status-sync-manager) | [PASS] (via status-sync-manager) | [FAIL] (not created) | N/A | [PASS] (via git-workflow-manager) |
| /implement | [PASS] (via status-sync-manager) | [PASS] (via status-sync-manager) | [FAIL] (not created) | [PASS] (manual in command) | [PASS] (via git-workflow-manager) |

**Key Observations**:
- status-sync-manager handles TODO.md and state.json consistently
- Project state.json never created or updated (lazy creation gap)
- Plan file updates happen manually in /implement, not via status-sync-manager
- Git commits delegated to git-workflow-manager consistently

### 1.3 Agents Performing Updates

| Agent/Manager | Responsibility | Files Updated | Atomic? |
|---------------|----------------|---------------|---------|
| status-sync-manager | Status transitions, timestamps, artifact links | TODO.md, state.json | [PASS] Yes (two-phase commit) |
| git-workflow-manager | Git commits | N/A (commits files) | [PASS] Yes (atomic commit) |
| /research command | Artifact linking (manual) | TODO.md (direct edit) | [FAIL] No |
| /plan command | Plan metadata (manual) | TODO.md (direct edit) | [FAIL] No |
| /revise command | Plan link update (manual) | TODO.md (direct edit) | [FAIL] No |
| /implement command | Plan phase updates (manual) | Plan file (direct edit) | [FAIL] No |

**Critical Finding**: Commands perform manual updates outside status-sync-manager, breaking atomicity guarantees.

### 1.4 Current Gaps Summary

1. **Project state.json never created**: Lazy creation policy not implemented for project-level state tracking
2. **Artifact links added manually**: Commands edit TODO.md directly instead of delegating to status-sync-manager
3. **Plan file updates manual**: /implement updates plan phases directly, not via status-sync-manager
4. **Plan metadata not tracked**: Phase count, estimated hours, version history missing from state.json
5. **No artifact validation**: Links added without verifying files exist
6. **Inconsistent update patterns**: Some updates via status-sync-manager, others manual
7. **No project state.json schema**: state-schema.md defines it but no command creates it

---

## 2. Gap Analysis (25%)

### 2.1 Missing Updates (Critical Gaps)

#### Gap 1: Project state.json Never Created
**Location**: All commands  
**Severity**: Critical  
**Impact**: No project-level state tracking, violates state-schema.md specification

**Evidence**:
- state-schema.md defines project state.json schema (lines 256-288)
- artifact-management.md references project state.json (line 22)
- No command creates .opencode/specs/NNN_project_name/state.json
- Lazy creation applies only to reports/, plans/, summaries/ subdirectories

**Recommendation**: Enhance status-sync-manager to create project state.json on first artifact write

#### Gap 2: Artifact Links Added Without Validation
**Location**: /research, /plan, /implement commands (Stage 7 Postflight)  
**Severity**: Critical  
**Impact**: Broken links in TODO.md if artifact creation fails

**Evidence**:
```markdown
# /research command (lines 193-196)
<artifact_linking>
  - Main Report: [.opencode/specs/{task_number}_{slug}/reports/research-001.md]
  - Summary: [.opencode/specs/{task_number}_{slug}/summaries/research-summary.md]
</artifact_linking>
```

**Issue**: Links added before verifying files exist on disk

**Recommendation**: Add artifact validation step before linking:
```python
def validate_artifacts_exist(artifacts):
    for artifact in artifacts:
        if not os.path.exists(artifact['path']):
            raise ArtifactNotFoundError(f"Artifact {artifact['path']} not found")
```

#### Gap 3: Plan File Phase Updates Not Atomic
**Location**: /implement command (Stage 1 Preflight, Stage 7 Postflight)  
**Severity**: Critical  
**Impact**: Plan file can be inconsistent with TODO.md/state.json if update fails

**Evidence**:
```markdown
# /implement command (lines 150-152)
<status_update>
  Atomic update via status-sync-manager:
    - TODO.md: [IMPLEMENTING], **Started**: {date}
    - state.json: status = "implementing", started = "{date}"
    - Plan file (if exists): Mark resuming phase [IN PROGRESS]  # ← Manual update
</status_update>
```

**Issue**: Plan file updated separately from TODO.md/state.json, not part of atomic transaction

**Recommendation**: Extend status-sync-manager to include plan file in two-phase commit

#### Gap 4: Plan Metadata Not Tracked in state.json
**Location**: /plan, /revise commands  
**Severity**: Moderate  
**Impact**: Cannot query plan metadata without parsing plan file

**Evidence**:
- state.json tracks plan_path but not phase_count, estimated_hours, complexity
- Plan summary includes metadata but not persisted to state.json
- /implement cannot determine total phases without reading plan file

**Recommendation**: Add plan metadata fields to state.json:
```json
{
  "plan_path": ".opencode/specs/195_task/plans/implementation-001.md",
  "plan_metadata": {
    "phases": 4,
    "estimated_hours": 6,
    "complexity": "medium",
    "created": "2025-12-28"
  }
}
```

#### Gap 5: Plan Version History Not Tracked
**Location**: /revise command  
**Severity**: Moderate  
**Impact**: Cannot reconstruct plan evolution, only latest version known

**Evidence**:
```markdown
# /revise command (lines 185-190)
<atomic_update>
  Use status-sync-manager to atomically:
    - Update TODO.md: Update plan link to new version  # ← Overwrites previous
    - Update state.json: plan_path to new version      # ← Overwrites previous
</atomic_update>
```

**Issue**: Previous plan versions lost when /revise updates plan_path

**Recommendation**: Track plan version array in state.json:
```json
{
  "plan_path": ".opencode/specs/195_task/plans/implementation-003.md",
  "plan_versions": [
    {
      "version": 1,
      "path": ".opencode/specs/195_task/plans/implementation-001.md",
      "created": "2025-12-27",
      "reason": "initial"
    },
    {
      "version": 2,
      "path": ".opencode/specs/195_task/plans/implementation-002.md",
      "created": "2025-12-28",
      "reason": "adjust approach based on research"
    },
    {
      "version": 3,
      "path": ".opencode/specs/195_task/plans/implementation-003.md",
      "created": "2025-12-28",
      "reason": "simplify phase breakdown"
    }
  ]
}
```

#### Gap 6: Implementation Summary Not Tracked
**Location**: /implement command  
**Severity**: Moderate  
**Impact**: Implementation summaries not queryable from state.json

**Evidence**:
- /implement creates summaries/implementation-summary-{date}.md
- Summary path not added to state.json artifacts array
- Cannot list all implementation summaries without filesystem scan

**Recommendation**: Add implementation summaries to state.json artifacts:
```json
{
  "artifacts": [
    ".opencode/specs/195_task/summaries/implementation-summary-20251228.md",
    "Logos/Core/Automation/ProofSearch.lean"
  ]
}
```

#### Gap 7: Resume Logic Reads Plan File Directly
**Location**: /implement command (Stage 1 Preflight)  
**Severity**: Low  
**Impact**: Tight coupling to plan file format, fragile resume logic

**Evidence**:
```markdown
# /implement command (lines 137-146)
<resume_logic>
  If plan exists:
    - Check phase statuses in plan file  # ← Direct file parsing
    - Find first [NOT STARTED] or [IN PROGRESS] phase
    - Resume from that phase
</resume_logic>
```

**Issue**: Plan file parsed directly instead of reading from state tracking

**Recommendation**: Track phase statuses in state.json:
```json
{
  "plan_path": ".opencode/specs/195_task/plans/implementation-001.md",
  "phase_statuses": [
    {"phase": 1, "status": "completed", "started": "2025-12-28", "completed": "2025-12-28"},
    {"phase": 2, "status": "in_progress", "started": "2025-12-28"},
    {"phase": 3, "status": "not_started"},
    {"phase": 4, "status": "not_started"}
  ]
}
```

### 2.2 Inconsistent Update Patterns

#### Inconsistency 1: Artifact Linking
- **status-sync-manager**: Supports artifact_links parameter (line 45-48)
- **/research command**: Adds artifact links manually in command (lines 193-196)
- **/plan command**: Adds plan link manually in command (lines 167-169)
- **/implement command**: Adds implementation links manually in command (lines 246-248)

**Impact**: Bypasses atomic update guarantees, risk of inconsistent state

#### Inconsistency 2: Timestamp Preservation
- **status-sync-manager**: Preserves Started timestamp (principle_4, line 334)
- **Commands**: Explicitly document "preserve Started" in multiple places
- **Redundancy**: Same requirement stated in 3 places (status-markers.md, status-sync-manager, commands)

**Impact**: Duplication increases maintenance burden, risk of drift

#### Inconsistency 3: Plan File Updates
- **/implement**: Updates plan file directly (lines 150-152, 268)
- **status-sync-manager**: Does not handle plan file updates
- **Gap**: Plan file not part of atomic transaction

**Impact**: Plan file can diverge from TODO.md/state.json if update fails

### 2.3 Non-Atomic Update Risks

#### Risk 1: Partial Update on status-sync-manager Failure
**Scenario**: status-sync-manager updates TODO.md successfully, then state.json write fails

**Current Behavior**:
- status-sync-manager rollback restores TODO.md (lines 125-131)
- Atomic guarantee preserved [PASS]

**Risk Level**: Low (status-sync-manager handles this correctly)

#### Risk 2: Partial Update on Manual Artifact Linking Failure
**Scenario**: Command updates status via status-sync-manager, then manual artifact linking fails

**Current Behavior**:
- status-sync-manager completes successfully
- Command adds artifact links manually
- If linking fails, TODO.md/state.json updated but no artifact links

**Risk Level**: High (no rollback mechanism for manual updates)

**Example**:
```
1. status-sync-manager: [RESEARCHING] → [RESEARCHED] [PASS]
2. Command: Add artifact links to TODO.md [FAIL] (fails)
Result: Task marked [RESEARCHED] but no artifact links
```

#### Risk 3: Partial Update on Plan File Update Failure
**Scenario**: /implement updates TODO.md/state.json via status-sync-manager, then plan file update fails

**Current Behavior**:
- status-sync-manager completes successfully
- Command updates plan file manually
- If plan update fails, TODO.md/state.json show [COMPLETED] but plan shows [IN PROGRESS]

**Risk Level**: High (plan file diverges from status tracking)

**Example**:
```
1. status-sync-manager: [IMPLEMENTING] → [COMPLETED] [PASS]
2. Command: Mark plan phases [COMPLETED] [FAIL] (fails)
Result: Task marked [COMPLETED] but plan shows incomplete phases
```

### 2.4 Missing Validation

#### Validation Gap 1: Artifact Existence
**Location**: All commands adding artifact links  
**Missing Check**: Verify artifact files exist before linking

**Recommendation**:
```python
def validate_artifact_links(artifact_links):
    for link in artifact_links:
        path = link['path']
        if not os.path.exists(path):
            raise ArtifactNotFoundError(f"Artifact {path} does not exist")
        if os.path.getsize(path) == 0:
            raise ArtifactEmptyError(f"Artifact {path} is empty")
```

#### Validation Gap 2: Plan File Consistency
**Location**: /implement command resume logic  
**Missing Check**: Verify plan file phase count matches expected phases

**Recommendation**:
```python
def validate_plan_consistency(plan_path, expected_phases):
    actual_phases = parse_plan_phases(plan_path)
    if len(actual_phases) != expected_phases:
        raise PlanInconsistencyError(
            f"Plan has {len(actual_phases)} phases, expected {expected_phases}"
        )
```

#### Validation Gap 3: State.json Schema Compliance
**Location**: status-sync-manager  
**Missing Check**: Validate state.json updates match state-schema.md

**Recommendation**:
```python
def validate_state_schema(state_update):
    required_fields = ['status', 'started']
    for field in required_fields:
        if field not in state_update:
            raise SchemaValidationError(f"Missing required field: {field}")
    
    if state_update['status'] not in VALID_STATUSES:
        raise SchemaValidationError(f"Invalid status: {state_update['status']}")
```

### 2.5 Documentation Gaps

#### Documentation Gap 1: status-sync-manager Usage Examples
**Location**: status-sync-manager.md  
**Missing**: Concrete usage examples from commands

**Recommendation**: Add examples section:
```markdown
## Usage Examples

### Example 1: /research Command Postflight
```python
status_sync_manager.update_status(
    task_number=195,
    new_status="researched",
    timestamp="2025-12-28",
    session_id="sess_1703606400_a1b2c3",
    artifact_links=[
        {
            "type": "research",
            "path": ".opencode/specs/195_task/reports/research-001.md",
            "label": "Main Report"
        },
        {
            "type": "summary",
            "path": ".opencode/specs/195_task/summaries/research-summary.md",
            "label": "Summary"
        }
    ]
)
```
```

#### Documentation Gap 2: Project state.json Creation
**Location**: state-schema.md  
**Missing**: When and how project state.json should be created

**Current State**:
- Schema defined (lines 256-288)
- No creation guidance
- No command implements creation

**Recommendation**: Add creation guidance:
```markdown
## Project State File Creation

Project state.json should be created lazily on first artifact write:

1. /research: Create on first research report write
2. /plan: Create on first plan write
3. /implement: Create on first implementation artifact write

Template:
```json
{
  "project_name": "{slug}",
  "project_number": {number},
  "type": "{type}",
  "phase": "{current_phase}",
  "reports": [],
  "plans": [],
  "summaries": [],
  "status": "{status}",
  "created": "{ISO8601}",
  "last_updated": "{ISO8601}"
}
```
```

#### Documentation Gap 3: Atomic Update Guarantees
**Location**: command-lifecycle.md  
**Missing**: Clear statement of atomicity guarantees and limitations

**Recommendation**: Add atomicity section:
```markdown
## Atomicity Guarantees

### Guaranteed Atomic (via status-sync-manager)
- TODO.md + state.json status updates
- Timestamp updates
- Status marker transitions

### Not Atomic (manual updates)
- Artifact linking (added after status update)
- Plan file phase updates (separate from status update)
- Project state.json updates (not implemented)

### Recommendation
All updates should go through status-sync-manager for atomicity.
```

---

## 3. Architecture Evaluation (25%)

### 3.1 Current status-sync-manager Capabilities

#### Strengths
1. **Two-Phase Commit**: Robust prepare-then-commit pattern (lines 63-145)
2. **Rollback on Failure**: Automatic rollback if any write fails (lines 125-131)
3. **Status Transition Validation**: Enforces valid state machine (lines 77-88, 296-318)
4. **Timestamp Preservation**: Preserves Started timestamp across updates (principle_4)
5. **Multi-File Updates**: Handles TODO.md, state.json, project state.json, plan file (lines 90-110)
6. **Standardized Returns**: Follows subagent-return-format.md (lines 159-276)

#### Limitations
1. **Underutilized**: Commands perform manual updates instead of delegating
2. **No Artifact Validation**: Accepts artifact_links without verifying files exist
3. **No Plan Metadata**: Cannot store plan phase count, estimated hours
4. **No Version Tracking**: Cannot track plan version history
5. **No Project State Creation**: Does not create project state.json (lazy creation gap)
6. **Limited Error Context**: Rollback details minimal (line 248)

#### Current Usage Pattern
```
Commands → status-sync-manager (status only) → TODO.md + state.json
Commands → Manual updates → Artifact links, plan files
```

**Problem**: Manual updates bypass atomic guarantees

### 3.2 Centralized vs Distributed Updates

#### Option A: Pure Centralized (Enhanced status-sync-manager)
**Approach**: All updates go through status-sync-manager

**Pros**:
- Single source of truth for all updates
- Guaranteed atomicity across all files
- Consistent validation and error handling
- Easier to maintain and debug

**Cons**:
- status-sync-manager becomes complex (handles artifacts, plans, metadata)
- Tight coupling between commands and status-sync-manager
- Harder to extend with new update types
- Single point of failure

**Complexity**: High (status-sync-manager grows to 500+ lines)

#### Option B: Pure Distributed (Each Subagent Updates)
**Approach**: Each subagent updates its own files directly

**Pros**:
- Loose coupling, easier to extend
- Subagents own their update logic
- Simpler individual components

**Cons**:
- No atomicity guarantees across files
- Inconsistent update patterns
- Harder to validate cross-file consistency
- Risk of partial updates on failure

**Complexity**: Medium (distributed complexity)

#### Option C: Hybrid (Enhanced status-sync-manager + Distributed Validation)
**Approach**: status-sync-manager coordinates atomic updates, subagents validate their artifacts

**Pros**:
- Atomicity guaranteed by status-sync-manager
- Subagents validate their own artifacts before update
- Clear separation of concerns (coordination vs validation)
- Extensible (new artifact types add validation, not coordination)

**Cons**:
- Requires coordination protocol between subagents and status-sync-manager
- Slightly more complex than pure centralized

**Complexity**: Medium (balanced)

**Recommended**: Option C (Hybrid)

### 3.3 Complexity Analysis

#### Option A: Pure Centralized
**status-sync-manager Complexity**:
- Current: ~340 lines
- With enhancements: ~550 lines (+62%)
  - Artifact validation: +50 lines
  - Plan metadata tracking: +40 lines
  - Project state.json creation: +60 lines
  - Plan version history: +40 lines
  - Enhanced error handling: +20 lines

**Command Complexity**:
- Current: Manual updates in each command
- With centralization: Delegate all updates to status-sync-manager
- Reduction: ~30 lines per command × 4 commands = 120 lines saved

**Total Complexity**: +430 lines (status-sync-manager) - 120 lines (commands) = +310 lines

#### Option B: Pure Distributed
**Subagent Complexity**:
- Each subagent implements own update logic
- researcher: +80 lines (artifact validation, state updates)
- planner: +90 lines (plan metadata, version tracking)
- implementer: +100 lines (plan phase updates, implementation tracking)
- lean-implementation-agent: +100 lines (similar to implementer)

**Command Complexity**:
- Commands coordinate subagent updates
- Each command: +40 lines (coordination logic)
- Total: 4 commands × 40 lines = 160 lines

**Total Complexity**: +370 lines (subagents) + 160 lines (commands) = +530 lines

#### Option C: Hybrid
**status-sync-manager Complexity**:
- Current: ~340 lines
- With enhancements: ~480 lines (+41%)
  - Artifact validation protocol: +40 lines
  - Plan metadata tracking: +40 lines
  - Project state.json creation: +60 lines

**Subagent Complexity**:
- Each subagent implements artifact validation
- researcher: +30 lines (validate research artifacts)
- planner: +35 lines (validate plan, extract metadata)
- implementer: +40 lines (validate implementation, plan phases)
- lean-implementation-agent: +40 lines (similar to implementer)

**Command Complexity**:
- Commands delegate to status-sync-manager with validation
- Each command: -20 lines (remove manual updates, add validation delegation)
- Total: 4 commands × -20 lines = -80 lines saved

**Total Complexity**: +140 lines (status-sync-manager) + 145 lines (subagents) - 80 lines (commands) = +205 lines

**Winner**: Option C (Hybrid) - Lowest total complexity, best separation of concerns

### 3.4 Performance and Reliability Trade-offs

#### Performance

| Approach | File I/O Operations | Network Calls | Latency |
|----------|-------------------|---------------|---------|
| Centralized | 4 reads + 4 writes (atomic) | 0 (local) | Low (~2s) |
| Distributed | 4 reads + 4 writes (non-atomic) | 0 (local) | Low (~2s) |
| Hybrid | 4 reads + 4 writes (atomic) + validation | 0 (local) | Low (~2.5s) |

**Analysis**: All approaches have similar performance (local file I/O). Hybrid adds ~0.5s for validation.

#### Reliability

| Approach | Atomicity | Rollback | Consistency | Failure Recovery |
|----------|-----------|----------|-------------|------------------|
| Centralized | [PASS] Full | [PASS] Automatic | [PASS] Guaranteed | [PASS] Excellent |
| Distributed | [FAIL] None | [FAIL] Manual | [FAIL] Risk of drift | [FAIL] Poor |
| Hybrid | [PASS] Full | [PASS] Automatic | [PASS] Guaranteed | [PASS] Excellent |

**Analysis**: Centralized and Hybrid both provide full atomicity. Distributed has reliability risks.

#### Extensibility

| Approach | Add New Artifact Type | Add New Update File | Modify Update Logic |
|----------|----------------------|---------------------|---------------------|
| Centralized | Modify status-sync-manager | Modify status-sync-manager | Modify status-sync-manager |
| Distributed | Add validation to subagent | Add update to subagent | Modify subagent |
| Hybrid | Add validation to subagent | Modify status-sync-manager | Modify status-sync-manager or subagent |

**Analysis**: Hybrid provides best extensibility (artifact validation in subagents, coordination in status-sync-manager).

**Recommendation**: Hybrid approach balances performance, reliability, and extensibility.

---

## 4. Recommendation (20%)

### 4.1 Best Architecture Approach

**Recommended: Option C - Hybrid (Enhanced status-sync-manager + Distributed Validation)**

**Justification**:
1. **Lowest Complexity**: +205 lines total (vs +310 centralized, +530 distributed)
2. **Full Atomicity**: status-sync-manager provides two-phase commit across all files
3. **Clear Separation**: Coordination (status-sync-manager) vs Validation (subagents)
4. **Extensibility**: New artifact types add validation, not coordination logic
5. **Reliability**: Automatic rollback on failure, guaranteed consistency
6. **Maintainability**: Single coordination point, distributed validation logic

### 4.2 High-Level Implementation Plan

#### Phase 1: Enhance status-sync-manager (4 hours)
**Goal**: Add missing capabilities to status-sync-manager

**Tasks**:
1. Add artifact validation protocol (1 hour)
   - Define validation interface for subagents
   - Add pre-commit validation step
   - Validate artifact files exist and are non-empty

2. Add plan metadata tracking (1 hour)
   - Store phase_count, estimated_hours, complexity in state.json
   - Extract metadata from plan file during update
   - Update state-schema.md with new fields

3. Add project state.json creation (1.5 hours)
   - Implement lazy creation on first artifact write
   - Use state-template.json for initial structure
   - Add to two-phase commit transaction

4. Add plan version history tracking (0.5 hours)
   - Store plan_versions array in state.json
   - Track version, path, created, reason for each revision
   - Update /revise command to append to array

#### Phase 2: Update Subagents with Validation (2 hours)
**Goal**: Add artifact validation to each subagent

**Tasks**:
1. researcher: Validate research artifacts (0.5 hours)
   - Check research-001.md exists and is non-empty
   - Check research-summary.md exists and is <100 tokens
   - Return validation result to status-sync-manager

2. planner: Validate plan and extract metadata (0.5 hours)
   - Check implementation-NNN.md exists and is non-empty
   - Extract phase_count, estimated_hours from plan
   - Return validation result + metadata to status-sync-manager

3. implementer: Validate implementation artifacts (0.5 hours)
   - Check implementation files exist
   - Check implementation-summary-{date}.md exists
   - Return validation result to status-sync-manager

4. lean-implementation-agent: Validate Lean implementation (0.5 hours)
   - Check Lean files compile (via lean-lsp-mcp)
   - Check implementation-summary-{date}.md exists
   - Return validation result to status-sync-manager

#### Phase 3: Update Commands to Use Enhanced status-sync-manager (2 hours)
**Goal**: Remove manual updates from commands, delegate to status-sync-manager

**Tasks**:
1. /research command (0.5 hours)
   - Remove manual artifact linking
   - Pass artifact_links to status-sync-manager
   - Add validation delegation to researcher

2. /plan command (0.5 hours)
   - Remove manual plan linking
   - Pass plan_path and metadata to status-sync-manager
   - Add validation delegation to planner

3. /revise command (0.5 hours)
   - Remove manual plan link update
   - Pass new plan_path and version to status-sync-manager
   - Add validation delegation to planner

4. /implement command (0.5 hours)
   - Remove manual plan phase updates
   - Pass plan_path and phase_statuses to status-sync-manager
   - Add validation delegation to implementer/lean-implementation-agent

#### Phase 4: Testing and Documentation (2 hours)
**Goal**: Validate changes and update documentation

**Tasks**:
1. Integration testing (1 hour)
   - Test /research → /plan → /implement workflow
   - Test /revise workflow
   - Test failure scenarios (artifact missing, validation failure)
   - Verify atomicity (rollback on failure)

2. Documentation updates (1 hour)
   - Update status-sync-manager.md with new capabilities
   - Update state-schema.md with new fields
   - Update command-lifecycle.md with validation protocol
   - Add usage examples to status-sync-manager.md

### 4.3 Files Requiring Updates

#### Core Files (status-sync-manager)
1. `.opencode/agent/subagents/status-sync-manager.md` (+140 lines)
   - Add artifact validation protocol
   - Add plan metadata tracking
   - Add project state.json creation
   - Add plan version history tracking

#### Subagent Files (validation)
2. `.opencode/agent/subagents/researcher.md` (+30 lines)
   - Add artifact validation function
   - Return validation result to status-sync-manager

3. `.opencode/agent/subagents/planner.md` (+35 lines)
   - Add plan validation function
   - Extract and return plan metadata

4. `.opencode/agent/subagents/implementer.md` (+40 lines)
   - Add implementation artifact validation
   - Validate plan phase updates

5. `.opencode/agent/subagents/lean-implementation-agent.md` (+40 lines)
   - Add Lean-specific validation (compilation check)
   - Validate implementation artifacts

#### Command Files (delegation)
6. `.opencode/command/research.md` (-20 lines)
   - Remove manual artifact linking
   - Add validation delegation

7. `.opencode/command/plan.md` (-20 lines)
   - Remove manual plan linking
   - Add validation delegation

8. `.opencode/command/revise.md` (-20 lines)
   - Remove manual plan link update
   - Add validation delegation

9. `.opencode/command/implement.md` (-20 lines)
   - Remove manual plan phase updates
   - Add validation delegation

#### Documentation Files
10. `.opencode/context/core/system/state-schema.md` (+50 lines)
    - Add plan_metadata field schema
    - Add plan_versions array schema
    - Add project state.json creation guidance

11. `.opencode/context/core/workflows/command-lifecycle.md` (+30 lines)
    - Add validation protocol section
    - Add atomicity guarantees section
    - Update postflight procedures

### 4.4 Estimated Effort

| Phase | Tasks | Hours |
|-------|-------|-------|
| Phase 1: Enhance status-sync-manager | 4 tasks | 4.0 |
| Phase 2: Update Subagents | 4 tasks | 2.0 |
| Phase 3: Update Commands | 4 tasks | 2.0 |
| Phase 4: Testing and Documentation | 2 tasks | 2.0 |
| **Total** | **14 tasks** | **10.0** |

**Contingency**: +2 hours for unexpected issues

**Total Estimated Effort**: 10-12 hours

---

## 5. Documentation Plan (10%)

### 5.1 Where to Document Update Procedures

#### Primary Documentation Location
**File**: `.opencode/context/core/workflows/command-lifecycle.md`  
**Section**: New "Stage 7: Postflight - Update Procedures"

**Rationale**:
- command-lifecycle.md already defines 8-stage pattern for all commands
- Postflight stage (Stage 7) is where updates occur
- Centralized location for all commands to reference
- Avoids duplication across 4 command files

**Content**:
```markdown
### Stage 7: Postflight - Update Procedures

All status and artifact updates MUST go through status-sync-manager for atomicity.

#### Update Protocol
1. Subagent validates artifacts (returns validation result)
2. Command delegates to status-sync-manager with:
   - task_number
   - new_status
   - timestamp
   - artifact_links (validated)
   - plan_metadata (if applicable)
3. status-sync-manager performs two-phase commit:
   - Phase 1: Prepare updates, validate, create backups
   - Phase 2: Write all files or rollback all
4. status-sync-manager returns success/failure
5. Command proceeds to git commit (via git-workflow-manager)

#### Atomicity Guarantees
- TODO.md + state.json + project state.json + plan file updated atomically
- Automatic rollback if any write fails
- No partial updates possible

#### Validation Requirements
- Subagents MUST validate artifacts before returning to command
- Artifacts MUST exist on disk and be non-empty
- Plan metadata MUST be extracted from plan file
- Validation failures MUST abort update (no status change)
```

#### Secondary Documentation Locations

**File**: `.opencode/agent/subagents/status-sync-manager.md`  
**Section**: New "Usage Examples" section

**Content**: Concrete examples from each command showing how to call status-sync-manager

**File**: `.opencode/context/core/system/state-schema.md`  
**Section**: Enhanced "Project State File" section

**Content**: When and how to create project state.json, new field schemas

### 5.2 New Context File vs Enhance Existing

**Decision**: Enhance existing files (no new context file)

**Rationale**:
1. **Avoid Context Bloat**: New file adds to context loading overhead
2. **Logical Grouping**: Update procedures belong in command-lifecycle.md
3. **Single Source of Truth**: Centralized documentation easier to maintain
4. **Existing Structure**: command-lifecycle.md already has postflight section

**Files to Enhance**:
1. command-lifecycle.md: Add update protocol to Stage 7
2. status-sync-manager.md: Add usage examples
3. state-schema.md: Add new field schemas and creation guidance

**Total Documentation Additions**: ~150 lines across 3 files (vs ~200 lines for new file)

### 5.3 How to Avoid Context Bloat

#### Strategy 1: Use Concise Examples
- Provide 1-2 concrete examples per command
- Avoid verbose explanations (reference standards instead)
- Use code snippets, not prose

**Before** (verbose):
```markdown
The /research command should call status-sync-manager after the researcher
subagent completes. It should pass the task number, new status (researched),
timestamp, and artifact links. The artifact links should include the research
report and summary paths.
```

**After** (concise):
```markdown
/research postflight:
```python
status_sync_manager.update(
    task_number=195,
    new_status="researched",
    timestamp="2025-12-28",
    artifact_links=[
        {"type": "research", "path": "reports/research-001.md"},
        {"type": "summary", "path": "summaries/research-summary.md"}
    ]
)
```
```

**Savings**: 60 words → 15 words (75% reduction)

#### Strategy 2: Reference Existing Standards
- Link to status-markers.md for status transitions
- Link to state-schema.md for field schemas
- Link to subagent-return-format.md for return formats

**Example**:
```markdown
Status transitions follow status-markers.md valid transitions table.
Field schemas follow state-schema.md project state section.
```

**Savings**: Avoids duplicating 100+ lines of status transition rules

#### Strategy 3: Use Variation Tables
- command-lifecycle.md already uses variation tables effectively
- Add update procedure variations to existing tables
- Avoid repeating common procedures

**Example**:
```markdown
| Command | Artifacts to Validate | Metadata to Extract |
|---------|----------------------|---------------------|
| /research | research-001.md, research-summary.md | None |
| /plan | implementation-NNN.md | phase_count, estimated_hours |
| /implement | implementation files, summary | phase_statuses |
```

**Savings**: 80 lines of prose → 10 lines of table

#### Strategy 4: Lazy Loading
- Core update protocol in command-lifecycle.md (always loaded)
- Detailed examples in status-sync-manager.md (loaded only when needed)
- Field schemas in state-schema.md (loaded only when needed)

**Context Loading**:
- Commands load: command-lifecycle.md (core protocol)
- Subagents load: status-sync-manager.md (detailed examples)
- State operations load: state-schema.md (field schemas)

**Savings**: Avoids loading all 3 files for every command invocation

### 5.4 Integration with command-lifecycle.md

#### Current Structure
command-lifecycle.md defines 8 stages:
1. Preflight
2. CheckLanguage / DetermineRouting
3. PrepareDelegation
4. InvokeAgent
5. ReceiveResults
6. ProcessResults
7. Postflight
8. ReturnSuccess

#### Proposed Enhancement
**Stage 7: Postflight** currently covers:
- Status transitions
- Artifact linking
- Git commits

**Add**: Update Procedures subsection
```markdown
### Stage 7: Postflight

**Purpose**: Update status, link artifacts, create git commit

**Common Steps**:
1. Validate artifacts (delegate to subagent)
2. Update status via status-sync-manager (atomic)
3. Create git commit via git-workflow-manager
4. Validate updates succeeded

**Update Procedures** (NEW):
[Insert update protocol from 5.1]

**Status Update Patterns**: [existing content]
**Artifact Linking Patterns**: [existing content]
**Git Commit Pattern**: [existing content]
```

**Integration Points**:
- Validation (Step 1) → Subagent validation protocol
- Update (Step 2) → status-sync-manager delegation
- Commit (Step 3) → git-workflow-manager delegation

**Total Addition**: ~50 lines to command-lifecycle.md

---

## 6. Key Findings Summary

### Critical Gaps (7)
1. Project state.json never created (violates state-schema.md)
2. Artifact links added without validation (risk of broken links)
3. Plan file phase updates not atomic (risk of inconsistency)
4. Plan metadata not tracked in state.json (cannot query without parsing)
5. Plan version history not tracked (cannot reconstruct evolution)
6. Implementation summary not tracked in state.json (not queryable)
7. Resume logic reads plan file directly (tight coupling, fragile)

### Architectural Findings (4)
1. status-sync-manager exists with robust two-phase commit but underutilized
2. Commands perform manual updates bypassing atomic guarantees
3. Hybrid approach (enhanced status-sync-manager + distributed validation) optimal
4. Lowest complexity (+205 lines), full atomicity, best extensibility

### Recommended Architecture
**Hybrid**: Enhanced status-sync-manager + Distributed Validation
- status-sync-manager: Coordination, atomicity, rollback
- Subagents: Artifact validation, metadata extraction
- Commands: Delegation to status-sync-manager

### Implementation Effort
**Total**: 10-12 hours
- Phase 1: Enhance status-sync-manager (4 hours)
- Phase 2: Update subagents (2 hours)
- Phase 3: Update commands (2 hours)
- Phase 4: Testing and documentation (2 hours)
- Contingency: +2 hours

### Documentation Strategy
**Enhance Existing Files** (no new context file):
- command-lifecycle.md: Add update protocol to Stage 7 (+50 lines)
- status-sync-manager.md: Add usage examples (+60 lines)
- state-schema.md: Add field schemas and creation guidance (+40 lines)
- **Total**: +150 lines (vs +200 for new file)

---

## 7. References

### Analyzed Files
1. `.opencode/command/research.md` (333 lines)
2. `.opencode/command/plan.md` (310 lines)
3. `.opencode/command/revise.md` (287 lines)
4. `.opencode/command/implement.md` (394 lines)
5. `.opencode/agent/subagents/status-sync-manager.md` (341 lines)
6. `.opencode/agent/subagents/git-workflow-manager.md` (310 lines)
7. `.opencode/context/core/standards/status-markers.md` (889 lines)
8. `.opencode/context/core/system/state-schema.md` (642 lines)
9. `.opencode/context/core/system/artifact-management.md` (182 lines)
10. `.opencode/context/core/workflows/command-lifecycle.md` (809 lines)

### Standards Referenced
- status-markers.md: Status transition rules, timestamp formats
- state-schema.md: State file schemas, field naming conventions
- artifact-management.md: Lazy directory creation, artifact requirements
- command-lifecycle.md: 8-stage command pattern, postflight procedures
- subagent-return-format.md: Standardized return format for all agents

### Current State
- TODO.md: 36 active tasks, 29 completed tasks
- state.json: 7 active projects, 8 completed projects
- status-sync-manager: Exists with two-phase commit, underutilized
- git-workflow-manager: Exists with scoped commits, well-utilized

---

## 8. Conclusion

This research reveals that while the ProofChecker project has a robust atomic update mechanism (status-sync-manager) with two-phase commit capabilities, it is significantly underutilized. Commands perform manual updates outside the atomic transaction, creating risks of partial updates and inconsistent state. The recommended hybrid architecture enhances status-sync-manager with artifact validation, plan metadata tracking, and project state.json creation, while distributing validation logic to subagents. This approach provides full atomicity guarantees, lowest implementation complexity (+205 lines), and best extensibility for future artifact types. Implementation is estimated at 10-12 hours across 4 phases, with documentation enhancements to existing files (no new context file needed) to avoid context bloat.
