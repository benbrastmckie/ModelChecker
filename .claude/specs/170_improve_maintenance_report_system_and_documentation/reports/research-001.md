# Research Report: Improve Maintenance Report System and Documentation

- **Task**: 170 - Improve maintenance report system and documentation
- **Status**: [COMPLETED]
- **Started**: 2025-12-28T20:00:00Z
- **Completed**: 2025-12-28T21:00:00Z
- **Effort**: 1.5 hours
- **Priority**: Medium
- **Dependencies**: None
- **Sources/Inputs**:
  - .opencode/command/todo.md
  - .opencode/command/review.md
  - .opencode/command/revise.md
  - .opencode/command/research.md
  - .opencode/command/plan.md
  - .opencode/command/implement.md
  - .opencode/agent/subagents/reviewer.md
  - .opencode/context/core/system/artifact-management.md
  - .opencode/context/core/workflows/command-lifecycle.md
  - .opencode/context/core/standards/report.md
  - .opencode/context/core/standards/summary.md
  - .opencode/specs/state.json
  - .opencode/specs/maintenance/maintenance-report-20251224.md
  - .opencode/specs/maintenance/state.json
- **Artifacts**: 
  - .opencode/specs/170_improve_maintenance_report_system_and_documentation/reports/research-001.md
- **Standards**: status-markers.md, artifact-management.md, tasks.md, report.md

---

## Executive Summary

- **/todo command** is responsible for cleanup operations (archiving completed/abandoned tasks, moving project directories to archive, updating state files)
- **/review command** is responsible for surveying repository state, creating review reports following artifact-management.md standards, updating registries, and creating maintenance tasks
- **Current state**: /review command exists with comprehensive 8-stage workflow, delegates to reviewer.md subagent, creates review summary artifacts in lazy-created directories, updates state.json with review_artifacts array
- **Gap identified**: /review does NOT update project state.json or specs/state.json appropriately - missing state file update integration
- **Patterns from other commands**: All workflow commands (/research, /plan, /revise, /implement) follow command-lifecycle.md 8-stage pattern with atomic status updates via status-sync-manager
- **Recommended improvements**: Integrate /review with status-sync-manager for atomic state updates, clarify /revise task creation patterns, standardize context file documentation

---

## Context & Scope

This research analyzes the maintenance report system to clarify command responsibilities and identify improvements needed for consistency with project standards. The scope includes:

1. **Command Responsibilities**: Defining what /todo and /review should do
2. **Artifact Management Integration**: How /review should follow artifact-management.md
3. **State File Updates**: How /review should update state.json and project state.json
4. **Task Creation Patterns**: How /revise and other commands create tasks from reports
5. **Workflow Consistency**: Patterns from /research, /plan, /implement to adopt

---

## Findings

### 1. Current /todo Command Responsibilities

**File**: .opencode/command/todo.md (541 lines)

**Responsibilities** (WELL-DEFINED):
- Archive completed and abandoned tasks from TODO.md
- Move project directories to archive (.opencode/specs/archive/)
- Update state.json (move tasks from active_projects to completed_projects)
- Update archive/state.json (add archive entries)
- Preserve task numbering (no renumbering)
- Atomic updates with two-phase commit and rollback
- Git commit after archival

**Workflow** (7 stages):
1. ScanTODO: Identify [COMPLETED] and [ABANDONED] tasks
2. ConfirmArchival: User confirmation if > 5 tasks
3. PrepareArchival: Prepare directory moves and archive state updates
4. PrepareUpdates: Prepare TODO.md and state.json updates with complete task block removal
5. AtomicUpdate: Two-phase commit (backup → write → verify or rollback)
6. GitCommit: Commit archival changes
7. ReturnSuccess: Return comprehensive summary

**Key Features**:
- Self-healing: Auto-creates archive/state.json if missing
- Task block structure: Removes complete blocks (heading + body) with explicit boundary detection
- Validation: Detects orphaned metadata lines, validates JSON, checks paths
- No emojis: Professional output only

**Strengths**:
- Comprehensive error handling with rollback
- Atomic guarantees across 4 entities (TODO.md, state.json, archive/state.json, directories)
- Well-documented task block structure and boundary patterns
- Extensive test cases and validation checklist

**Gaps**: None identified - /todo is well-specified for cleanup operations

---

### 2. Current /review Command Responsibilities

**File**: .opencode/command/review.md (405 lines)

**Responsibilities** (WELL-DEFINED):
- Analyze codebase comprehensively (Lean code, docs, tests)
- Update project registries (IMPLEMENTATION_STATUS.md, SORRY_REGISTRY.md, TACTIC_REGISTRY.md, FEATURE_REGISTRY.md)
- Create review summary artifact following summary.md standard
- Create maintenance tasks from identified issues
- Commit registry updates and artifacts

**Workflow** (8 stages):
1. Preflight: Load registries, determine review scope, prepare project path
2. PrepareDelegation: Generate session_id, prepare delegation context
3. InvokeReviewer: Delegate to reviewer.md subagent
4. ReceiveResults: Wait for and validate reviewer return
5. ProcessResults: Extract registry updates, artifacts, identified tasks
6. CreateTasks: Invoke /task command to create maintenance tasks
7. Postflight: Update state.json, registries, commit changes
8. ReturnSuccess: Return brief summary to user

**Artifact Management**:
- Lazy directory creation: Project root created by reviewer when writing first artifact
- Creates only summaries/ subdirectory (not reports/ or plans/)
- Review summary: summaries/review-summary.md following summary.md standard
- Project directory format: {next_project_number}_codebase_review

**State File Updates**:
- Updates state.json repository_health with review_artifacts entry:
  ```json
  "review_artifacts": [
    {
      "timestamp": "2025-12-28T20:00:00Z",
      "path": ".opencode/specs/207_codebase_review/summaries/review-summary.md",
      "scope": "full"
    }
  ]
  ```
- Increments next_project_number after project creation
- Updates TODO.md with created tasks
- Updates state.json with new task entries

**Strengths**:
- Follows command-lifecycle.md pattern (8 stages)
- Delegates to reviewer.md subagent with standardized return format
- Creates review summary artifact following summary.md standard
- Lazy directory creation (only summaries/)
- Comprehensive registry updates (4 registries)
- Task creation from identified issues

**Gaps Identified**:
1. **Missing project state.json update**: /review does NOT create or update project state.json file
2. **Missing status-sync-manager integration**: /review does NOT use status-sync-manager for atomic updates
3. **Missing specs/state.json update**: /review updates state.json repository_health but not active_projects or completed_projects arrays
4. **Unclear task creation pattern**: Stage 6 invokes /task command but doesn't specify how many tasks to create or how to batch them

---

### 3. Reviewer Subagent Responsibilities

**File**: .opencode/agent/subagents/reviewer.md (364 lines)

**Responsibilities** (WELL-DEFINED):
- Analyze codebase comprehensively based on review_scope (full|lean|docs)
- Update project registries (IMPLEMENTATION_STATUS.md, SORRY_REGISTRY.md, TACTIC_REGISTRY.md, FEATURE_REGISTRY.md)
- Identify maintenance tasks with priorities
- Create review summary artifact in summaries/review-summary.md
- Return standardized result per subagent-return-format.md

**Process Flow** (5 steps):
1. Analyze codebase: Scan files, collect metrics, categorize findings
2. Update registries: Update 4 registries with accurate counts
3. Identify maintenance tasks: Create task descriptions with priorities
4. Create review summary artifact: Write summaries/review-summary.md following summary.md standard
5. Return standardized result: Format return with artifacts, metrics, identified_tasks

**Artifact Structure**:
- Project directory: {project_path} (provided as input)
- Subdirectories: summaries/ only (created lazily)
- Artifacts: summaries/review-summary.md

**Return Format**:
```json
{
  "status": "completed",
  "summary": "Codebase review completed. Found {sorry_count} sorry statements, {axiom_count} axioms, {build_error_count} build errors. Identified {undocumented_tactic_count} undocumented tactics and {missing_feature_count} missing features. Created {task_count} tasks.",
  "artifacts": [
    {
      "type": "summary",
      "path": "{project_path}/summaries/review-summary.md",
      "summary": "Review findings and recommendations"
    },
    {
      "type": "documentation",
      "path": "Documentation/ProjectInfo/IMPLEMENTATION_STATUS.md",
      "summary": "Updated implementation status registry"
    }
  ],
  "metadata": {
    "session_id": "{session_id}",
    "duration_seconds": 1800,
    "agent_type": "reviewer",
    "delegation_depth": 1,
    "delegation_path": ["orchestrator", "review", "reviewer"]
  },
  "errors": [],
  "next_steps": "Review findings and address high-priority tasks",
  "identified_tasks": [
    {
      "description": "Fix {N} sorry statements in {file}",
      "priority": "high",
      "language": "lean"
    }
  ],
  "metrics": {
    "sorry_count": 10,
    "axiom_count": 11,
    "build_errors": 3,
    "undocumented_tactics": 8,
    "missing_features": 3,
    "tasks_created": 5
  }
}
```

**Strengths**:
- Follows subagent-return-format.md
- Creates review summary artifact following summary.md standard
- Lazy directory creation (only summaries/)
- Returns identified_tasks array for /review to create
- Returns metrics for state.json tracking
- No emojis in summaries or registry updates

**Gaps**: None identified - reviewer.md is well-specified

---

### 4. Artifact Management Integration

**File**: .opencode/context/core/system/artifact-management.md (275 lines)

**Key Principles**:
1. **Lazy directory creation**: Create project root and subdirectories only when writing first artifact
2. **Context window protection**: Subagents return artifact links + brief summaries (metadata), NOT full content
3. **Summary artifacts**: Required for multi-file outputs (e.g., /implement), NOT required for single-file outputs (e.g., /research, /plan)
4. **Artifact patterns by command**:
   - /research: 1 artifact (report only, NO summary artifact)
   - /plan: 1 artifact (plan only, self-documenting, NO summary artifact)
   - /revise: 1 artifact (revised plan, self-documenting, NO summary artifact)
   - /implement: N+1 artifacts (N files + 1 summary artifact)
   - /review: 1 artifact (review summary only)

**Summary Artifacts vs Summary Metadata**:
- **Summary Artifact** (file on disk): Created for multi-file outputs, provides detailed overview
- **Summary Metadata** (field in return object): Returned by ALL subagents, brief description (<100 tokens), NOT a separate file

**When to Create Summary Artifacts**:
- Create when: Multiple implementation files, output spans multiple files
- Do NOT create when: Single file, self-documenting file

**Validation Requirements**:
- Verify artifact files exist on disk
- Verify artifact files are non-empty (size > 0)
- Verify summary artifacts within token limit (<100 tokens, ~400 chars)
- Return validated_artifacts in return object metadata
- If validation fails: Return status "failed" with error details

**Integration with /review**:
- /review creates 1 artifact: summaries/review-summary.md
- Review summary is single file, self-contained
- NO separate summary artifact needed (review summary IS the summary)
- Summary metadata returned in return object summary field (<100 tokens)

**Compliance Check**:
- [PASS] /review follows lazy directory creation
- [PASS] /review creates review summary artifact
- [PASS] reviewer.md returns summary metadata in return object
- [PASS] /review does NOT create unnecessary summary artifact (review summary is the artifact)
- [FAIL] /review does NOT update project state.json (gap identified)

---

### 5. Task Creation Patterns from /revise

**File**: .opencode/command/revise.md (309 lines)

**Responsibilities**:
- Create new plan version for task
- Update status to [REVISED]
- Update plan link in TODO.md
- Commit new plan with status updates

**Workflow** (8 stages following command-lifecycle.md):
1. Preflight: Validate task, update status to [REVISING]
2. DeterminePlanVersion: Calculate next plan version number
3. PrepareDelegation: Prepare delegation context with existing_plan_path, new_version, revision_reason
4. InvokeAgent: Delegate to planner subagent
5. ReceiveResults: Validate planner return
6. ProcessResults: Extract new plan artifact
7. Postflight: Update status to [REVISED], update plan link, commit
8. ReturnSuccess: Return brief summary

**Task Creation**: /revise does NOT create tasks - it creates new plan versions

**Key Insight**: /revise is NOT a task creation command - it's a plan revision command

---

### 6. Task Creation Patterns from Other Commands

**Analysis of /research, /plan, /implement**:

None of these commands create tasks from their reports. They:
1. Create artifacts (reports, plans, implementation files)
2. Update status markers
3. Link artifacts in TODO.md
4. Commit changes

**Task Creation Responsibility**: /review is the ONLY command that creates tasks from reports

**Pattern**: /review Stage 6 (CreateTasks):
```
1. For each identified task from review:
   a. Invoke /task command to create task
   b. Set appropriate priority based on severity
   c. Set language based on task type
   d. Link to review findings
2. Collect created task numbers
3. Prepare task summary
```

**Gap**: /review.md does NOT specify:
- How many tasks to create (all identified tasks? batch them? prioritize?)
- How to batch task creation (one /task invocation per task? batch invocation?)
- How to handle task creation failures (continue? abort?)

---

### 7. Workflow Patterns from Other Commands

**File**: .opencode/context/core/workflows/command-lifecycle.md (930 lines)

**8-Stage Lifecycle Pattern** (followed by /research, /plan, /revise, /implement):

1. **Preflight**: Parse arguments, validate task, update status to in-progress
2. **CheckLanguage/DetermineRouting**: Extract language field, determine target agent
3. **PrepareDelegation**: Prepare delegation context for subagent
4. **InvokeAgent**: Delegate to subagent and wait for return
5. **ReceiveResults**: Validate agent return against subagent-return-format.md
6. **ProcessResults**: Extract artifacts, summary, errors
7. **Postflight**: Update status, link artifacts, create git commit
8. **ReturnSuccess**: Return brief summary to user

**Key Integration Point - Stage 7 Postflight**:

All workflow commands delegate to **status-sync-manager** for atomic updates:

```
Delegate to status-sync-manager:
  - task_number: {number}
  - new_status: {status from subagent return}
  - timestamp: {ISO8601 date}
  - session_id: {session_id}
  - validated_artifacts: {artifacts from subagent return}
  - plan_metadata: {metadata from planner if applicable}
  - plan_version: {version from revise if applicable}
  - phase_statuses: {statuses from implement if applicable}

status-sync-manager performs two-phase commit:
  - Phase 1: Prepare, validate artifacts, backup
  - Phase 2: Write all files or rollback all

Atomicity guaranteed across:
  - TODO.md (status markers, timestamps, artifact links)
  - state.json (status, timestamps, artifacts array, plan_metadata, plan_versions)
  - project state.json (lazy created on first artifact write)
  - plan file (phase statuses if applicable)
```

**Critical Finding**: /review does NOT use status-sync-manager for atomic updates

**Comparison**:

| Command | Uses status-sync-manager? | Updates project state.json? | Updates state.json? |
|---------|--------------------------|----------------------------|---------------------|
| /research | [PASS] Yes | [PASS] Yes (lazy) | [PASS] Yes (active_projects) |
| /plan | [PASS] Yes | [PASS] Yes (lazy) | [PASS] Yes (active_projects) |
| /revise | [PASS] Yes | [PASS] Yes (lazy) | [PASS] Yes (active_projects) |
| /implement | [PASS] Yes | [PASS] Yes (lazy) | [PASS] Yes (active_projects) |
| /review | [FAIL] No | [FAIL] No | [WARN] Partial (repository_health only) |

**Gap Identified**: /review should use status-sync-manager for atomic updates across TODO.md, state.json, and project state.json

---

### 8. State File Update Patterns

**File**: .opencode/specs/state.json (663 lines)

**Schema Version**: 1.1.0

**Key Sections**:
- `next_project_number`: 222 (incremented after each project creation)
- `active_projects`: Array of active project objects
- `completed_projects`: Array of completed project objects
- `repository_health`: Object with metrics and review_artifacts array
- `recent_activities`: Array of activity log entries
- `pending_tasks`: Array of pending task objects

**repository_health Section**:
```json
"repository_health": {
  "last_assessed": "2025-12-28T20:57:08Z",
  "overall_score": 92,
  "active_tasks": 24,
  "completed_tasks": 30,
  "blocked_tasks": 2,
  "in_progress_tasks": 2,
  "not_started_tasks": 23,
  "high_priority_tasks": 15,
  "medium_priority_tasks": 12,
  "low_priority_tasks": 11,
  "production_readiness": "excellent",
  "technical_debt": {
    "sorry_count": 10,
    "axiom_count": 11,
    "build_errors": 3,
    "status": "well-documented"
  },
  "review_artifacts": []
}
```

**Current /review State Updates**:
- [PASS] Updates repository_health.review_artifacts array
- [PASS] Increments next_project_number
- [PASS] Updates TODO.md with created tasks
- [PASS] Updates state.json with new task entries (via /task command)
- [FAIL] Does NOT update repository_health metrics (sorry_count, axiom_count, etc.)
- [FAIL] Does NOT create project state.json

**Recommended /review State Updates**:
1. Update repository_health.review_artifacts array (already done)
2. Update repository_health.last_assessed timestamp
3. Update repository_health.technical_debt metrics from reviewer return
4. Create project state.json for review project (lazy creation)
5. Add review project to active_projects or completed_projects (depending on review status)
6. Use status-sync-manager for atomic updates

---

### 9. Maintenance Report Example

**File**: .opencode/specs/maintenance/maintenance-report-20251224.md (427 lines)

**Structure**:
- Executive Summary
- Operations Performed (Tasks Removed, Projects Archived, Directories Moved, State File Updates, TODO.md Updates)
- Validation and Verification
- Warnings and Issues
- Statistics
- Next Steps
- Appendices

**Key Insights**:
- Comprehensive documentation of maintenance operations
- Detailed validation checks (next_project_number preservation, artifact preservation, JSON validity)
- Statistics on operation efficiency and repository health
- Clear next steps and recommendations

**Maintenance State File**: .opencode/specs/maintenance/state.json (2118 bytes)

**Integration with /review**:
- /review creates review summary artifact (similar to maintenance report)
- /review updates registries (similar to maintenance operations)
- /review creates tasks (similar to maintenance recommendations)
- /review should update maintenance/state.json with review operation details

**Gap**: /review does NOT update maintenance/state.json

---

### 10. Context File Consistency Analysis

**Files Analyzed**:
- .opencode/command/todo.md (541 lines) - [PASS] Well-documented
- .opencode/command/review.md (405 lines) - [WARN] Missing state update details
- .opencode/command/revise.md (309 lines) - [PASS] Well-documented
- .opencode/command/research.md (355 lines) - [PASS] Well-documented
- .opencode/command/plan.md (330 lines) - [PASS] Well-documented
- .opencode/command/implement.md (416 lines) - [PASS] Well-documented
- .opencode/agent/subagents/reviewer.md (364 lines) - [PASS] Well-documented
- .opencode/context/core/workflows/command-lifecycle.md (930 lines) - [PASS] Comprehensive
- .opencode/context/core/system/artifact-management.md (275 lines) - [PASS] Comprehensive
- .opencode/context/core/standards/report.md (67 lines) - [PASS] Clear
- .opencode/context/core/standards/summary.md (61 lines) - [PASS] Clear

**Consistency Findings**:
- [PASS] All workflow commands follow command-lifecycle.md 8-stage pattern
- [PASS] All commands use lazy directory creation
- [PASS] All commands create artifacts following standards
- [PASS] All commands (except /review) use status-sync-manager for atomic updates
- [WARN] /review.md missing status-sync-manager integration details
- [WARN] /review.md missing project state.json update details
- [WARN] /review.md missing task creation batching details

**Recommendations for Context File Updates**:
1. Update /review.md Stage 7 (Postflight) to use status-sync-manager
2. Add project state.json creation to /review.md
3. Clarify task creation batching in /review.md Stage 6
4. Update reviewer.md to document state file update expectations
5. Add maintenance/state.json update to /review workflow

---

## Decisions

### Decision 1: /todo Command Responsibilities (CONFIRMED)

**Decision**: /todo command is responsible for cleanup operations only:
- Archive completed and abandoned tasks from TODO.md
- Move project directories to archive
- Update state.json and archive/state.json
- Preserve task numbering
- Atomic updates with rollback
- Git commit after archival

**Rationale**: /todo.md is well-specified and comprehensive. No changes needed.

### Decision 2: /review Command Responsibilities (CLARIFIED)

**Decision**: /review command is responsible for:
- Surveying the present state of the repository
- Analyzing codebase (Lean code, docs, tests)
- Updating project registries (IMPLEMENTATION_STATUS.md, SORRY_REGISTRY.md, TACTIC_REGISTRY.md, FEATURE_REGISTRY.md)
- Creating review summary artifact following artifact-management.md standards
- Creating/updating project state.json file (NEW)
- Updating specs/state.json appropriately (ENHANCED)
- Creating maintenance tasks from identified issues
- Committing registry updates and artifacts

**Rationale**: /review should follow same patterns as other workflow commands (/research, /plan, /implement) for state file management.

### Decision 3: State File Update Integration (NEW REQUIREMENT)

**Decision**: /review must use status-sync-manager for atomic updates across:
- TODO.md (created tasks)
- state.json (repository_health, active_projects, next_project_number)
- project state.json (lazy created for review project)
- maintenance/state.json (review operation details)

**Rationale**: Consistency with other workflow commands and atomic update guarantees.

### Decision 4: Task Creation Pattern (CLARIFIED)

**Decision**: /review Stage 6 (CreateTasks) should:
- Create ALL identified tasks (no batching)
- Invoke /task command once per task
- Set priority based on severity (high/medium/low)
- Set language based on task type (lean/markdown/general)
- Link to review findings in task description
- Continue on task creation failure (log error, continue with next task)
- Collect created task numbers for summary

**Rationale**: Simple, predictable pattern. Batching adds complexity without clear benefit.

### Decision 5: /revise Does NOT Create Tasks (CONFIRMED)

**Decision**: /revise command creates new plan versions, NOT tasks.

**Rationale**: /revise is a plan revision command, not a task creation command. Task creation is /review's responsibility.

---

## Recommendations

### Priority 1: HIGH - Integrate /review with status-sync-manager

**Action**: Update /review.md Stage 7 (Postflight) to use status-sync-manager for atomic updates

**Details**:
1. Add status-sync-manager delegation in Stage 7
2. Update TODO.md, state.json, project state.json atomically
3. Use two-phase commit with rollback
4. Validate all updates before commit

**Estimated Effort**: 2-3 hours

**Owner**: Implementation team

**Files to Update**:
- .opencode/command/review.md (Stage 7 Postflight section)

**Example Integration**:
```xml
<stage id="7" name="Postflight">
  <atomic_update>
    Delegate to status-sync-manager:
      - review_number: {next_project_number}
      - new_status: "completed"
      - timestamp: {ISO8601 date}
      - session_id: {session_id}
      - validated_artifacts: {artifacts from reviewer return}
      - review_metrics: {metrics from reviewer return}
      - created_tasks: {task_numbers from CreateTasks stage}
    
    status-sync-manager performs two-phase commit:
      - Phase 1: Prepare, validate artifacts, backup
      - Phase 2: Write all files or rollback all
    
    Atomicity guaranteed across:
      - TODO.md (created tasks)
      - state.json (repository_health, active_projects, next_project_number)
      - project state.json (lazy created for review project)
      - maintenance/state.json (review operation details)
  </atomic_update>
</stage>
```

### Priority 2: HIGH - Add project state.json creation to /review

**Action**: Update /review.md to create project state.json for review project

**Details**:
1. Create project state.json lazily when reviewer writes first artifact
2. Populate with review metadata (scope, timestamp, metrics)
3. Add to status-sync-manager atomic update
4. Follow state-schema.md template

**Estimated Effort**: 1-2 hours

**Owner**: Implementation team

**Files to Update**:
- .opencode/command/review.md (Stage 7 Postflight section)
- .opencode/agent/subagents/reviewer.md (Step 4 artifact creation)

**Example state.json**:
```json
{
  "project_number": 207,
  "project_name": "codebase_review",
  "type": "review",
  "status": "completed",
  "scope": "full",
  "created": "2025-12-28T20:00:00Z",
  "completed": "2025-12-28T21:00:00Z",
  "artifacts": [
    ".opencode/specs/207_codebase_review/summaries/review-summary.md"
  ],
  "metrics": {
    "sorry_count": 10,
    "axiom_count": 11,
    "build_errors": 3,
    "undocumented_tactics": 8,
    "missing_features": 3,
    "tasks_created": 5
  },
  "registries_updated": [
    "Documentation/ProjectInfo/IMPLEMENTATION_STATUS.md",
    "Documentation/ProjectInfo/SORRY_REGISTRY.md",
    "Documentation/ProjectInfo/TACTIC_REGISTRY.md",
    "Documentation/ProjectInfo/FEATURE_REGISTRY.md"
  ]
}
```

### Priority 3: MEDIUM - Clarify task creation batching in /review

**Action**: Update /review.md Stage 6 (CreateTasks) with clear task creation pattern

**Details**:
1. Document task creation loop (one /task invocation per identified task)
2. Specify error handling (continue on failure, log error)
3. Document task numbering (sequential, no gaps)
4. Specify task linking (link to review findings)

**Estimated Effort**: 1 hour

**Owner**: Documentation team

**Files to Update**:
- .opencode/command/review.md (Stage 6 CreateTasks section)

**Example Documentation**:
```xml
<stage id="6" name="CreateTasks">
  <action>Create TODO.md tasks for identified work</action>
  <process>
    1. For each identified task from review:
       a. Invoke /task command to create task
       b. Set appropriate priority based on severity
       c. Set language based on task type
       d. Link to review findings
       e. If task creation fails: Log error, continue with next task
    2. Collect created task numbers
    3. Prepare task summary
  </process>
  <task_creation_pattern>
    - Create ALL identified tasks (no batching)
    - One /task invocation per task
    - Sequential task numbering (no gaps)
    - Continue on failure (log error, continue with next task)
  </task_creation_pattern>
  <error_handling>
    If task creation fails:
      - Log error with task description and reason
      - Continue with next task
      - Include failed task count in summary
      - Recommend manual task creation for failed tasks
  </error_handling>
</stage>
```

### Priority 4: MEDIUM - Update state.json repository_health metrics

**Action**: Update /review.md to update repository_health metrics from reviewer return

**Details**:
1. Extract metrics from reviewer return (sorry_count, axiom_count, build_errors, etc.)
2. Update repository_health.technical_debt section
3. Update repository_health.last_assessed timestamp
4. Add to status-sync-manager atomic update

**Estimated Effort**: 1 hour

**Owner**: Implementation team

**Files to Update**:
- .opencode/command/review.md (Stage 7 Postflight section)

**Example Update**:
```xml
<state_json_update>
  Update repository_health section:
  {
    "last_assessed": "{ISO8601 timestamp}",
    "technical_debt": {
      "sorry_count": {from reviewer metrics},
      "axiom_count": {from reviewer metrics},
      "build_errors": {from reviewer metrics},
      "status": "well-documented"
    },
    "review_artifacts": [
      {
        "timestamp": "{ISO8601}",
        "path": "{review_summary_artifact_path}",
        "scope": "{full|lean|docs}"
      }
    ]
  }
</state_json_update>
```

### Priority 5: LOW - Add maintenance/state.json update to /review

**Action**: Update /review.md to update maintenance/state.json with review operation details

**Details**:
1. Create maintenance/state.json if missing (self-healing)
2. Add review operation entry with timestamp, scope, metrics
3. Add to status-sync-manager atomic update

**Estimated Effort**: 1-2 hours

**Owner**: Implementation team

**Files to Update**:
- .opencode/command/review.md (Stage 7 Postflight section)

**Example Entry**:
```json
{
  "operation_id": 2,
  "timestamp": "2025-12-28T20:00:00Z",
  "type": "codebase_review",
  "scope": "full",
  "status": "completed",
  "metrics": {
    "sorry_count": 10,
    "axiom_count": 11,
    "build_errors": 3,
    "undocumented_tactics": 8,
    "missing_features": 3,
    "tasks_created": 5
  },
  "artifacts": [
    ".opencode/specs/207_codebase_review/summaries/review-summary.md"
  ],
  "registries_updated": [
    "Documentation/ProjectInfo/IMPLEMENTATION_STATUS.md",
    "Documentation/ProjectInfo/SORRY_REGISTRY.md",
    "Documentation/ProjectInfo/TACTIC_REGISTRY.md",
    "Documentation/ProjectInfo/FEATURE_REGISTRY.md"
  ]
}
```

### Priority 6: LOW - Update reviewer.md documentation

**Action**: Update reviewer.md to document state file update expectations

**Details**:
1. Add note about /review command's responsibility for state file updates
2. Document metrics return format for state.json integration
3. Clarify identified_tasks return format for task creation

**Estimated Effort**: 30 minutes

**Owner**: Documentation team

**Files to Update**:
- .opencode/agent/subagents/reviewer.md (integration_notes section)

---

## Risks & Mitigations

### Risk 1: Breaking Changes to /review Workflow

**Risk**: Integrating status-sync-manager may break existing /review workflows

**Likelihood**: Medium

**Impact**: High

**Mitigation**:
1. Test /review workflow thoroughly before deployment
2. Create backup of state.json before first /review invocation
3. Add rollback mechanism to status-sync-manager
4. Document migration path for existing review projects

### Risk 2: State File Corruption

**Risk**: Atomic update failures may corrupt state.json

**Likelihood**: Low

**Impact**: High

**Mitigation**:
1. Use two-phase commit with backup
2. Validate JSON before writing
3. Add self-healing for corrupted state files
4. Document manual recovery procedures

### Risk 3: Task Creation Failures

**Risk**: /task command failures may leave review incomplete

**Likelihood**: Medium

**Impact**: Medium

**Mitigation**:
1. Continue on task creation failure (don't abort review)
2. Log failed task descriptions for manual creation
3. Include failed task count in review summary
4. Provide manual task creation instructions

---

## Appendix

### A. Command Comparison Table

| Feature | /todo | /review | /research | /plan | /revise | /implement |
|---------|-------|---------|-----------|-------|---------|------------|
| **Purpose** | Cleanup | Survey | Research | Plan | Revise | Implement |
| **Creates Tasks** | No | Yes | No | No | No | No |
| **Updates Registries** | No | Yes | No | No | No | No |
| **Creates Artifacts** | No | Yes | Yes | Yes | Yes | Yes |
| **Uses status-sync-manager** | No | [FAIL] No | [PASS] Yes | [PASS] Yes | [PASS] Yes | [PASS] Yes |
| **Updates project state.json** | No | [FAIL] No | [PASS] Yes | [PASS] Yes | [PASS] Yes | [PASS] Yes |
| **Updates state.json** | Yes | [WARN] Partial | [PASS] Yes | [PASS] Yes | [PASS] Yes | [PASS] Yes |
| **Lazy Directory Creation** | No | [PASS] Yes | [PASS] Yes | [PASS] Yes | [PASS] Yes | [PASS] Yes |
| **Git Commit** | Yes | Yes | Yes | Yes | Yes | Yes |

### B. State File Update Patterns

**Current /review Updates**:
- [PASS] state.json.repository_health.review_artifacts
- [PASS] state.json.next_project_number
- [PASS] TODO.md (via /task command)
- [PASS] state.json.active_projects (via /task command)

**Missing /review Updates**:
- [FAIL] state.json.repository_health.last_assessed
- [FAIL] state.json.repository_health.technical_debt
- [FAIL] project state.json
- [FAIL] maintenance/state.json

**Recommended /review Updates**:
- [PASS] All current updates (keep)
- [PLUS] state.json.repository_health.last_assessed
- [PLUS] state.json.repository_health.technical_debt
- [PLUS] project state.json (lazy creation)
- [PLUS] maintenance/state.json (review operation entry)
- [PLUS] Use status-sync-manager for atomic updates

### C. Artifact Management Compliance

**/review Artifact Pattern**:
- Creates 1 artifact: summaries/review-summary.md
- NO separate summary artifact (review summary IS the summary)
- Summary metadata returned in return object (<100 tokens)
- Follows lazy directory creation
- Follows summary.md standard

**Compliance Check**:
- [PASS] Lazy directory creation
- [PASS] Single artifact (review summary)
- [PASS] No unnecessary summary artifact
- [PASS] Summary metadata in return object
- [PASS] Follows summary.md standard
- [FAIL] Missing project state.json

### D. Implementation Roadmap

**Phase 1: State File Integration (2-3 hours)**
1. Update /review.md Stage 7 to use status-sync-manager
2. Add project state.json creation
3. Update state.json repository_health metrics
4. Test atomic updates with rollback

**Phase 2: Task Creation Clarification (1 hour)**
1. Update /review.md Stage 6 with task creation pattern
2. Document error handling for task creation failures
3. Add task creation examples

**Phase 3: Maintenance Integration (1-2 hours)**
1. Add maintenance/state.json update to /review
2. Create self-healing for missing maintenance/state.json
3. Test maintenance operation logging

**Phase 4: Documentation Updates (1 hour)**
1. Update reviewer.md with state file expectations
2. Update artifact-management.md with /review example
3. Update command-lifecycle.md with /review variations

**Total Estimated Effort**: 5-7 hours

### E. References

**Command Files**:
- .opencode/command/todo.md
- .opencode/command/review.md
- .opencode/command/revise.md
- .opencode/command/research.md
- .opencode/command/plan.md
- .opencode/command/implement.md

**Agent Files**:
- .opencode/agent/subagents/reviewer.md

**Standard Files**:
- .opencode/context/core/system/artifact-management.md
- .opencode/context/core/workflows/command-lifecycle.md
- .opencode/context/core/standards/report.md
- .opencode/context/core/standards/summary.md

**State Files**:
- .opencode/specs/state.json
- .opencode/specs/maintenance/state.json
- .opencode/specs/maintenance/maintenance-report-20251224.md

---

**End of Research Report**
