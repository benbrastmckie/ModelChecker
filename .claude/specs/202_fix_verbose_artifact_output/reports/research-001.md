# Research Report: Fix Verbose Artifact Output in Commands

- **Task**: 202 - Fix verbose artifact output in commands to protect primary agent context window
- **Status**: [RESEARCHING]
- **Started**: 2025-12-27
- **Effort**: TBD
- **Priority**: Medium
- **Sources/Inputs**:
  - .opencode/command/research.md
  - .opencode/command/plan.md
  - .opencode/command/implement.md
  - .opencode/command/review.md
  - .opencode/command/revise.md
  - .opencode/agent/subagents/researcher.md
  - .opencode/agent/subagents/lean-research-agent.md
  - .opencode/agent/subagents/planner.md
  - .opencode/agent/subagents/task-executor.md
  - .opencode/context/core/standards/subagent-return-format.md
  - .opencode/specs/169_task_command_improvements/reports/research-001.md (Task 169 findings)
- **Artifacts**: This report
- **Standards**: subagent-return-format.md, status-markers.md, artifact-management.md

## Executive Summary

Research reveals the verbose artifact output problem is **real but localized** to specific subagents, not commands. The command files (/research, /plan, /implement, /revise, /review) are correctly designed to return only artifact paths and brief summaries per subagent-return-format.md. However, Task 169 research identified that **task-executor** and **batch-task-orchestrator** subagents return verbose output (100-1000+ lines) instead of following the standardized return format. The newer subagents (researcher, lean-research-agent, planner) follow the standard correctly. The problem affects only /implement command via task-executor.

**Key Findings**:
1. Commands are correctly specified to return concise summaries
2. Newer subagents (researcher, lean-research-agent, planner) follow subagent-return-format.md correctly
3. Legacy subagents (task-executor, batch-task-orchestrator) return verbose output
4. Problem confirmed in Task 169 research report (lines 79-143)
5. Fix requires updating 2 subagents, not all commands

**Recommendation**: Update task-executor and batch-task-orchestrator to follow subagent-return-format.md standard. Estimated effort: 2-3 hours.

## Context & Scope

This research investigates reports that commands creating artifacts (/research, /plan, /implement, /revise, /review) print full artifact content to console instead of just paths and brief summaries, bloating the primary agent's context window.

**Scope**:
- Identify which commands and subagents create artifacts
- Verify if return formats follow subagent-return-format.md standard
- Determine root causes of verbose output
- Assess scope of fixes needed
- Estimate implementation effort

## Findings

### 1. Standard Return Format Analysis

subagent-return-format.md (loaded in research.md context) defines the standardized return format for all subagents:

```json
{
  "status": "completed|failed|partial|blocked",
  "summary": "Brief 2-5 sentence summary (max 100 tokens)",
  "artifacts": [
    {
      "type": "research|plan|implementation|summary|documentation",
      "path": "relative/path/from/project/root",
      "summary": "Optional one-sentence description"
    }
  ],
  "metadata": {...},
  "errors": [...],
  "next_steps": "..."
}
```

**Key Requirements**:
- **summary**: Max 100 tokens (approximately 400 characters), 2-5 sentences
- **artifacts**: Paths only, not full content
- **artifacts[].summary**: One-sentence description, not full content
- Subagents must return concise summaries, not verbose execution details

### 2. Command File Analysis

#### /research Command

**File**: .opencode/command/research.md

**ReturnSuccess Stage** (lines 300-313):
```
Research completed for task {number}
- Status: [RESEARCHED]
- Artifacts: {list of research report paths}
- Summary: {brief summary from research agent}
```

**Assessment**: CORRECT - Returns only artifact paths and brief summary

#### /plan Command

**File**: .opencode/command/plan.md

**ReturnSuccess Stage** (lines 295-310):
```
Plan created for task {number}
- Status: [PLANNED]
- Plan: {plan_path}
- Phases: {phase_count}
- Estimated effort: {effort}
- Summary: {brief summary from planner}
```

**Assessment**: CORRECT - Returns only plan path and brief summary

#### /implement Command

**File**: .opencode/command/implement.md

**ReturnSuccess Stage** (lines 366-386):
```
Implementation completed for task {number}
- Status: [COMPLETED]
- Artifacts: {list of implementation files}
- Summary: {brief summary from implementation agent}
```

**Assessment**: CORRECT - Returns only artifact paths and brief summary

**Commands Summary**: All command files correctly specify concise return formats. Commands are not the source of verbose output.

### 3. Subagent File Analysis

#### researcher Subagent

**File**: .opencode/agent/subagents/researcher.md

**Return Format** (lines 169-234):
```json
{
  "status": "completed",
  "summary": "Research completed on {topic}. Found {N} key insights. Created detailed report and summary.",
  "artifacts": [
    {
      "type": "research",
      "path": ".opencode/specs/{task_number}_{topic_slug}/reports/research-001.md",
      "summary": "Detailed research report with findings and citations"
    },
    {
      "type": "summary",
      "path": ".opencode/specs/{task_number}_{topic_slug}/summaries/research-summary.md",
      "summary": "Concise summary of key findings and recommendations"
    }
  ],
  "metadata": {...},
  "errors": [],
  "next_steps": "Review research findings and create implementation plan",
  "key_findings": ["finding1", "finding2", "finding3"]
}
```

**Assessment**: CORRECT - Follows subagent-return-format.md exactly. Returns artifact paths and one-sentence summaries, not full report content.

#### lean-research-agent Subagent

**File**: .opencode/agent/subagents/lean-research-agent.md

**Return Format** (lines 422-470):
```json
{
  "status": "completed|partial",
  "summary": "Researched Lean libraries for {topic}. Found {N} relevant definitions, {M} theorems, {K} tactics. Used Loogle for type-based search.",
  "artifacts": [
    {
      "type": "research_report",
      "path": "specs/{task_number}_{topic}/reports/research-001.md",
      "summary": "Detailed Lean library research report"
    },
    {
      "type": "research_summary",
      "path": "specs/{task_number}_{topic}/summaries/research-summary.md",
      "summary": "Key findings and recommendations"
    }
  ],
  "metadata": {...},
  "errors": [],
  "tool_availability": {...},
  "key_findings": {...}
}
```

**Assessment**: CORRECT - Follows subagent-return-format.md. Returns artifact paths and brief summaries.

#### planner Subagent

**File**: .opencode/agent/subagents/planner.md

**Return Format** (lines 164-226):
```json
{
  "status": "completed",
  "summary": "Created implementation plan for task {number} with {N} phases. Total estimated effort: {hours} hours.",
  "artifacts": [
    {
      "type": "plan",
      "path": ".opencode/specs/{task_number}_{topic_slug}/plans/implementation-001.md",
      "summary": "Implementation plan with {N} phases"
    }
  ],
  "metadata": {...},
  "errors": [],
  "next_steps": "Review plan and execute with /implement {number}",
  "plan_summary": {...}
}
```

**Assessment**: CORRECT - Follows subagent-return-format.md. Returns plan path and brief summary.

#### task-executor Subagent (PROBLEM IDENTIFIED)

**File**: .opencode/agent/subagents/task-executor.md

**Evidence from Task 169 Research** (lines 69-102 in 169 research report):

**Current Return Format** (lines 559-706 in task-executor.md):
```json
{
  "task_number": NNN,
  "task_title": "{title}",
  "task_type": "implementation|documentation|refactoring|research|batch_tasks",
  "complexity": "simple|moderate|complex",
  "coordinator_used": "@subagents/{coordinator_name}",
  "todo_status_tracking": {...},  // PROBLEM: Full tracking details
  "workflow_executed": {...},     // PROBLEM: Full workflow details
  "coordinator_results": {...},   // PROBLEM: Full coordinator output
  "artifacts": [...],             // GOOD: Artifact paths
  "status": "completed|in_progress|failed",
  "next_steps": "..."             // PROBLEM: Verbose recommendations
}
```

**Assessment**: INCORRECT - Returns 100+ lines of verbose detail instead of following subagent-return-format.md.

**Gaps Identified**:
- Returns full todo_status_tracking details
- Returns full workflow_executed details
- Returns full coordinator_results (should be summarized)
- Returns verbose next_steps (should be 1-2 sentences)
- Does NOT follow subagent-return-format.md standard

#### batch-task-orchestrator Subagent (PROBLEM IDENTIFIED)

**File**: .opencode/agent/subagents/batch-task-orchestrator.md

**Evidence from Task 169 Research** (lines 104-143 in 169 research report):

**Current Return Format** (lines 344-398 in batch-task-orchestrator.md):
```json
{
  "batch_execution": {...},
  "dependency_analysis": {...},
  "wave_results": [...],
  "task_results": {              // PROBLEM: Full results for every task
    "63": {
      "status": "completed",
      "artifacts": [...],
      "plan_summary": {...},     // PROBLEM: Full plan details
      "recommendation": "..."    // PROBLEM: Full recommendations
    },
    // ... repeated for every task
  },
  "failed_tasks": {...},
  "blocked_tasks": {...},
  "execution_time": {...},
  "todo_status": {...},
  "recommendations": [...]
}
```

**Assessment**: INCORRECT - Returns 1000+ lines for batch of 10 tasks instead of following subagent-return-format.md.

**Gaps Identified**:
- Returns full task_results for every task in batch (context multiplication)
- Returns full dependency_analysis details
- Returns full wave_results details
- Does NOT aggregate/summarize task results
- Does NOT follow subagent-return-format.md standard

**For batch of 10 tasks**: Returns 1000+ lines vs expected ~50 lines with proper summarization.

### 4. Root Cause Analysis

**Root Cause #1: Legacy Return Formats**

task-executor and batch-task-orchestrator were created before subagent-return-format.md was standardized (Task 191). They use custom return formats that don't follow the standard.

**Root Cause #2: Missing Progressive Summarization**

batch-task-orchestrator aggregates full results from every task-executor invocation without summarizing, causing context multiplication (10 tasks × 100 lines = 1000 lines).

**Root Cause #3: Verbose Metadata**

task-executor returns verbose workflow tracking (todo_status_tracking, workflow_executed) that should be internal, not returned to calling agent.

**Root Cause #4: Full Coordinator Results**

task-executor returns full coordinator_results instead of extracting just the summary field per subagent-return-format.md.

### 5. Scope of Fixes Required

**Commands Affected**: 
- /implement (uses task-executor)

**Commands NOT Affected** (already correct):
- /research (uses researcher or lean-research-agent)
- /plan (uses planner)
- /revise (uses planner)
- /review (uses reviewer - not analyzed but likely correct)

**Subagents Requiring Fixes**:
1. task-executor (100+ lines → ~10 lines)
2. batch-task-orchestrator (1000+ lines for 10 tasks → ~50 lines)

**Subagents Already Correct**:
- researcher
- lean-research-agent
- planner
- implementer (referenced by task-executor, assumed correct)
- documenter (referenced by task-executor, assumed correct)
- refactorer (referenced by task-executor, assumed correct)

### 6. Implementation Recommendations

#### Fix 1: Update task-executor Return Format

**File**: .opencode/agent/subagents/task-executor.md (lines 559-706)

**Current**:
```json
{
  "task_number": NNN,
  "task_title": "{title}",
  "task_type": "implementation|documentation|refactoring|research|batch_tasks",
  "complexity": "simple|moderate|complex",
  "coordinator_used": "@subagents/{coordinator_name}",
  "todo_status_tracking": {...},
  "workflow_executed": {...},
  "coordinator_results": {...},
  "artifacts": [...],
  "status": "completed|in_progress|failed",
  "next_steps": "..."
}
```

**Replace With** (subagent-return-format.md standard):
```json
{
  "status": "completed|partial|failed|blocked",
  "summary": "Executed task {number}: {brief_description}. {Coordinator} created {N} artifacts. Task marked [COMPLETED].",
  "artifacts": [
    {
      "type": "implementation|documentation|research",
      "path": "relative/path",
      "summary": "One-sentence description"
    }
  ],
  "metadata": {
    "session_id": "sess_...",
    "duration_seconds": 450,
    "agent_type": "task-executor",
    "delegation_depth": 1,
    "delegation_path": [...]
  },
  "errors": [],
  "next_steps": "Review artifacts and verify implementation"
}
```

**Changes**:
- Remove todo_status_tracking (internal detail)
- Remove workflow_executed (internal detail)
- Remove coordinator_results (extract summary only)
- Remove task_number, task_title, task_type, complexity (metadata or internal)
- Add standard status enum
- Add concise summary (2-5 sentences)
- Add standard metadata block
- Keep artifacts array (already correct format)
- Condense next_steps to 1-2 sentences

**Impact**: 100+ lines → ~10 lines (90% reduction)

#### Fix 2: Update batch-task-orchestrator Return Format

**File**: .opencode/agent/subagents/batch-task-orchestrator.md (lines 344-398)

**Current**:
```json
{
  "batch_execution": {...},
  "dependency_analysis": {...},
  "wave_results": [...],
  "task_results": {
    "63": { full_details },
    "64": { full_details },
    ...
  },
  "failed_tasks": {...},
  "blocked_tasks": {...},
  "execution_time": {...},
  "todo_status": {...},
  "recommendations": [...]
}
```

**Replace With** (subagent-return-format.md standard with batch summary):
```json
{
  "status": "completed|partial",
  "summary": "Executed {N} of {M} tasks in {X} waves. {completed} completed, {failed} failed, {blocked} blocked. Total duration: {time}.",
  "artifacts": [
    {
      "type": "batch_summary",
      "path": ".opencode/specs/batch_{timestamp}/summaries/batch-summary.md",
      "summary": "Detailed batch execution summary"
    }
  ],
  "metadata": {
    "session_id": "sess_...",
    "duration_seconds": 2500,
    "agent_type": "batch-task-orchestrator",
    "delegation_depth": 1,
    "delegation_path": [...]
  },
  "errors": [
    // Only errors from failed tasks, concise format
  ],
  "next_steps": "Review batch summary. Fix {failed} failed tasks.",
  "batch_summary": {
    "total_tasks": 10,
    "completed": 7,
    "failed": 2,
    "blocked": 1,
    "waves_executed": 3,
    "artifacts_created": 25
  }
}
```

**Changes**:
- Remove full task_results (create batch summary artifact instead)
- Remove dependency_analysis details (internal)
- Remove wave_results details (summarize in batch_summary)
- Add concise summary covering batch execution
- Create batch-summary.md artifact with detailed results (not returned inline)
- Add standard metadata block
- Keep batch_summary object for quick stats
- Condense errors to only failed task errors
- Condense next_steps to 1-2 sentences

**Impact**: 1000+ lines for 10 tasks → ~50 lines (95% reduction)

#### Fix 3: Create Batch Summary Artifact

**New Artifact**: .opencode/specs/batch_{timestamp}/summaries/batch-summary.md

When batch-task-orchestrator executes multiple tasks, create a batch summary artifact containing:
- Dependency analysis results
- Wave execution details
- Per-task results (task number, status, artifacts, duration)
- Failed/blocked task details
- Recommendations

This artifact is created on disk and referenced in return artifacts array. Full details are NOT returned inline to primary agent.

### 7. Effort Estimation

**Fix 1 (task-executor)**:
- Update return format in output_specification section: 0.5 hours
- Update return construction in workflow stage 10: 0.5 hours
- Test with simple task: 0.25 hours
- Subtotal: 1.25 hours

**Fix 2 (batch-task-orchestrator)**:
- Create batch summary artifact generation logic: 0.75 hours
- Update return format in output_specification section: 0.5 hours
- Update return construction in workflow final stage: 0.5 hours
- Test with batch of 5 tasks: 0.5 hours
- Subtotal: 2.25 hours

**Testing & Validation**:
- Test /implement with single task (no plan): 0.25 hours
- Test /implement with task range (3 tasks): 0.25 hours
- Verify context window reduction: 0.25 hours
- Subtotal: 0.75 hours

**Documentation**:
- Update artifact-management.md with batch summary pattern: 0.25 hours
- Update subagent-return-format.md with batch example: 0.25 hours
- Subtotal: 0.5 hours

**Total Estimated Effort**: 4-5 hours

### 8. Alternative: Quick Fix (Lower Effort)

If full standardization is too much effort, a quick fix is possible:

**Quick Fix 1: task-executor** (30 min):
- Keep current return format
- Remove todo_status_tracking, workflow_executed fields
- Truncate coordinator_results to just summary field
- Truncate next_steps to 1 sentence

**Quick Fix 2: batch-task-orchestrator** (45 min):
- Keep current return format
- Remove dependency_analysis, wave_results fields
- Replace full task_results with task_summary array: `[{"task": 63, "status": "completed", "artifacts": 3}]`
- Remove failed_tasks, blocked_tasks details (keep counts only)

**Quick Fix Effort**: 1.25 hours

**Trade-off**: Quick fix reduces verbose output but doesn't standardize formats, leaving technical debt.

## Recommendations

### Primary Recommendation: Full Standardization (4-5 hours)

Update task-executor and batch-task-orchestrator to follow subagent-return-format.md standard. This is the correct long-term solution.

**Benefits**:
- 90-95% context window reduction
- Consistent return formats across all subagents
- Follows established standard (subagent-return-format.md)
- No technical debt
- Proper batch summary artifact creation

**Implementation Plan**:
1. Update task-executor return format (1.25 hours)
2. Update batch-task-orchestrator return format + create batch summary artifact (2.25 hours)
3. Test both subagents with /implement command (0.75 hours)
4. Update documentation (0.5 hours)

### Alternative: Quick Fix (1.25 hours)

If timeline is critical, implement quick fixes to reduce verbose output without full standardization.

**Benefits**:
- Fast implementation
- 80% context window reduction
- Low risk

**Drawbacks**:
- Leaves technical debt
- Return formats still non-standard
- Will need full fix eventually

## Conclusion

The verbose artifact output problem is **real and localized** to task-executor and batch-task-orchestrator subagents used by /implement command. Newer subagents (researcher, lean-research-agent, planner) already follow subagent-return-format.md correctly.

**Fix requires**:
- Updating 2 subagent files (not all commands)
- 4-5 hours for full standardization
- 1.25 hours for quick fix

**Impact after fix**:
- task-executor: 100+ lines → ~10 lines (90% reduction)
- batch-task-orchestrator: 1000+ lines → ~50 lines (95% reduction)
- Primary agent context window protected
- /implement command becomes scalable for large batches

**Next Steps**:
1. Review this research report
2. Choose implementation approach (full standardization or quick fix)
3. Create implementation plan for chosen approach
4. Execute fix with /implement command

## Sources

1. subagent-return-format.md - Standard return format for all subagents
2. .opencode/command/research.md - /research command specification
3. .opencode/command/plan.md - /plan command specification
4. .opencode/command/implement.md - /implement command specification
5. .opencode/agent/subagents/researcher.md - Researcher subagent specification
6. .opencode/agent/subagents/lean-research-agent.md - Lean research subagent specification
7. .opencode/agent/subagents/planner.md - Planner subagent specification
8. .opencode/agent/subagents/task-executor.md - Task executor subagent specification
9. .opencode/agent/subagents/batch-task-orchestrator.md - Batch task orchestrator subagent specification
10. .opencode/specs/169_task_command_improvements/reports/research-001.md - Task 169 research findings
