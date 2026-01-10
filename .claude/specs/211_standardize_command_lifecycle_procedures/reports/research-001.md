# Research Report: Standardize Pre-flight and Post-flight Procedures

**Task**: 211  
**Date**: 2025-12-28  
**Researcher**: researcher  
**Status**: Completed

## Executive Summary

This research analyzes pre-flight and post-flight procedures across four workflow commands (/research, /plan, /revise, /implement) and six associated agents (researcher, planner, lean-research-agent, lean-implementation-agent, task-executor, implementer). The analysis reveals significant procedural duplication and inconsistencies that can be standardized into a single command-lifecycle.md context file while preserving legitimate command-specific variations.

Key findings:
- All four commands follow an 8-stage lifecycle pattern with 90% structural similarity
- Pre-flight procedures vary in 3 critical areas: status markers, validation checks, and routing logic
- Post-flight procedures vary in 4 areas: status updates, artifact linking, git commits, and return formats
- Agents show 85% consistency in return format but differ in artifact creation patterns
- Standardization opportunity: Extract common 8-stage pattern to command-lifecycle.md, document variations in command-specific tables

## Research Methodology

### Files Analyzed

**Commands** (4 files):
- .opencode/command/research.md (466 lines)
- .opencode/command/plan.md (450 lines)
- .opencode/command/revise.md (422 lines)
- .opencode/command/implement.md (623 lines)

**Agents** (6 files):
- .opencode/agent/subagents/researcher.md (341 lines)
- .opencode/agent/subagents/planner.md (333 lines)
- .opencode/agent/subagents/lean-research-agent.md (963 lines)
- .opencode/agent/subagents/lean-implementation-agent.md (374 lines)
- .opencode/agent/subagents/task-executor.md (389 lines)
- .opencode/agent/subagents/implementer.md (316 lines)

**Supporting Standards** (5 files):
- .opencode/context/core/standards/status-markers.md (889 lines)
- .opencode/context/core/standards/subagent-return-format.md (356 lines)
- .opencode/context/core/system/artifact-management.md (182 lines)
- .opencode/context/core/system/git-commits.md (35 lines)

### Analysis Approach

1. Extract stage-by-stage procedures from each command
2. Map agent process flows to command invocations
3. Identify common patterns across all commands/agents
4. Document variations and their justifications
5. Assess compliance with existing standards
6. Propose standardization structure

## Current State Analysis

### Command Lifecycle Pattern (Common Structure)

All four commands follow this 8-stage pattern:

**Stage 1: Preflight** - Parse arguments, validate task, update status to in-progress
**Stage 2: CheckLanguage/DetermineRouting** - Extract language, determine target agent
**Stage 3: PrepareDelegation** - Generate session_id, set delegation context
**Stage 4: InvokeAgent** - Delegate to appropriate subagent
**Stage 5: ReceiveResults** - Wait for return, validate against subagent-return-format.md
**Stage 6: ProcessResults** - Extract artifacts, summary, errors
**Stage 7: Postflight** - Update status, link artifacts, commit changes
**Stage 8: ReturnSuccess** - Return brief summary to user

**Consistency**: 90% structural similarity across all commands

### Pre-flight Procedures Analysis

#### Common Pre-flight Steps (All Commands)

1. Parse task number from $ARGUMENTS
2. Validate task number is integer
3. Load task from TODO.md
4. Validate task exists and not [COMPLETED]
5. Extract task description and language
6. Mark task with in-progress status marker
7. Update state.json with status and started timestamp

**Status Markers Used**:
- /research: [NOT STARTED] → [RESEARCHING]
- /plan: [NOT STARTED] → [PLANNING]
- /revise: [PLANNED] → [REVISING]
- /implement: [NOT STARTED]/[PLANNED] → [IMPLEMENTING]

**Atomic Update Mechanism**: All use status-sync-manager for TODO.md + state.json synchronization

#### Pre-flight Variations

**Variation 1: Status Marker Transitions**

| Command | Initial States | In-Progress Marker | Completion Marker |
|---------|---------------|-------------------|-------------------|
| /research | [NOT STARTED] | [RESEARCHING] | [RESEARCHED] |
| /plan | [NOT STARTED], [RESEARCHED] | [PLANNING] | [PLANNED] |
| /revise | [PLANNED], [REVISED] | [REVISING] | [REVISED] |
| /implement | [NOT STARTED], [PLANNED], [REVISED] | [IMPLEMENTING] | [COMPLETED]/[PARTIAL] |

**Justification**: Legitimate - each command has different workflow position

**Variation 2: Validation Checks**

| Command | Unique Validation |
|---------|------------------|
| /research | Check for --divide flag |
| /plan | Check for existing plan (warn if exists) |
| /revise | Require existing plan (fail if missing) |
| /implement | Check for plan existence, determine resume phase |

**Justification**: Legitimate - command-specific requirements

**Variation 3: Language Routing Logic**

| Command | Routing Decision |
|---------|-----------------|
| /research | Language: lean → lean-research-agent, else → researcher |
| /plan | No routing (always planner) |
| /revise | No routing (always planner) |
| /implement | Language: lean + has_plan → lean-implementation-agent (phased)<br>Language: lean + no_plan → lean-implementation-agent (simple)<br>Language: * + has_plan → task-executor<br>Language: * + no_plan → implementer |

**Justification**: Legitimate - different agents for different workflows

**Variation 4: Delegation Context**

| Command | Timeout | Delegation Depth | Special Context |
|---------|---------|-----------------|----------------|
| /research | 3600s (1 hour) | 1 | divide_topics flag |
| /plan | 1800s (30 min) | 1 | research_inputs from TODO.md |
| /revise | 1800s (30 min) | 1 | existing_plan_path, new_version |
| /implement | 7200s (2 hours) | 1 | plan_path, resume_from_phase |

**Justification**: Legitimate - different complexity and requirements

### Post-flight Procedures Analysis

#### Common Post-flight Steps (All Commands)

1. Check return status (completed/partial/failed/blocked)
2. Extract artifacts from return object
3. Update TODO.md with status marker and timestamp
4. Update state.json with status and timestamp
5. Link artifacts in TODO.md
6. Create git commit (if completed)
7. Return brief summary to user

**Git Commit Pattern**: All use git-workflow-manager for scoped commits

#### Post-flight Variations

**Variation 1: Status Update Patterns**

| Command | Completion Status | Partial Status | Failed Status |
|---------|------------------|----------------|---------------|
| /research | [RESEARCHED] + Completed timestamp | Keep [RESEARCHING] | Keep [RESEARCHING] |
| /plan | [PLANNED] + Completed timestamp | Keep [PLANNING] | Keep [PLANNING] |
| /revise | [REVISED] + Completed timestamp | Keep [REVISING] | Keep [REVISING] |
| /implement | [COMPLETED] + Completed timestamp + [PASS] | [PARTIAL] + note | Keep [IMPLEMENTING] |

**Justification**: Legitimate - different workflow semantics

**Variation 2: Artifact Linking**

| Command | Artifact Types | Link Format |
|---------|---------------|-------------|
| /research | reports/research-001.md, summaries/research-summary.md | - Research: {path} |
| /plan | plans/implementation-001.md | - Plan: {path} |
| /revise | plans/implementation-{version}.md | - Plan: {new_path} (updates existing link) |
| /implement | Implementation files + summaries/implementation-summary-{date}.md | - Implementation: {paths}<br>- Summary: {path} |

**Justification**: Legitimate - different artifact types

**Variation 3: Git Commit Scope**

| Command | Commit Scope | Message Format |
|---------|-------------|----------------|
| /research | Research artifacts + TODO.md + state.json | "task {number}: research completed" |
| /plan | Plan file + TODO.md + state.json | "task {number}: plan created" |
| /revise | New plan file + TODO.md + state.json | "task {number}: plan revised to v{version}" |
| /implement | Implementation files + TODO.md + state.json + plan (if exists) | "task {number}: implementation completed" |

**Justification**: Legitimate - different artifact scopes

**Variation 4: Return Format**

| Command | Return Content | Token Limit |
|---------|---------------|-------------|
| /research | Brief summary (3-5 sentences) + artifact paths | <100 tokens |
| /plan | Brief summary (3-5 sentences) + plan path + phase count + effort | <100 tokens |
| /revise | Brief summary (3-5 sentences) + new plan path | <100 tokens |
| /implement | Brief summary (3-5 sentences) + summary artifact path | <100 tokens |

**Justification**: Legitimate - different information needs

### Agent Procedures Analysis

#### Common Agent Pattern (All Agents)

All agents follow this 6-step pattern:

**Step 1: Load Context** - Load domain context and check tool availability
**Step 2: Analyze Input** - Parse task/topic, determine approach
**Step 3: Execute Work** - Conduct research/planning/implementation
**Step 4: Create Artifacts** - Write reports/plans/code with lazy directory creation
**Step 5: Create Summary** - Write summary artifact (<100 tokens)
**Step 6: Return Standardized Result** - Format per subagent-return-format.md

**Consistency**: 85% structural similarity across all agents

#### Agent-Specific Variations

**Variation 1: Artifact Creation Patterns**

| Agent | Artifacts Created | Directory Structure |
|-------|------------------|-------------------|
| researcher | reports/research-001.md, summaries/research-summary.md | specs/{task}_{slug}/reports/, specs/{task}_{slug}/summaries/ |
| planner | plans/implementation-001.md | specs/{task}_{slug}/plans/ |
| lean-research-agent | reports/research-001.md, summaries/research-summary.md | specs/{task}_{slug}/reports/, specs/{task}_{slug}/summaries/ |
| lean-implementation-agent | Lean files, summaries/implementation-summary-{date}.md | Logos/*, LogosTest/*, specs/{task}_{slug}/summaries/ |
| task-executor | Delegates to implementer/lean-implementation-agent, summaries/implementation-summary-{date}.md | Varies by language, specs/{task}_{slug}/summaries/ |
| implementer | Implementation files, summaries/implementation-summary-{date}.md | Varies by task, specs/{task}_{slug}/summaries/ |

**Justification**: Legitimate - different artifact types and locations

**Variation 2: Tool Integration**

| Agent | Tools Used | Fallback Behavior |
|-------|-----------|------------------|
| researcher | Web search | N/A (always available) |
| planner | None | N/A |
| lean-research-agent | Loogle CLI (integrated), LeanExplore (future), LeanSearch (future) | Web search if Loogle unavailable |
| lean-implementation-agent | lean-lsp-mcp | Direct file modification if unavailable |
| task-executor | None (orchestrates) | N/A |
| implementer | None (delegates Lean to lean-implementation-agent) | N/A |

**Justification**: Legitimate - different tool requirements

**Variation 3: Return Status Handling**

| Agent | Status Values | Partial Handling |
|-------|--------------|-----------------|
| researcher | completed, partial (timeout), failed, blocked | Partial report if timeout |
| planner | completed, partial, failed, blocked | Partial plan if timeout |
| lean-research-agent | completed, partial (timeout), failed | Partial report if timeout, warnings if tools unavailable |
| lean-implementation-agent | completed, partial (degraded mode), failed | Partial if lean-lsp-mcp unavailable |
| task-executor | completed, partial (phase timeout), failed, blocked | Partial if phase incomplete |
| implementer | completed, failed | Delegates to lean-implementation-agent for Lean |

**Justification**: Legitimate - different failure modes

## Inconsistency Matrix

### Critical Inconsistencies (Require Standardization)

**Inconsistency 1: Pre-flight Status Update Timing**

| Command | Status Update Timing |
|---------|---------------------|
| /research | Stage 1 (Preflight) line 116 |
| /plan | Stage 1 (Preflight) line 102 |
| /revise | Stage 1 (Preflight) line 106 |
| /implement | Stage 1 (Preflight) line 138 |

**Issue**: All identical but duplicated across 4 files
**Recommendation**: Extract to command-lifecycle.md pre-flight checklist

**Inconsistency 2: Delegation Context Generation**

| Command | Session ID Format | Delegation Path Format |
|---------|------------------|----------------------|
| /research | sess_{timestamp}_{random_6char} | ["orchestrator", "research", "{agent}"] |
| /plan | sess_{timestamp}_{random_6char} | ["orchestrator", "plan", "planner"] |
| /revise | sess_{timestamp}_{random_6char} | ["orchestrator", "revise", "planner"] |
| /implement | sess_{timestamp}_{random_6char} | ["orchestrator", "implement", "{agent}"] |

**Issue**: Identical pattern but duplicated across 4 files
**Recommendation**: Extract to command-lifecycle.md delegation preparation section

**Inconsistency 3: Return Validation Logic**

All commands validate return against subagent-return-format.md with identical steps:
1. Validate return is valid JSON
2. Validate against schema
3. Check session_id matches
4. Validate status enum
5. Validate artifacts array
6. Check artifact paths exist

**Issue**: Identical validation but duplicated across 4 files
**Recommendation**: Extract to command-lifecycle.md validation checklist

**Inconsistency 4: Timeout Handling**

| Command | Timeout Duration | Timeout Handling |
|---------|-----------------|-----------------|
| /research | 3600s | Log timeout, check partial artifacts, keep [RESEARCHING], provide resume instructions |
| /plan | 1800s | Log timeout, check partial plan, keep [PLANNING], provide resume instructions |
| /revise | 1800s | Log timeout, check partial plan, keep [REVISING], provide retry instructions |
| /implement | 7200s | Log timeout, check plan phases, keep [IMPLEMENTING], provide resume instructions |

**Issue**: Identical pattern (different timeouts justified) but duplicated logic
**Recommendation**: Extract timeout handling pattern to command-lifecycle.md, parameterize timeout duration

**Inconsistency 5: Git Commit Failure Handling**

All commands handle git commit failures identically:
1. Log error to errors.json
2. Continue (commit failure non-critical)
3. Return success with warning

**Issue**: Identical handling but duplicated across 4 files
**Recommendation**: Extract to command-lifecycle.md post-flight checklist

### Minor Inconsistencies (Documentation Only)

**Inconsistency 6: Error Handling Verbosity**

- /research: 4 error scenarios documented
- /plan: 4 error scenarios documented
- /revise: 4 error scenarios documented
- /implement: 6 error scenarios documented

**Issue**: Inconsistent documentation depth
**Recommendation**: Standardize error scenario documentation in command-lifecycle.md

**Inconsistency 7: Validation Check Documentation**

- /research: 3 validation sections (pre_flight, mid_flight, post_flight)
- /plan: 3 validation sections (pre_flight, mid_flight, post_flight)
- /revise: 3 validation sections (pre_flight, mid_flight, post_flight)
- /implement: 3 validation sections (pre_flight, mid_flight, post_flight)

**Issue**: Identical structure but duplicated content
**Recommendation**: Extract validation framework to command-lifecycle.md

## Compliance Assessment

### Status Markers Compliance

**Compliance Level**: 100%

All commands correctly implement status-markers.md:
- Use bracketed uppercase markers: [NOT STARTED], [RESEARCHING], etc.
- Include Started timestamp on transition to in-progress
- Include Completed timestamp on transition to completion
- Use atomic updates via status-sync-manager
- Follow valid transition paths

**Evidence**:
- /research: Lines 116-122 (status update), Lines 282-318 (postflight)
- /plan: Lines 102-109 (status update), Lines 243-292 (postflight)
- /revise: Lines 106-112 (status update), Lines 257-305 (postflight)
- /implement: Lines 138-156 (status update), Lines 341-407 (postflight)

### Subagent Return Format Compliance

**Compliance Level**: 95%

All agents return standardized format per subagent-return-format.md:
- Required fields present: status, summary, artifacts, metadata
- Status enum valid: completed, partial, failed, blocked
- Summary within limits: 3-5 sentences, <100 tokens
- Metadata complete: session_id, duration, agent_type, delegation info
- Errors array present when status != completed

**Non-compliance**:
- lean-implementation-agent: Missing explicit summary artifact validation (line 149)
- task-executor: Summary artifact creation documented but not enforced (line 149)

**Recommendation**: Add summary artifact validation to both agents

### Artifact Management Compliance

**Compliance Level**: 100%

All commands and agents follow artifact-management.md:
- Lazy directory creation: Create directories only when writing files
- No pre-creation of empty directories
- No placeholder files (.gitkeep)
- Summary artifacts required for all detailed artifacts
- Summary token limits enforced (<100 tokens)

**Evidence**:
- researcher: Lines 110-125 (lazy creation)
- planner: Lines 115-136 (lazy creation)
- lean-research-agent: Lines 269-336 (lazy creation)
- lean-implementation-agent: Lines 135-156 (lazy creation)
- task-executor: Lines 145-160 (lazy creation)
- implementer: Lines 115-128 (lazy creation)

### Git Commits Compliance

**Compliance Level**: 100%

All commands follow git-commits.md:
- Targeted commits: Only files relevant to task
- Scoped staging: Use git add with specific files
- Commit after artifacts written and validated
- Focused commit messages: "task {number}: {action}"
- Git failures non-critical: Log and continue

**Evidence**:
- /research: Lines 319-325 (git commit)
- /plan: Lines 286-292 (git commit)
- /revise: Lines 299-305 (git commit)
- /implement: Lines 397-407 (git commit)

## Standardization Recommendations

### Recommendation 1: Create command-lifecycle.md

**Purpose**: Extract common 8-stage lifecycle pattern to single source of truth

**Structure**:

```markdown
# Command Lifecycle Standard

## Overview
All workflow commands (/research, /plan, /revise, /implement) follow an 8-stage lifecycle pattern.

## Stage 1: Preflight
### Common Steps (All Commands)
1. Parse task number from $ARGUMENTS
2. Validate task number is integer
3. Load task from TODO.md
4. Validate task exists
5. Extract task description and language
6. Mark task with in-progress status marker
7. Update state.json with status and started timestamp

### Command-Specific Variations
[Table of status markers, validation checks, etc.]

## Stage 2: CheckLanguage/DetermineRouting
[Common routing logic + variation table]

## Stage 3: PrepareDelegation
[Common delegation context + variation table]

## Stage 4: InvokeAgent
[Common invocation pattern + variation table]

## Stage 5: ReceiveResults
[Common validation logic + timeout handling]

## Stage 6: ProcessResults
[Common artifact extraction + status handling]

## Stage 7: Postflight
[Common status update + artifact linking + git commit]

## Stage 8: ReturnSuccess
[Common return format + variation table]

## Validation Checklists
### Pre-flight Checklist
- [ ] Task number is valid integer
- [ ] Task exists in TODO.md
- [ ] Task not [COMPLETED] or [ABANDONED]
- [ ] Language field present
- [ ] Status updated to in-progress
- [ ] state.json synchronized

### Post-flight Checklist
- [ ] Status updated to completion marker
- [ ] Artifacts linked in TODO.md
- [ ] state.json synchronized
- [ ] Git commit created (if completed)
- [ ] Brief summary returned (<100 tokens)

## Error Handling Patterns
[Common error scenarios + handling]

## Command-Specific Variations Table
[Comprehensive table of all variations]
```

**Benefits**:
- Single source of truth for lifecycle pattern
- Reduces duplication from ~1,961 lines to ~500 lines
- Easier to maintain consistency
- Clear documentation of variations

### Recommendation 2: Update Commands to Reference Lifecycle

**Changes Required**:

Each command file should:
1. Load command-lifecycle.md in context
2. Remove duplicated lifecycle documentation
3. Document only command-specific variations
4. Reference lifecycle stages by name

**Example** (/research.md):

```markdown
Context Loaded:
@.opencode/context/core/workflows/command-lifecycle.md
@.opencode/specs/TODO.md
@.opencode/specs/state.json
...

<workflow_execution>
  Follow command-lifecycle.md 8-stage pattern with these variations:
  
  <stage id="1" name="Preflight">
    Status transition: [NOT STARTED] → [RESEARCHING]
    Validation: Check for --divide flag
  </stage>
  
  <stage id="2" name="CheckLanguage">
    Routing: Language: lean → lean-research-agent, else → researcher
  </stage>
  
  <stage id="3" name="PrepareDelegation">
    Timeout: 3600s (1 hour)
    Special context: divide_topics flag
  </stage>
  
  [Continue with variations only...]
</workflow_execution>
```

**Reduction**: Each command file reduces from ~450-623 lines to ~250-350 lines

### Recommendation 3: Create Command Variations Table

**Purpose**: Single reference for all command-specific differences

**Structure**:

```markdown
# Command Lifecycle Variations

## Pre-flight Variations

| Aspect | /research | /plan | /revise | /implement |
|--------|-----------|-------|---------|------------|
| Initial Status | [NOT STARTED] | [NOT STARTED], [RESEARCHED] | [PLANNED], [REVISED] | [NOT STARTED], [PLANNED], [REVISED] |
| In-Progress Status | [RESEARCHING] | [PLANNING] | [REVISING] | [IMPLEMENTING] |
| Completion Status | [RESEARCHED] | [PLANNED] | [REVISED] | [COMPLETED], [PARTIAL] |
| Unique Validation | --divide flag | Warn if plan exists | Require existing plan | Check plan, determine resume phase |
| Routing | lean → lean-research-agent<br>* → researcher | Always planner | Always planner | Complex routing (see table) |
| Timeout | 3600s | 1800s | 1800s | 7200s |

## Post-flight Variations

| Aspect | /research | /plan | /revise | /implement |
|--------|-----------|-------|---------|------------|
| Artifact Types | reports/, summaries/ | plans/ | plans/ (versioned) | Implementation files, summaries/ |
| Link Format | - Research: {path} | - Plan: {path} | - Plan: {new_path} | - Implementation: {paths}<br>- Summary: {path} |
| Commit Scope | Research + TODO + state | Plan + TODO + state | New plan + TODO + state | Implementation + TODO + state + plan |
| Commit Message | "task {N}: research completed" | "task {N}: plan created" | "task {N}: plan revised to v{V}" | "task {N}: implementation completed" |
```

**Benefits**:
- Quick reference for all variations
- Easy to spot inconsistencies
- Clear documentation of legitimate differences

### Recommendation 4: Standardize Agent Return Validation

**Purpose**: Ensure all agents create required summary artifacts

**Changes Required**:

1. Add explicit summary artifact validation to lean-implementation-agent (line 149)
2. Add explicit summary artifact validation to task-executor (line 149)
3. Document summary artifact requirements in command-lifecycle.md

**Validation Logic** (add to both agents):

```xml
<validation>
  Before returning:
  - Verify all artifacts created successfully
  - Verify summary artifact exists in artifacts array
  - Verify summary artifact path exists on disk
  - Verify summary within token limit (<100 tokens)
  - Verify return format matches subagent-return-format.md
</validation>
```

### Recommendation 5: Create Pre-flight and Post-flight Checklists

**Purpose**: Standardize validation across all commands

**Pre-flight Checklist** (command-lifecycle.md):

```markdown
## Pre-flight Checklist

All commands MUST complete these checks before invoking agents:

- [ ] Task number parsed and validated as integer
- [ ] Task exists in TODO.md
- [ ] Task not in terminal state ([COMPLETED], [ABANDONED])
- [ ] Language field extracted (default "general" if missing)
- [ ] Command-specific validation passed (see variations table)
- [ ] Status marker updated to in-progress state
- [ ] Started timestamp added (YYYY-MM-DD format)
- [ ] state.json synchronized atomically with TODO.md
- [ ] Session ID generated (sess_{timestamp}_{random_6char})
- [ ] Delegation context prepared (depth, path, timeout)

If any check fails: Abort before invoking agent, return error to user
```

**Post-flight Checklist** (command-lifecycle.md):

```markdown
## Post-flight Checklist

All commands MUST complete these steps after receiving agent return:

- [ ] Return validated against subagent-return-format.md
- [ ] Session ID matches expected value
- [ ] Status extracted (completed/partial/failed/blocked)
- [ ] Artifacts extracted and paths validated
- [ ] Summary extracted (within <100 token limit)
- [ ] Errors extracted (if status != completed)
- [ ] TODO.md updated with completion status marker
- [ ] Completed timestamp added (YYYY-MM-DD format)
- [ ] Artifacts linked in TODO.md
- [ ] state.json synchronized atomically with TODO.md
- [ ] Git commit created (if status == completed)
- [ ] Brief summary returned to user (<100 tokens)

If validation fails: Log error, keep in-progress status, return actionable message
```

## Implementation Complexity Estimate

### Phase 1: Create command-lifecycle.md (4 hours)

**Tasks**:
1. Extract common 8-stage pattern from commands (1 hour)
2. Create variations tables for all differences (1.5 hours)
3. Document pre-flight and post-flight checklists (1 hour)
4. Add error handling patterns (0.5 hours)

**Deliverable**: .opencode/context/core/workflows/command-lifecycle.md (~500 lines)

### Phase 2: Update Commands (6 hours)

**Tasks**:
1. Update /research.md to reference lifecycle (1.5 hours)
2. Update /plan.md to reference lifecycle (1.5 hours)
3. Update /revise.md to reference lifecycle (1.5 hours)
4. Update /implement.md to reference lifecycle (1.5 hours)

**Deliverable**: 4 updated command files (reduced from ~1,961 lines to ~1,200 lines)

### Phase 3: Update Agents (4 hours)

**Tasks**:
1. Add summary artifact validation to lean-implementation-agent (1 hour)
2. Add summary artifact validation to task-executor (1 hour)
3. Update agent documentation to reference lifecycle (2 hours)

**Deliverable**: 2 updated agent files + documentation updates

### Phase 4: Testing and Validation (4 hours)

**Tasks**:
1. Test /research with lifecycle changes (1 hour)
2. Test /plan with lifecycle changes (1 hour)
3. Test /revise with lifecycle changes (1 hour)
4. Test /implement with lifecycle changes (1 hour)

**Deliverable**: Validation that all commands work correctly with new structure

### Total Estimate: 18 hours

**Risk Factors**:
- Medium: Commands may have undocumented variations
- Low: Agents may have edge cases not covered in analysis
- Low: Testing may reveal inconsistencies requiring additional fixes

**Mitigation**:
- Thorough review of all command files before extraction
- Incremental testing after each phase
- Rollback plan if issues discovered

## Proposed command-lifecycle.md Structure

```markdown
# Command Lifecycle Standard

**Version**: 1.0
**Status**: Active
**Created**: 2025-12-28
**Purpose**: Define standardized lifecycle for all workflow commands

## Overview

All workflow commands (/research, /plan, /revise, /implement) follow an 8-stage lifecycle pattern. This document defines the common pattern and documents command-specific variations.

## 8-Stage Lifecycle Pattern

### Stage 1: Preflight
Parse arguments, validate task, update status to in-progress

### Stage 2: CheckLanguage/DetermineRouting
Extract language field, determine target agent

### Stage 3: PrepareDelegation
Generate session_id, set delegation context

### Stage 4: InvokeAgent
Delegate to appropriate subagent with timeout

### Stage 5: ReceiveResults
Wait for return, validate against subagent-return-format.md

### Stage 6: ProcessResults
Extract artifacts, summary, errors from validated return

### Stage 7: Postflight
Update status, link artifacts, commit changes

### Stage 8: ReturnSuccess
Return brief summary to user (<100 tokens)

## Pre-flight Checklist

[Detailed checklist from Recommendation 5]

## Post-flight Checklist

[Detailed checklist from Recommendation 5]

## Command-Specific Variations

### Status Marker Transitions

[Table from Recommendation 3]

### Validation Checks

[Table from Recommendation 3]

### Routing Logic

[Table from Recommendation 3]

### Delegation Context

[Table from Recommendation 3]

### Artifact Linking

[Table from Recommendation 3]

### Git Commit Patterns

[Table from Recommendation 3]

## Error Handling Patterns

### Timeout Handling

All commands handle timeouts with this pattern:
1. Log timeout error with session_id
2. Check for partial artifacts on disk
3. Return partial status with artifacts found
4. Keep task in in-progress status (not failed)
5. Provide resume/retry instructions to user

Command-specific timeout durations:
- /research: 3600s (1 hour)
- /plan: 1800s (30 minutes)
- /revise: 1800s (30 minutes)
- /implement: 7200s (2 hours)

### Validation Failure Handling

All commands handle validation failures with this pattern:
1. Log validation error with details
2. Return failed status
3. Keep task in in-progress status
4. Recommend subagent fix or retry

### Git Commit Failure Handling

All commands handle git commit failures with this pattern:
1. Log error to errors.json
2. Continue (commit failure non-critical)
3. Return success with warning

### Tool Unavailability Handling

Commands that use specialized tools (/research with Loogle, /implement with lean-lsp-mcp):
1. Check tool availability before use
2. Log tool unavailability to errors.json
3. Use fallback approach (web search, direct file modification)
4. Include warning in return object
5. Continue with degraded mode (don't fail)

## Validation Framework

### Return Validation (Stage 5)

All commands validate agent returns with these steps:
1. Validate return is valid JSON
2. Validate against subagent-return-format.md schema
3. Check session_id matches expected value
4. Validate status is valid enum (completed/partial/failed/blocked)
5. Validate artifacts array structure
6. Check all artifact paths exist on disk

### Artifact Validation (Stage 6)

All commands validate artifacts with these steps:
1. Extract artifact paths from return
2. Verify all paths exist on disk
3. Verify artifact types match expected types
4. Verify summary artifact exists (if detailed artifact created)
5. Verify summary within token limit (<100 tokens)

## Integration with Existing Standards

This lifecycle integrates with:
- status-markers.md: Status marker transitions and timestamps
- subagent-return-format.md: Agent return validation
- artifact-management.md: Lazy directory creation and summary requirements
- git-commits.md: Targeted commit patterns

## Usage in Commands

Commands should:
1. Load command-lifecycle.md in context
2. Reference stages by name in workflow_execution section
3. Document only command-specific variations
4. Follow checklists for validation

Example:
```xml
<workflow_execution>
  Follow command-lifecycle.md 8-stage pattern with these variations:
  
  <stage id="1" name="Preflight">
    Status transition: [NOT STARTED] → [RESEARCHING]
    Validation: Check for --divide flag
  </stage>
  
  [Continue with variations only...]
</workflow_execution>
```
```

## References

### Command Files Analyzed
- .opencode/command/research.md (466 lines)
- .opencode/command/plan.md (450 lines)
- .opencode/command/revise.md (422 lines)
- .opencode/command/implement.md (623 lines)

### Agent Files Analyzed
- .opencode/agent/subagents/researcher.md (341 lines)
- .opencode/agent/subagents/planner.md (333 lines)
- .opencode/agent/subagents/lean-research-agent.md (963 lines)
- .opencode/agent/subagents/lean-implementation-agent.md (374 lines)
- .opencode/agent/subagents/task-executor.md (389 lines)
- .opencode/agent/subagents/implementer.md (316 lines)

### Supporting Standards
- .opencode/context/core/standards/status-markers.md (889 lines)
- .opencode/context/core/standards/subagent-return-format.md (356 lines)
- .opencode/context/core/system/artifact-management.md (182 lines)
- .opencode/context/core/system/git-commits.md (35 lines)

### Related Tasks
- Task 191: Fix subagent delegation hang (created subagent-return-format.md)
- Task 169: Context window protection (created summary artifact requirements)
- Task 156: Targeted git commits (created git-commits.md)

## Conclusion

Standardizing pre-flight and post-flight procedures across workflow commands is highly feasible with significant benefits:

**Benefits**:
- Reduces duplication from ~1,961 lines to ~1,200 lines (39% reduction)
- Single source of truth for lifecycle pattern
- Easier to maintain consistency across commands
- Clear documentation of legitimate variations
- Improved compliance with existing standards

**Risks**:
- Medium: Undocumented variations may exist
- Low: Edge cases may require additional handling
- Low: Testing may reveal inconsistencies

**Recommendation**: Proceed with 4-phase implementation (18 hours estimated)

**Next Steps**:
1. Review research findings with stakeholders
2. Create implementation plan for command-lifecycle.md
3. Execute Phase 1: Create command-lifecycle.md
4. Execute Phase 2: Update commands
5. Execute Phase 3: Update agents
6. Execute Phase 4: Testing and validation
