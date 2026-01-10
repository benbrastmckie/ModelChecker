# Research Report: Systematically Fix Metadata Lookup to Use state.json Instead of TODO.md

**Task**: 279 - Systematically fix metadata lookup to use state.json instead of TODO.md  
**Started**: 2026-01-05  
**Completed**: 2026-01-05  
**Effort**: 3 hours  
**Priority**: High  
**Dependencies**: None  
**Sources/Inputs**: Codebase analysis, TODO.md task description, state.json schema  
**Artifacts**: research-001.md  
**Standards**: status-markers.md, artifact-management.md, tasks.md, report.md

---

## Executive Summary

This research report documents the comprehensive analysis of metadata lookup patterns across the OpenCode system, identifying 25 files that incorrectly extract task metadata from TODO.md instead of the authoritative source (state.json). The issue was discovered when `/implement 276` showed "Extract task 276 details from TODO.md" in its output, revealing a systematic architectural violation where TODO.md is being used for programmatic metadata access instead of serving solely as a user-facing synchronized view.

**Key Findings**:
- 25 files across orchestrator, commands, subagents, context, standards, templates, and documentation use TODO.md for metadata extraction
- 8 metadata fields are affected: language, priority, status, effort, dependencies, blocking, description, and artifacts
- Current architecture violates single-source-of-truth principle with bidirectional sync instead of unidirectional (state.json → TODO.md)
- Fix requires 5-phase implementation (12-16 hours) to establish state.json as authoritative source

**Recommendations**:
1. Implement jq-based metadata extraction pattern from state.json
2. Update all 25 files to remove TODO.md metadata lookups
3. Preserve TODO.md synchronization via status-sync-manager (state.json → TODO.md only)
4. Document state.json as single source of truth in architecture standards
5. Validate language-based routing works correctly after migration

---

## Context & Scope

### Problem Statement

When running `/implement 276`, the command output displayed:
```bash
/implement 276
# Output shows: "Extract task 276 details from TODO.md"
# Problem: Using TODO.md for metadata lookup instead of state.json
```

This reveals a fundamental architectural issue: commands and subagents are extracting metadata from TODO.md instead of from the authoritative source (state.json). TODO.md should be kept in sync as a user-facing version of state.json, but all metadata lookups should reference state.json as the single source of truth.

### Scope of Investigation

This research analyzed:
1. All command files (`.opencode/command/*.md`)
2. All subagent files (`.opencode/agent/subagents/*.md`)
3. Orchestrator file (`.opencode/agent/orchestrator.md`)
4. Context files (`.opencode/context/**/*.md`)
5. Standards and templates (`.opencode/context/core/**/*.md`)
6. Documentation files (`.opencode/docs/**/*.md`, `.opencode/*.md`)

### Research Methodology

1. **Codebase Search**: Comprehensive grep analysis for TODO.md references
2. **Pattern Analysis**: Identified metadata extraction patterns (grep, jq, etc.)
3. **Impact Assessment**: Catalogued affected files and metadata fields
4. **Architecture Review**: Analyzed correct sync direction and data flow
5. **Implementation Planning**: Designed 5-phase migration strategy

---

## Key Findings

### Finding 1: Widespread TODO.md Metadata Extraction

**25 files** across the codebase extract metadata from TODO.md instead of state.json:

#### Orchestrator (1 file)
- `.opencode/agent/orchestrator.md`
  - Stage 2 (DetermineRouting): "Extract language from state.json or TODO.md"
  - **Issue**: Should extract from state.json ONLY

#### Workflow Commands (4 files)
- `.opencode/command/research.md` - "Extract language from task entry (state.json or TODO.md)"
- `.opencode/command/plan.md` - "Extract language from task entry (state.json or TODO.md)"
- `.opencode/command/implement.md` - "Extract language from task entry (state.json or TODO.md)"
- `.opencode/command/revise.md` - "Extract language from task entry (state.json or TODO.md)"
- **Issue**: All commands use TODO.md as fallback instead of state.json as primary source

#### Subagents (7 files)
- `researcher.md` - "Extract language from state.json (fallback to TODO.md)"
- `planner.md` - "Read task from .opencode/specs/TODO.md"
- `implementer.md` - "grep -A 50 "^### ${task_number}\." .opencode/specs/TODO.md"
- `lean-research-agent.md` - "Extract language from state.json (fallback to TODO.md)"
- `lean-implementation-agent.md` - "Read task from .opencode/specs/TODO.md"
- `lean-planner.md` - "Read task from .opencode/specs/TODO.md"
- `status-sync-manager.md` - "Extract current status from .opencode/specs/TODO.md"
- **Issue**: Subagents use grep patterns on TODO.md instead of jq queries on state.json

#### Context Files (6 files)
- `routing-guide.md` - "Extract language from task entry in TODO.md"
- `routing-logic.md` - "task_entry=$(grep -A 20 "^### ${task_number}\." .opencode/specs/TODO.md)"
- `research-workflow.md` - "Read task from TODO.md using grep"
- `planning-workflow.md` - "Read task from TODO.md using grep"
- `implementation-workflow.md` - "Read task from TODO.md using grep"
- `subagent-structure.md` - "Read task from TODO.md"
- **Issue**: Documentation teaches incorrect pattern

#### Standards (2 files)
- `state-management.md` - Needs clarification that state.json is authoritative source
- `artifact-management.md` - Needs documentation of metadata lookup pattern
- **Issue**: Standards don't explicitly forbid TODO.md metadata extraction

#### Templates (1 file)
- `command-template.md` - Template uses TODO.md pattern
- **Issue**: New commands inherit incorrect pattern

#### Documentation (4 files)
- `.opencode/docs/guides/creating-commands.md` - Examples use TODO.md
- `.opencode/ARCHITECTURE.md` - Needs state.json source-of-truth documentation
- `.opencode/REFACTOR.md` - Needs refactoring notes update
- `.opencode/REBUILD_SUMMARY.md` - Needs rebuild notes update
- **Issue**: Documentation perpetuates incorrect pattern

### Finding 2: Metadata Fields Affected

The following metadata fields are currently extracted from TODO.md but should come from state.json:

1. **Language** - Used for routing to Lean-specific agents (CRITICAL for routing)
2. **Priority** - Used for task prioritization
3. **Status** - Used for workflow state tracking
4. **Effort** - Used for estimation
5. **Dependencies** - Used for task ordering
6. **Blocking** - Used for identifying blockers
7. **Description** - Used for task context
8. **Artifacts** - Used for linking research/plans/implementations

**Impact**: Language field is most critical as it controls routing to lean-research-agent vs researcher, lean-implementation-agent vs implementer, etc.

### Finding 3: Incorrect Architecture Pattern

**Current (Incorrect) Behavior**:
```
TODO.md ←→ state.json (bidirectional sync)
    ↑
    | (metadata extraction)
    |
Commands/Subagents
```

**Correct Architecture**:
```
state.json (authoritative source)
    ↓
    | (read metadata)
    ↓
Commands/Subagents
    ↓
    | (update metadata)
    ↓
status-sync-manager
    ↓
    | (atomic two-phase commit)
    ↓
state.json + TODO.md (synchronized)
```

**Sync Direction**: state.json → TODO.md (NOT bidirectional)

### Finding 4: Root Cause Analysis

The root cause is **historical evolution** of the OpenCode system:

1. **Phase 1**: TODO.md was original task tracking file
2. **Phase 2**: state.json added as structured metadata store
3. **Phase 3**: status-sync-manager created for atomic updates
4. **Phase 4**: Migration incomplete - many files still use TODO.md patterns

**Evidence**:
- Older files (orchestrator, commands) use "state.json or TODO.md" fallback pattern
- Newer files (status-sync-manager) use state.json but still read TODO.md for current status
- Documentation hasn't been updated to reflect state.json as authoritative

### Finding 5: Correct Metadata Extraction Pattern

**Recommended Pattern** (using jq):

```bash
# Extract task metadata from state.json
task_metadata=$(jq -r --arg task_num "$task_number" \
  '.active_projects[] | select(.project_number == ($task_num | tonumber))' \
  .opencode/specs/state.json)

# Extract specific fields
language=$(echo "$task_metadata" | jq -r '.language // "general"')
priority=$(echo "$task_metadata" | jq -r '.priority // "medium"')
status=$(echo "$task_metadata" | jq -r '.status // "not_started"')
effort=$(echo "$task_metadata" | jq -r '.effort // "TBD"')
dependencies=$(echo "$task_metadata" | jq -r '.dependencies // []')
description=$(echo "$task_metadata" | jq -r '.description // ""')
```

**Benefits**:
- Single source of truth (state.json)
- Structured data access (JSON parsing)
- Type safety (jq schema validation)
- Atomic updates (via status-sync-manager)
- Clear sync direction (state.json → TODO.md)

---

## Detailed Analysis

### Analysis 1: Orchestrator Language Extraction

**File**: `.opencode/agent/orchestrator.md`

**Current Behavior**:
```markdown
Stage 2 (DetermineRouting): "Extract language from state.json or TODO.md"
```

**Issue**: Uses TODO.md as fallback instead of state.json as primary source.

**Recommended Fix**:
```markdown
Stage 2 (DetermineRouting): "Extract language from state.json ONLY"

# Implementation
language=$(jq -r --arg task_num "$task_number" \
  '.active_projects[] | select(.project_number == ($task_num | tonumber)) | .language // "general"' \
  .opencode/specs/state.json)
```

**Impact**: HIGH - Controls routing to Lean-specific agents

### Analysis 2: Command Metadata Extraction

**Files**: 
- `.opencode/command/research.md`
- `.opencode/command/plan.md`
- `.opencode/command/implement.md`
- `.opencode/command/revise.md`

**Current Behavior**:
```markdown
Stage 1 (PreflightValidation): "Extract language from task entry (state.json or TODO.md)"
```

**Issue**: All commands use same incorrect pattern.

**Recommended Fix**:
```markdown
Stage 1 (PreflightValidation): "Extract metadata from state.json"

# Implementation
task_metadata=$(jq -r --arg task_num "$task_number" \
  '.active_projects[] | select(.project_number == ($task_num | tonumber))' \
  .opencode/specs/state.json)

language=$(echo "$task_metadata" | jq -r '.language // "general"')
status=$(echo "$task_metadata" | jq -r '.status // "not_started"')
```

**Impact**: HIGH - Affects all workflow commands

### Analysis 3: Subagent Task Reading

**Files**:
- `.opencode/agent/subagents/planner.md`
- `.opencode/agent/subagents/implementer.md`
- `.opencode/agent/subagents/lean-implementation-agent.md`
- `.opencode/agent/subagents/lean-planner.md`

**Current Behavior**:
```bash
grep -A 50 "^### ${task_number}\." .opencode/specs/TODO.md
```

**Issue**: Uses grep pattern matching on TODO.md markdown.

**Recommended Fix**:
```bash
# Extract full task metadata from state.json
task_metadata=$(jq -r --arg task_num "$task_number" \
  '.active_projects[] | select(.project_number == ($task_num | tonumber))' \
  .opencode/specs/state.json)

# Extract description (may be multi-line)
description=$(echo "$task_metadata" | jq -r '.description // ""')
```

**Impact**: MEDIUM - Affects task context extraction

### Analysis 4: Status-Sync-Manager Current Status Extraction

**File**: `.opencode/agent/subagents/status-sync-manager.md`

**Current Behavior**:
```markdown
"Extract current status from .opencode/specs/TODO.md"
```

**Issue**: Reads current status from TODO.md instead of state.json.

**Recommended Fix**:
```markdown
"Extract current status from state.json"

# Implementation
current_status=$(jq -r --arg task_num "$task_number" \
  '.active_projects[] | select(.project_number == ($task_num | tonumber)) | .status // "not_started"' \
  .opencode/specs/state.json)
```

**Impact**: CRITICAL - Status-sync-manager is responsible for maintaining state.json, should not read TODO.md

### Analysis 5: Context File Documentation

**Files**:
- `.opencode/context/core/system/routing-guide.md`
- `.opencode/context/core/system/routing-logic.md`
- `.opencode/context/project/processes/research-workflow.md`
- `.opencode/context/project/processes/planning-workflow.md`
- `.opencode/context/project/processes/implementation-workflow.md`
- `.opencode/context/core/standards/subagent-structure.md`

**Current Behavior**: Documentation teaches TODO.md extraction pattern.

**Recommended Fix**: Update all documentation to show state.json extraction pattern with jq examples.

**Impact**: MEDIUM - Affects developer understanding and new file creation

---

## Code Examples

### Example 1: Correct Language Extraction (Orchestrator)

**Before**:
```bash
# Stage 2: DetermineRouting
# Extract language from state.json or TODO.md
language=$(grep -A 5 "^### ${task_number}\." .opencode/specs/TODO.md | grep "Language:" | cut -d: -f2 | xargs)
```

**After**:
```bash
# Stage 2: DetermineRouting
# Extract language from state.json (authoritative source)
language=$(jq -r --arg task_num "$task_number" \
  '.active_projects[] | select(.project_number == ($task_num | tonumber)) | .language // "general"' \
  .opencode/specs/state.json)

# Validate language extracted
if [[ -z "$language" ]]; then
  echo "[ERROR] Task $task_number not found in state.json"
  exit 1
fi
```

### Example 2: Correct Metadata Extraction (Commands)

**Before**:
```bash
# Stage 1: PreflightValidation
# Extract language from task entry (state.json or TODO.md)
task_entry=$(grep -A 20 "^### ${task_number}\." .opencode/specs/TODO.md)
language=$(echo "$task_entry" | grep "Language:" | cut -d: -f2 | xargs)
```

**After**:
```bash
# Stage 1: PreflightValidation
# Extract metadata from state.json (authoritative source)
task_metadata=$(jq -r --arg task_num "$task_number" \
  '.active_projects[] | select(.project_number == ($task_num | tonumber))' \
  .opencode/specs/state.json)

# Validate task exists
if [[ -z "$task_metadata" ]] || [[ "$task_metadata" == "null" ]]; then
  echo "[ERROR] Task $task_number not found in state.json"
  exit 1
fi

# Extract specific fields
language=$(echo "$task_metadata" | jq -r '.language // "general"')
priority=$(echo "$task_metadata" | jq -r '.priority // "medium"')
status=$(echo "$task_metadata" | jq -r '.status // "not_started"')
```

### Example 3: Correct Task Description Extraction (Subagents)

**Before**:
```bash
# Read task from TODO.md
task_description=$(grep -A 50 "^### ${task_number}\." .opencode/specs/TODO.md | sed -n '/^### /,/^---$/p')
```

**After**:
```bash
# Read task from state.json
task_metadata=$(jq -r --arg task_num "$task_number" \
  '.active_projects[] | select(.project_number == ($task_num | tonumber))' \
  .opencode/specs/state.json)

# Extract description (handles multi-line)
description=$(echo "$task_metadata" | jq -r '.description // ""')
project_name=$(echo "$task_metadata" | jq -r '.project_name // ""')

# Construct task context
task_context="Task $task_number: $project_name\n\n$description"
```

---

## Decisions

### Decision 1: Use state.json as Single Source of Truth

**Decision**: Establish state.json as the authoritative source for all task metadata.

**Rationale**:
- Structured JSON format enables type-safe parsing
- Atomic updates via status-sync-manager prevent race conditions
- Clear schema (state-schema.md) documents expected fields
- Eliminates ambiguity about which file is authoritative

**Alternatives Considered**:
1. **Keep TODO.md as source**: Rejected - markdown parsing is fragile and error-prone
2. **Bidirectional sync**: Rejected - creates ambiguity and potential conflicts
3. **Dual sources with priority**: Rejected - adds complexity without benefits

**Impact**: All 25 files must be updated to use state.json

### Decision 2: Preserve TODO.md as User-Facing View

**Decision**: Keep TODO.md synchronized via status-sync-manager (state.json → TODO.md).

**Rationale**:
- TODO.md provides human-readable task list
- Markdown format is easier to read than JSON
- Git diffs on TODO.md show task changes clearly
- Users expect TODO.md for quick task overview

**Sync Direction**: Unidirectional (state.json → TODO.md)

**Impact**: status-sync-manager remains responsible for TODO.md updates

### Decision 3: Use jq for JSON Parsing

**Decision**: Standardize on jq for all state.json metadata extraction.

**Rationale**:
- jq is standard JSON query tool (available in all environments)
- Supports complex queries and transformations
- Type-safe field extraction with defaults
- Consistent pattern across all files

**Alternative Considered**:
- **Python/Node.js scripts**: Rejected - adds dependency, slower than jq

**Impact**: All metadata extraction uses jq pattern

### Decision 4: Remove TODO.md Fallback Pattern

**Decision**: Remove all "state.json or TODO.md" fallback patterns.

**Rationale**:
- Fallback pattern perpetuates incorrect usage
- Creates ambiguity about which source is authoritative
- Hides bugs where state.json is out of sync
- Forces proper state.json maintenance

**Impact**: Commands will fail if state.json is missing/corrupt (fail-fast behavior)

### Decision 5: 5-Phase Implementation Strategy

**Decision**: Implement fix in 5 phases over 12-16 hours.

**Phases**:
1. **Phase 1**: Update metadata extraction pattern (4 hours)
2. **Phase 2**: Update orchestrator and commands (3 hours)
3. **Phase 3**: Update subagents (4 hours)
4. **Phase 4**: Update context and documentation (3 hours)
5. **Phase 5**: Testing and validation (2 hours)

**Rationale**: Phased approach allows incremental testing and validation.

---

## Recommendations

### Recommendation 1: Implement Helper Function for Metadata Extraction

**Priority**: HIGH

**Description**: Create standardized helper function for state.json metadata extraction.

**Implementation**:
```bash
# Add to state-management.md as standard pattern
extract_task_metadata() {
  local task_number=$1
  local field=$2
  local default_value=${3:-""}
  
  jq -r --arg task_num "$task_number" --arg field "$field" --arg default "$default_value" \
    '.active_projects[] | select(.project_number == ($task_num | tonumber)) | .[$field] // $default' \
    .opencode/specs/state.json
}

# Usage examples
language=$(extract_task_metadata "$task_number" "language" "general")
priority=$(extract_task_metadata "$task_number" "priority" "medium")
status=$(extract_task_metadata "$task_number" "status" "not_started")
```

**Benefits**:
- Consistent pattern across all files
- Centralized error handling
- Easy to update if schema changes
- Reduces code duplication

### Recommendation 2: Update Orchestrator Stage 2 (DetermineRouting)

**Priority**: CRITICAL

**Description**: Fix orchestrator to extract language from state.json ONLY.

**Files**: `.opencode/agent/orchestrator.md`

**Changes**:
- Remove TODO.md fallback
- Use jq to extract language field
- Add validation for missing task
- Log routing decision

**Impact**: Ensures correct routing to Lean-specific agents

### Recommendation 3: Update All Workflow Commands

**Priority**: HIGH

**Description**: Fix all workflow commands to use state.json for metadata extraction.

**Files**:
- `.opencode/command/research.md`
- `.opencode/command/plan.md`
- `.opencode/command/implement.md`
- `.opencode/command/revise.md`

**Changes**:
- Stage 1 (PreflightValidation): Extract metadata from state.json
- Remove TODO.md grep patterns
- Add task existence validation
- Use jq for all field extraction

**Impact**: Eliminates "Extract task NNN details from TODO.md" messages

### Recommendation 4: Update All Subagents

**Priority**: HIGH

**Description**: Fix all subagents to use state.json for task reading.

**Files**:
- `.opencode/agent/subagents/researcher.md`
- `.opencode/agent/subagents/planner.md`
- `.opencode/agent/subagents/implementer.md`
- `.opencode/agent/subagents/lean-research-agent.md`
- `.opencode/agent/subagents/lean-implementation-agent.md`
- `.opencode/agent/subagents/lean-planner.md`
- `.opencode/agent/subagents/status-sync-manager.md`

**Changes**:
- Replace grep TODO.md with jq state.json
- Extract description, artifacts, dependencies from state.json
- Remove TODO.md fallback patterns
- Add task existence validation

**Impact**: Consistent metadata access across all subagents

### Recommendation 5: Update Context and Documentation

**Priority**: MEDIUM

**Description**: Update all context files and documentation to teach state.json pattern.

**Files**:
- `.opencode/context/core/system/routing-guide.md`
- `.opencode/context/core/system/routing-logic.md`
- `.opencode/context/project/processes/research-workflow.md`
- `.opencode/context/project/processes/planning-workflow.md`
- `.opencode/context/project/processes/implementation-workflow.md`
- `.opencode/context/core/standards/subagent-structure.md`
- `.opencode/context/core/system/state-management.md`
- `.opencode/context/core/system/artifact-management.md`
- `.opencode/context/core/templates/command-template.md`
- `.opencode/docs/guides/creating-commands.md`
- `.opencode/ARCHITECTURE.md`
- `.opencode/REFACTOR.md`
- `.opencode/REBUILD_SUMMARY.md`

**Changes**:
- Replace TODO.md examples with state.json examples
- Document jq extraction pattern
- Clarify state.json as authoritative source
- Update command template to use state.json
- Add architecture documentation for sync direction

**Impact**: Prevents future files from using incorrect pattern

### Recommendation 6: Comprehensive Testing

**Priority**: HIGH

**Description**: Test all workflow commands after migration to verify correct behavior.

**Test Cases**:
1. `/research <lean_task>` - Verify routes to lean-research-agent
2. `/plan <markdown_task>` - Verify routes to planner
3. `/implement <general_task>` - Verify routes to implementer
4. `/revise <task>` - Verify metadata extraction works
5. Verify no "Extract task NNN details from TODO.md" messages
6. Verify TODO.md still synchronized correctly
7. Verify language-based routing works for all task types

**Success Criteria**:
- All commands extract metadata from state.json
- No grep TODO.md commands in output
- Language routing works correctly
- TODO.md remains synchronized

---

## Risks & Mitigations

### Risk 1: Breaking Language-Based Routing

**Risk**: Incorrect language extraction could break routing to Lean-specific agents.

**Impact**: HIGH - Lean tasks would route to wrong agents, causing build failures.

**Mitigation**:
- Test language extraction thoroughly before deployment
- Add validation to ensure language field exists
- Log routing decisions for debugging
- Test with Lean, markdown, and general tasks

**Contingency**: Rollback to TODO.md fallback if routing breaks

### Risk 2: state.json Out of Sync with TODO.md

**Risk**: If state.json is corrupted or out of sync, commands will fail.

**Impact**: MEDIUM - Commands will fail-fast instead of using stale TODO.md data.

**Mitigation**:
- Ensure status-sync-manager maintains sync correctly
- Add validation to detect sync issues
- Document manual sync procedure
- Consider creating /sync command (see task 295, 296)

**Contingency**: Manual state.json repair from TODO.md if needed

### Risk 3: Missing Metadata Fields in state.json

**Risk**: Some tasks may not have all metadata fields in state.json.

**Impact**: LOW - jq defaults handle missing fields gracefully.

**Mitigation**:
- Use jq default values (e.g., `.language // "general"`)
- Document required vs optional fields in state-schema.md
- Add validation to status-sync-manager
- Backfill missing fields during migration

**Contingency**: Add missing fields to state.json manually

### Risk 4: Performance Impact of jq Queries

**Risk**: jq queries on large state.json could be slower than grep on TODO.md.

**Impact**: LOW - state.json is small (<1MB), jq is fast.

**Mitigation**:
- Benchmark jq performance on current state.json
- Cache task metadata if needed
- Consider indexing if state.json grows large

**Contingency**: Optimize jq queries or add caching layer

### Risk 5: Incomplete Migration

**Risk**: Missing files during migration could leave TODO.md extraction in place.

**Impact**: MEDIUM - Inconsistent behavior across commands.

**Mitigation**:
- Comprehensive grep search for all TODO.md references
- Systematic file-by-file review
- Testing all commands after migration
- Code review of changes

**Contingency**: Second pass to catch missed files

---

## Appendix: Sources and Citations

### Source 1: Task 279 Description in TODO.md

**File**: `.opencode/specs/TODO.md` (lines 751-953)

**Content**: Original task description with comprehensive analysis of 25 affected files, metadata fields, root cause, and implementation strategy.

**Citation**: Used as primary source for affected files list and implementation phases.

### Source 2: state.json Schema

**File**: `.opencode/specs/state.json`

**Content**: Current state.json structure showing active_projects array with metadata fields.

**Citation**: Used to design jq extraction patterns and validate field names.

### Source 3: state-management.md Standard

**File**: `.opencode/context/core/system/state-management.md`

**Content**: Current state management documentation (needs update to clarify state.json as authoritative).

**Citation**: Referenced for understanding current state management patterns.

### Source 4: Codebase Grep Analysis

**Command**: `grep -r "TODO.md" .opencode/`

**Results**: Identified 25 files with TODO.md references for metadata extraction.

**Citation**: Used to validate completeness of affected files list.

---

## Implementation Strategy

### Phase 1: Update Metadata Extraction Pattern (4 hours)

**Objective**: Create and document standard pattern for state.json metadata extraction.

**Tasks**:
1. Create helper function for state.json metadata extraction
2. Document pattern in state-management.md
3. Create examples in routing-guide.md
4. Add jq extraction examples to subagent-structure.md

**Deliverables**:
- Helper function in state-management.md
- Examples in routing-guide.md
- Updated subagent-structure.md

**Validation**: Helper function works for all metadata fields

### Phase 2: Update Orchestrator and Commands (3 hours)

**Objective**: Fix orchestrator and all workflow commands to use state.json.

**Tasks**:
1. Update orchestrator.md Stage 2 (DetermineRouting)
2. Update research.md Stage 1 (PreflightValidation)
3. Update plan.md Stage 1 (PreflightValidation)
4. Update implement.md Stage 1 (PreflightValidation)
5. Update revise.md Stage 1 (PreflightValidation)

**Deliverables**:
- Updated orchestrator.md
- Updated research.md, plan.md, implement.md, revise.md

**Validation**: Commands extract metadata from state.json, not TODO.md

### Phase 3: Update Subagents (4 hours)

**Objective**: Fix all subagents to use state.json for task reading.

**Tasks**:
1. Update researcher.md - Remove TODO.md fallback
2. Update planner.md - Replace grep with jq
3. Update implementer.md - Replace grep with jq
4. Update lean-research-agent.md - Remove TODO.md fallback
5. Update lean-implementation-agent.md - Replace grep with jq
6. Update lean-planner.md - Replace grep with jq
7. Update status-sync-manager.md - Extract status from state.json

**Deliverables**:
- Updated researcher.md, planner.md, implementer.md
- Updated lean-research-agent.md, lean-implementation-agent.md, lean-planner.md
- Updated status-sync-manager.md

**Validation**: Subagents use jq for all metadata extraction

### Phase 4: Update Context and Documentation (3 hours)

**Objective**: Update all context files and documentation to teach state.json pattern.

**Tasks**:
1. Update 6 context files (routing, workflows, standards)
   - routing-guide.md
   - routing-logic.md
   - research-workflow.md
   - planning-workflow.md
   - implementation-workflow.md
   - subagent-structure.md
2. Update 2 standards files
   - state-management.md
   - artifact-management.md
3. Update 1 template file
   - command-template.md
4. Update 4 documentation files
   - creating-commands.md
   - ARCHITECTURE.md
   - REFACTOR.md
   - REBUILD_SUMMARY.md

**Deliverables**:
- Updated context files with state.json examples
- Updated standards with state.json as authoritative source
- Updated template with state.json pattern
- Updated documentation with architecture notes

**Validation**: All documentation teaches state.json pattern

### Phase 5: Testing and Validation (2 hours)

**Objective**: Comprehensive testing to ensure migration successful.

**Test Cases**:
1. Test `/research` command with Lean task (language routing)
2. Test `/plan` command with markdown task
3. Test `/implement` command with general task
4. Test `/revise` command
5. Verify metadata extracted from state.json, not TODO.md
6. Verify TODO.md still synchronized correctly
7. Verify no grep TODO.md commands in output

**Deliverables**:
- Test execution report
- Validation of all acceptance criteria
- Bug fixes for any issues found

**Validation**: All acceptance criteria met

---

## Acceptance Criteria

- [PENDING] All metadata extraction uses state.json as source of truth
- [PENDING] No commands or subagents extract metadata from TODO.md
- [PENDING] TODO.md remains synchronized via status-sync-manager (state.json → TODO.md)
- [PENDING] Language-based routing works correctly (Lean tasks → lean-research-agent)
- [PENDING] All workflow commands tested and verified
- [PENDING] Context files document state.json as authoritative source
- [PENDING] No "Extract task NNN details from TODO.md" messages in command output
- [PENDING] grep TODO.md only used for validation/testing, not metadata extraction

---

## Related Tasks

- **Task 276**: Investigate redundant project-level state.json files (related to state management)
- **Task 272**: Add YAML header to TODO.md (sync state.json → TODO.md)
- **Task 275**: Fix workflow status updates (uses status-sync-manager)
- **Task 295**: Create /sync command to synchronize TODO.md and state.json
- **Task 296**: Create /sync command to synchronize TODO.md and state.json (duplicate)

---

## Conclusion

This research has identified a systematic architectural issue where 25 files across the OpenCode system extract task metadata from TODO.md instead of the authoritative source (state.json). The fix requires a 5-phase implementation (12-16 hours) to establish state.json as the single source of truth, preserve TODO.md as a synchronized user-facing view, and update all commands, subagents, context files, and documentation to use the correct jq-based extraction pattern.

The migration will eliminate the "Extract task NNN details from TODO.md" messages, ensure correct language-based routing to Lean-specific agents, and establish a clear architectural principle: state.json is authoritative, TODO.md is synchronized view.

**Next Steps**:
1. Review and approve this research report
2. Create implementation plan based on 5-phase strategy
3. Execute Phase 1 (metadata extraction pattern)
4. Execute Phase 2 (orchestrator and commands)
5. Execute Phase 3 (subagents)
6. Execute Phase 4 (context and documentation)
7. Execute Phase 5 (testing and validation)
