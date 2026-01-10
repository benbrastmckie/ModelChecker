# Research Report: Create --sync flag for /task command to synchronize TODO.md and state.json

**Task**: 330 - Create --sync flag for /task command to synchronize TODO.md and state.json  
**Started**: 2026-01-07  
**Completed**: 2026-01-07  
**Effort**: 6-8 hours (estimated)  
**Priority**: Medium  
**Dependencies**: None  
**Sources/Inputs**:
- .opencode/command/sync.md (current /sync command implementation)
- .opencode/command/task.md (current /task command structure)
- .opencode/command/abandon.md (range/list parsing patterns)
- .opencode/agent/subagents/status-sync-manager.md (atomic update mechanism)
- .opencode/specs/TODO.md (task metadata)
- .opencode/state.json (authoritative state)
- .opencode/scripts/validate_state_sync.py (validation utility)

**Artifacts**:
- .opencode/specs/330_create___sync_flag_for_task_command_to_synchronize_todo_md_and_state_json/reports/research-001.md

**Standards**: status-markers.md, artifact-management.md, tasks.md, report.md

---

## Executive Summary

This research investigates implementing a `--sync` flag for the `/task` command that synchronizes TODO.md and state.json with optional task number ranges. The current `/sync` command (task 296) provides comprehensive bidirectional synchronization using git blame timestamps for field-level conflict resolution, but includes complexity (dry-run mode, extensive validation) that may not be needed for a simpler `/task --sync` variant.

**Key Findings**:
1. Current `/sync` command has 8 stages with 553 lines, including git blame-based field-level conflict resolution
2. Task 330 requests simpler approach: avoid needless complexity, omit dry-run mode
3. Range/list parsing patterns exist in `/abandon` command (task 311) and can be reused
4. status-sync-manager provides atomic update mechanism for TODO.md + state.json synchronization
5. validate_state_sync.py script provides validation and repair capabilities that could inform implementation

**Recommendations**:
1. Implement simplified sync as `/task --sync [RANGES]` with optional task number ranges
2. Reuse range/list parsing from `/abandon` command (proven pattern)
3. Delegate to status-sync-manager for atomic updates (no manual file manipulation)
4. Omit dry-run mode and git blame complexity (per task requirements)
5. Use state.json as authoritative source (per task 279 findings)
6. Estimated effort: 6-8 hours

---

## Context & Scope

### Task Description

Create a `--sync` flag for the `/task` command that synchronizes TODO.md and state.json. The flag should:
- Accept optional task number ranges (e.g., `343-345, 337`) to sync specific tasks
- Sync all tasks if no numbers are provided
- Improve upon the current `/sync` command implementation
- Avoid needless complexity
- Omit dry-run mode

### Related Tasks

- **Task 296**: Created `/sync` command with git blame-based field-level synchronization (completed)
- **Task 311**: Implemented range/list parsing for `/abandon` command (completed)
- **Task 279**: Systematically fix metadata lookup to use state.json instead of TODO.md (researched)
- **Task 329**: Research persistent state synchronization failures (high priority)
- **Task 333**: Fix workflow command TODO.md/state.json synchronization failures (completed)

### Architectural Context

Per task 333 findings, the architectural requirement is clear:
> **All workflow commands must delegate to status-sync-manager for atomic TODO.md + state.json updates**

This eliminates manual file manipulation (sed, awk, jq) which fails silently and causes synchronization failures.

---

## Key Findings

### Finding 1: Current /sync Command Implementation

**Source**: .opencode/command/sync.md (553 lines)

The current `/sync` command provides comprehensive bidirectional synchronization:

**Features**:
- 8-stage workflow (ParseAndValidate, ExtractTasksAndFields, GetGitBlameTimestamps, DetectDiscrepancies, ResolveConflicts, ApplyOrPreview, CreateCommit, ReportResults)
- Git blame-based field-level conflict resolution
- Dry-run mode (`--dry-run` flag)
- Handles missing tasks in either file
- Handles field-level mismatches (status, priority, effort, language, description)
- Caches git blame output for performance
- Delegates to status-sync-manager for atomic updates
- Delegates to git-workflow-manager for commits
- Comprehensive error handling and rollback

**Complexity Analysis**:

```
Stage 1 (ParseAndValidate): 71 lines
  - Validates git repository
  - Validates files tracked in git
  - Checks for uncommitted changes
  - Creates backups

Stage 2 (ExtractTasksAndFields): 38 lines
  - Parses TODO.md with grep/line numbers
  - Parses state.json with jq
  - Builds task index

Stage 3 (GetGitBlameTimestamps): 43 lines
  - Runs git blame --line-porcelain
  - Caches blame output
  - Extracts timestamps for each field
  - Handles uncommitted changes fallback

Stage 4 (DetectDiscrepancies): 38 lines
  - Compares field values
  - Normalizes values for comparison
  - Records discrepancies

Stage 5 (ResolveConflicts): 30 lines
  - Compares timestamps
  - Determines resolution (prefer_todo vs prefer_state)
  - Builds resolution plan

Stage 6 (ApplyOrPreview): 69 lines
  - Dry-run mode: Display preview
  - Apply mode: Delegate to status-sync-manager
  - Verify synchronization succeeded

Stage 7 (CreateCommit): 23 lines
  - Delegate to git-workflow-manager
  - Handle commit failures

Stage 8 (ReportResults): 38 lines
  - Format results summary
  - Clean up temporary files
```

**Strengths**:
- Surgical precision (field-level conflict resolution)
- Git blame provides accurate "most recent change" detection
- Handles complex scenarios (uncommitted changes, missing tasks, field mismatches)
- Atomic updates via status-sync-manager
- Comprehensive validation and error handling

**Complexity Concerns** (per task 330 requirements):
- 8 stages may be overkill for simpler use cases
- Git blame adds complexity and performance overhead (~50-100ms per file)
- Dry-run mode adds 69 lines of preview logic
- Extensive validation (git repo, tracked files, uncommitted changes) may not be needed for `/task --sync`

### Finding 2: Range/List Parsing Patterns

**Source**: .opencode/command/abandon.md (task 311)

The `/abandon` command implements proven range/list parsing:

```bash
# Parse task numbers from $ARGUMENTS using parse_task_numbers()
# Split by comma: IFS=',' read -ra PARTS <<< "$ARGUMENTS"
# For each part (trimmed):
#   * If matches range pattern ^([0-9]+)-([0-9]+)$:
#     - Extract start and end
#     - Validate start <= end (error if start > end)
#     - Expand with seq: seq $start $end
#   * If matches single number pattern ^[0-9]+$:
#     - Add to task list
#   * Else:
#     - Return error "Invalid task number format: '{part}'"
# Deduplicate and sort: printf '%s\n' "${task_numbers[@]}" | sort -nu
```

**Examples**:
- `"298"` → [298]
- `"293-295"` → [293, 294, 295]
- `"302, 303"` → [302, 303]
- `"293-295, 302, 303"` → [293, 294, 295, 302, 303]
- `"293, 293-295"` → [293, 294, 295] (deduplicated)

**Error Handling**:
- Invalid range (start > end): `Error: Invalid range 295-293 (start > end)`
- Invalid format: `Error: Invalid task number format: 'abc'`
- Task not found: `Error: Task 9999 not found`

**Validation**:
- Validates all tasks exist in state.json before processing
- Fail fast on first validation error
- Stores original status for rollback

**Strengths**:
- Simple, proven pattern (task 311 completed successfully)
- Handles ranges, lists, and mixed syntax
- Deduplicates and sorts automatically
- Clear error messages
- Reusable for `/task --sync`

### Finding 3: status-sync-manager Atomic Update Mechanism

**Source**: .opencode/agent/subagents/status-sync-manager.md (1467 lines)

status-sync-manager provides atomic multi-file synchronization:

**Operations**:
1. `create_task`: Create task entries in both files atomically
2. `update_status`: Update status markers atomically
3. `archive_tasks`: Move tasks to completed_projects atomically
4. `update_task_metadata`: Update task fields atomically

**Two-Phase Commit Protocol**:

```
Phase 1 (Prepare):
  1. Read TODO.md and state.json into memory
  2. Validate all updates
  3. Prepare updated content in memory
  4. NO BACKUP FILES CREATED (git-only rollback)

Phase 2 (Commit):
  1. Generate unique temp file names (include session_id)
  2. Write to temp files
  3. Verify temp files written successfully
  4. Atomic rename (both files or neither)
  5. Clean up temp files on success

Rollback on Failure:
  1. Remove all temp files
  2. Return failed status with error details
  3. Rely on git for recovery (no backup file rollback)
```

**Atomic Write Pattern**:
```bash
# Generate unique temp file names
todo_tmp=".opencode/specs/TODO.md.tmp.${session_id}"
state_tmp=".opencode/specs/state.json.tmp.${session_id}"

# Write to temp files
write_file "$todo_tmp" "$updated_todo_content"
write_file "$state_tmp" "$updated_state_content"

# Verify temp files
verify_file_exists "$todo_tmp"
verify_file_exists "$state_tmp"

# Atomic rename (both files or neither)
mv "$todo_tmp" ".opencode/specs/TODO.md"
mv "$state_tmp" ".opencode/specs/state.json"
```

**Strengths**:
- Atomic updates (all files or none)
- Two-phase commit ensures consistency
- Atomic rename eliminates race conditions
- No file locking (allows concurrent agent execution)
- Last writer wins (acceptable per user requirement)
- Git-only rollback (no backup file complexity)

**Relevance to /task --sync**:
- Provides proven atomic update mechanism
- Eliminates need for manual file manipulation
- Ensures TODO.md and state.json stay in sync
- Handles validation and error recovery

### Finding 4: validate_state_sync.py Validation Utility

**Source**: .opencode/scripts/validate_state_sync.py (782 lines)

Python utility for validating and repairing TODO.md ↔ state.json consistency:

**Features**:
- Detects missing tasks in either file
- Detects metadata mismatches (status, priority, language, effort, description)
- Detects numbering issues (duplicate task numbers, incorrect next_project_number)
- Detects structure issues (invalid JSON, missing sections)
- Provides automatic repair with `--fix` flag
- Creates backups before repair
- Uses state.json as source of truth for repairs

**Validation Checks**:

```python
def validate(self) -> List[Issue]:
    # Check files exist
    # Load files
    # Run validation checks:
    self._check_task_existence(todo_tasks, state_data)
    self._check_metadata_consistency(todo_tasks, state_data)
    self._check_numbering(todo_tasks, state_data)
    self._check_structure(todo_tasks, state_data)
    return self.issues
```

**Repair Operations**:
- `_fix_missing_description_in_todo()`: Copy description from state.json to TODO.md
- `_fix_missing_description_in_state()`: Copy description from TODO.md to state.json
- `_fix_status_mismatch()`: Update TODO.md status from state.json (state.json is source of truth)
- `_fix_priority_mismatch()`: Update TODO.md priority from state.json
- `_fix_language_mismatch()`: Update TODO.md language from state.json
- `_fix_missing_in_todo()`: Add task to TODO.md from state.json
- `_fix_missing_in_state()`: Add task to state.json from TODO.md
- `_fix_next_project_number()`: Update next_project_number to max task + 1

**Status Normalization**:
```python
status_map = {
    'NOT STARTED': 'not_started',
    'IN PROGRESS': 'in_progress',
    'RESEARCHED': 'researched',
    'PLANNED': 'planned',
    'BLOCKED': 'blocked',
    'ABANDONED': 'abandoned',
    'COMPLETED': 'completed'
}
```

**Strengths**:
- Comprehensive validation logic
- Uses state.json as source of truth (aligns with task 279)
- Provides repair capabilities
- Clear error messages
- Handles edge cases (missing descriptions, duplicate numbers, etc.)

**Relevance to /task --sync**:
- Validation logic could inform `/task --sync` implementation
- Status normalization patterns are reusable
- Repair operations show what needs to be synced
- Demonstrates state.json as authoritative source

### Finding 5: Simplified Sync Approach

**Analysis**: Comparing current `/sync` command with task 330 requirements

**Current /sync Complexity**:
- Git blame-based field-level conflict resolution (3 stages, ~150 lines)
- Dry-run mode (69 lines)
- Extensive git validation (git repo, tracked files, uncommitted changes)
- Backup file creation
- Comprehensive error handling for git failures

**Task 330 Requirements**:
- Avoid needless complexity
- Omit dry-run mode
- Support optional task number ranges
- Sync all tasks if no numbers provided

**Simplified Approach**:

Instead of git blame-based conflict resolution, use **state.json as authoritative source** (per task 279):

```
Stage 1: Parse and Validate
  - Parse task number ranges (reuse /abandon pattern)
  - If no ranges: sync all tasks
  - Validate state.json exists and is valid
  - Validate TODO.md exists

Stage 2: Detect Discrepancies
  - For each task in range (or all tasks):
    * Extract metadata from state.json (authoritative)
    * Extract metadata from TODO.md
    * Compare fields: status, priority, effort, language, description
    * Record discrepancies

Stage 3: Apply Updates
  - For each discrepancy:
    * Delegate to status-sync-manager with update_task_metadata operation
    * Pass updated_fields object with state.json values
  - status-sync-manager ensures atomic updates

Stage 4: Report Results
  - Display count of tasks synced
  - Display fields updated
  - Display any errors
```

**Simplifications**:
1. **No git blame**: Use state.json as source of truth (eliminates 150 lines)
2. **No dry-run mode**: Direct sync only (eliminates 69 lines)
3. **No git validation**: Assume files exist (eliminates 71 lines)
4. **No backup files**: Rely on git for recovery (per status-sync-manager pattern)
5. **Delegate to status-sync-manager**: No manual file manipulation (per task 333)

**Estimated Complexity**: 4 stages, ~200 lines (vs 8 stages, 553 lines for current /sync)

**Trade-offs**:
- **Pros**: Simpler, faster, easier to maintain, aligns with task 279 (state.json as source of truth)
- **Cons**: No field-level conflict resolution (always prefers state.json), no dry-run preview

**Justification**: Task 330 explicitly requests "avoid needless complexity" and "omit dry-run mode". Using state.json as authoritative source aligns with task 279 findings and eliminates the need for git blame-based conflict resolution.

---

## Detailed Analysis

### 1. Argument Parsing Strategy

**Requirement**: Accept optional task number ranges (e.g., `343-345, 337`) or sync all tasks if no numbers provided

**Approach**: Reuse `/abandon` command parsing pattern

**Implementation**:

```bash
# Parse task numbers from $ARGUMENTS
parse_task_numbers() {
  local args="$1"
  local task_numbers=()
  
  # If empty, return empty (will sync all tasks)
  if [[ -z "$args" ]]; then
    echo ""
    return 0
  fi
  
  # Split by comma
  IFS=',' read -ra PARTS <<< "$args"
  
  for part in "${PARTS[@]}"; do
    # Trim whitespace
    part=$(echo "$part" | xargs)
    
    # Check if range (N-M)
    if [[ "$part" =~ ^([0-9]+)-([0-9]+)$ ]]; then
      local start="${BASH_REMATCH[1]}"
      local end="${BASH_REMATCH[2]}"
      
      # Validate start <= end
      if (( start > end )); then
        echo "Error: Invalid range $start-$end (start > end)" >&2
        return 1
      fi
      
      # Expand range
      for i in $(seq "$start" "$end"); do
        task_numbers+=("$i")
      done
    # Check if single number
    elif [[ "$part" =~ ^[0-9]+$ ]]; then
      task_numbers+=("$part")
    else
      echo "Error: Invalid task number format: '$part'" >&2
      return 1
    fi
  done
  
  # Deduplicate and sort
  printf '%s\n' "${task_numbers[@]}" | sort -nu
}
```

**Examples**:
```bash
parse_task_numbers ""                    # → "" (sync all)
parse_task_numbers "343"                 # → "343"
parse_task_numbers "343-345"             # → "343\n344\n345"
parse_task_numbers "337"                 # → "337"
parse_task_numbers "343-345, 337"        # → "337\n343\n344\n345"
parse_task_numbers "343, 343-345"        # → "343\n344\n345" (deduplicated)
```

**Error Handling**:
```bash
parse_task_numbers "345-343"             # → Error: Invalid range 345-343 (start > end)
parse_task_numbers "abc"                 # → Error: Invalid task number format: 'abc'
parse_task_numbers "343-345, abc, 337"   # → Error: Invalid task number format: 'abc'
```

### 2. Discrepancy Detection Strategy

**Requirement**: Detect differences between TODO.md and state.json

**Approach**: Use state.json as authoritative source (per task 279)

**Fields to Compare**:
- Status (TODO.md: `[NOT STARTED]`, state.json: `not_started`)
- Priority (TODO.md: `High`, state.json: `high`)
- Effort (TODO.md: `4-6 hours`, state.json: `4-6 hours`)
- Language (TODO.md: `meta`, state.json: `meta`)
- Description (TODO.md: `**Description**: ...`, state.json: `description: "..."`)

**Normalization**:

```python
# Status normalization (TODO.md → state.json format)
def normalize_status(todo_status):
    status_map = {
        'NOT STARTED': 'not_started',
        'IN PROGRESS': 'in_progress',
        'RESEARCHED': 'researched',
        'PLANNED': 'planned',
        'BLOCKED': 'blocked',
        'ABANDONED': 'abandoned',
        'COMPLETED': 'completed'
    }
    return status_map.get(todo_status.upper(), todo_status.lower())

# Priority normalization (TODO.md → state.json format)
def normalize_priority(todo_priority):
    return todo_priority.lower()

# Effort normalization (no change)
def normalize_effort(effort):
    return effort.strip()

# Language normalization (no change)
def normalize_language(language):
    return language.lower()

# Description normalization (no change)
def normalize_description(description):
    return description.strip()
```

**Discrepancy Detection Algorithm**:

```python
def detect_discrepancies(task_numbers, todo_tasks, state_tasks):
    discrepancies = []
    
    for task_num in task_numbers:
        # Get task data
        todo_task = todo_tasks.get(task_num)
        state_task = state_tasks.get(task_num)
        
        # Skip if task missing in either file
        if not todo_task or not state_task:
            continue
        
        # Compare fields
        fields_to_update = {}
        
        # Status
        todo_status = normalize_status(todo_task.get('status'))
        state_status = state_task.get('status')
        if todo_status != state_status:
            fields_to_update['status'] = state_status
        
        # Priority
        todo_priority = normalize_priority(todo_task.get('priority'))
        state_priority = state_task.get('priority')
        if todo_priority != state_priority:
            fields_to_update['priority'] = state_priority
        
        # Effort
        todo_effort = normalize_effort(todo_task.get('effort'))
        state_effort = state_task.get('effort')
        if todo_effort != state_effort:
            fields_to_update['effort'] = state_effort
        
        # Language
        todo_language = normalize_language(todo_task.get('language'))
        state_language = state_task.get('language')
        if todo_language != state_language:
            fields_to_update['language'] = state_language
        
        # Description
        todo_description = normalize_description(todo_task.get('description'))
        state_description = state_task.get('description')
        if todo_description != state_description:
            fields_to_update['description'] = state_description
        
        # Record discrepancy if any fields differ
        if fields_to_update:
            discrepancies.append({
                'task_number': task_num,
                'fields_to_update': fields_to_update
            })
    
    return discrepancies
```

**Example Discrepancies**:

```json
[
  {
    "task_number": 343,
    "fields_to_update": {
      "status": "researched",
      "priority": "high"
    }
  },
  {
    "task_number": 344,
    "fields_to_update": {
      "description": "Updated description from state.json"
    }
  }
]
```

### 3. Atomic Update Strategy

**Requirement**: Update TODO.md and state.json atomically

**Approach**: Delegate to status-sync-manager with `update_task_metadata` operation

**status-sync-manager Interface**:

```
Operation: update_task_metadata
Inputs:
  - task_number: integer
  - updated_fields: object with fields to update
    * description: string (50-500 chars)
    * priority: string (Low|Medium|High)
    * effort: string (non-empty)
    * dependencies: array of integers

Process:
  1. Validate inputs
  2. Read TODO.md and state.json
  3. Update task entry in TODO.md
  4. Update task entry in state.json
  5. Atomic write (both files or neither)
  6. Return success or failure

Atomic Write Pattern:
  1. Write to temp files
  2. Verify temp files
  3. Atomic rename (mv)
  4. Clean up temp files
```

**Delegation Example**:

```bash
# For each discrepancy
for discrepancy in "${discrepancies[@]}"; do
  task_number=$(echo "$discrepancy" | jq -r '.task_number')
  fields_to_update=$(echo "$discrepancy" | jq -c '.fields_to_update')
  
  # Delegate to status-sync-manager
  result=$(task \
    subagent_type="status-sync-manager" \
    prompt="Update task $task_number metadata: $fields_to_update" \
    description="Sync task $task_number from state.json to TODO.md" \
    inputs="{
      \"operation\": \"update_task_metadata\",
      \"task_number\": $task_number,
      \"updated_fields\": $fields_to_update,
      \"timestamp\": \"$(date -I)\",
      \"session_id\": \"$session_id\",
      \"delegation_depth\": 1,
      \"delegation_path\": [\"orchestrator\", \"task\", \"status-sync-manager\"]
    }")
  
  # Check result
  status=$(echo "$result" | jq -r '.status')
  if [[ "$status" != "completed" ]]; then
    echo "Error: Failed to sync task $task_number"
    # Continue with other tasks (no rollback for sync)
  fi
done
```

**Atomicity Guarantee**:
- status-sync-manager uses two-phase commit
- Atomic rename ensures both files update or neither
- No partial state (all fields in a task update atomically)
- No rollback needed (each task syncs independently)

### 4. Error Handling Strategy

**Requirement**: Handle errors gracefully, provide clear messages

**Error Categories**:

1. **Argument Parsing Errors**:
   - Invalid range (start > end)
   - Invalid format (non-numeric)
   - Example: `Error: Invalid range 345-343 (start > end)`

2. **File Validation Errors**:
   - state.json missing
   - TODO.md missing
   - state.json invalid JSON
   - Example: `Error: state.json not found. Run /meta to regenerate.`

3. **Task Validation Errors**:
   - Task not found in state.json
   - Task not found in TODO.md
   - Example: `Error: Task 9999 not found in state.json`

4. **Sync Errors**:
   - status-sync-manager delegation failed
   - Atomic update failed
   - Example: `Error: Failed to sync task 343 (status-sync-manager returned failed status)`

**Error Handling Approach**:

```bash
# Fail fast on argument parsing errors
task_numbers=$(parse_task_numbers "$ARGUMENTS") || exit 1

# Fail fast on file validation errors
validate_files || exit 1

# Continue on task validation errors (skip invalid tasks)
for task_num in $task_numbers; do
  if ! validate_task "$task_num"; then
    echo "Warning: Skipping task $task_num (not found)"
    continue
  fi
  # ... sync task
done

# Continue on sync errors (report but don't abort)
for discrepancy in "${discrepancies[@]}"; do
  if ! sync_task "$discrepancy"; then
    echo "Error: Failed to sync task $task_number"
    failed_tasks+=("$task_number")
    continue
  fi
  synced_tasks+=("$task_number")
done

# Report results
echo "Synced ${#synced_tasks[@]} tasks"
if [[ ${#failed_tasks[@]} -gt 0 ]]; then
  echo "Failed to sync ${#failed_tasks[@]} tasks: ${failed_tasks[*]}"
fi
```

**Error Recovery**:
- No rollback needed (each task syncs independently)
- Failed tasks reported but don't abort entire sync
- User can retry failed tasks individually

### 5. Integration with Existing Commands

**Requirement**: Integrate `/task --sync` with existing `/task` command

**Current /task Command Structure**:

```
/task DESCRIPTION [FLAGS]

Flags:
  --priority Low|Medium|High
  --effort ESTIMATE
  --language lean|markdown|general|python|shell|json|meta
  --divide (divide into subtasks)
```

**Proposed /task --sync Structure**:

```
/task --sync [TASK_RANGES]

Examples:
  /task --sync                    # Sync all tasks
  /task --sync 343                # Sync task 343
  /task --sync 343-345            # Sync tasks 343-345
  /task --sync 337                # Sync task 337
  /task --sync 343-345, 337       # Sync tasks 343-345 and 337
```

**Argument Routing**:

```bash
# In /task command
if [[ "$1" == "--sync" ]]; then
  # Route to sync logic
  shift  # Remove --sync flag
  sync_tasks "$@"
  exit $?
fi

# Otherwise, route to task creation logic
create_task "$@"
```

**Conflict with Existing Flags**:
- `--sync` is a new flag, no conflicts with existing flags
- `--sync` is mutually exclusive with task creation (cannot create and sync simultaneously)
- Clear error if both provided: `Error: Cannot use --sync with task creation flags`

**Validation**:

```bash
# Validate flag combinations
if [[ "$sync_mode" == true ]] && [[ -n "$description" ]]; then
  echo "Error: Cannot use --sync with task description"
  echo "Usage: /task --sync [TASK_RANGES]"
  exit 1
fi

if [[ "$sync_mode" == true ]] && [[ -n "$priority" || -n "$effort" || -n "$language" || "$divide" == true ]]; then
  echo "Error: Cannot use --sync with task creation flags (--priority, --effort, --language, --divide)"
  echo "Usage: /task --sync [TASK_RANGES]"
  exit 1
fi
```

---

## Decisions

### Decision 1: Use state.json as Authoritative Source

**Rationale**:
- Task 279 findings: "Systematically fix metadata lookup to use state.json instead of TODO.md"
- state.json is the authoritative source per architecture
- TODO.md is synchronized user-facing view
- Eliminates need for git blame-based conflict resolution
- Simplifies implementation (per task 330 requirement: "avoid needless complexity")

**Trade-off**:
- **Pros**: Simpler, faster, aligns with task 279, eliminates git blame complexity
- **Cons**: No field-level conflict resolution (always prefers state.json)

**Justification**: Task 330 explicitly requests "avoid needless complexity". Using state.json as authoritative source is the simplest approach and aligns with architectural principles.

### Decision 2: Omit Dry-Run Mode

**Rationale**:
- Task 330 explicitly requests "omit dry-run mode"
- Dry-run mode adds 69 lines of preview logic
- Simplifies implementation
- Users can review changes via git diff after sync

**Trade-off**:
- **Pros**: Simpler implementation, fewer lines of code
- **Cons**: No preview before sync (users must trust sync logic)

**Justification**: Task 330 explicitly requests omitting dry-run mode. Users can review changes via `git diff` after sync if needed.

### Decision 3: Reuse /abandon Range Parsing Pattern

**Rationale**:
- Task 311 implemented proven range/list parsing for `/abandon`
- Pattern handles ranges (N-M), lists (N, M), and mixed syntax
- Deduplicates and sorts automatically
- Clear error messages
- Reusable for `/task --sync`

**Trade-off**:
- **Pros**: Proven pattern, handles all required cases, clear error messages
- **Cons**: None (pattern is well-tested and documented)

**Justification**: Reusing proven patterns reduces implementation risk and ensures consistency across commands.

### Decision 4: Delegate to status-sync-manager for Atomic Updates

**Rationale**:
- Task 333 findings: "All workflow commands must delegate to status-sync-manager for atomic TODO.md + state.json updates"
- Eliminates manual file manipulation (sed, awk, jq) which fails silently
- Ensures atomicity (both files update or neither)
- Provides validation and error recovery
- Aligns with architectural principles

**Trade-off**:
- **Pros**: Atomic updates, no manual file manipulation, validation, error recovery
- **Cons**: Delegation overhead (minimal, ~1-2s per task)

**Justification**: Delegation to status-sync-manager is the architectural requirement per task 333. Manual file manipulation causes synchronization failures.

### Decision 5: No Rollback for Sync Operations

**Rationale**:
- Each task syncs independently
- Failed tasks don't affect other tasks
- User can retry failed tasks individually
- Rollback adds complexity without significant benefit

**Trade-off**:
- **Pros**: Simpler implementation, no rollback logic needed
- **Cons**: Partial sync possible (some tasks succeed, some fail)

**Justification**: Sync operations are idempotent (can be retried safely). Rollback adds complexity without significant benefit for sync use case.

---

## Recommendations

### Recommendation 1: Implement Simplified Sync as /task --sync [RANGES]

**Approach**: 4-stage workflow (~200 lines)

```
Stage 1: Parse and Validate
  - Parse task number ranges (reuse /abandon pattern)
  - If no ranges: sync all tasks
  - Validate state.json exists and is valid
  - Validate TODO.md exists

Stage 2: Detect Discrepancies
  - For each task in range (or all tasks):
    * Extract metadata from state.json (authoritative)
    * Extract metadata from TODO.md
    * Compare fields: status, priority, effort, language, description
    * Record discrepancies

Stage 3: Apply Updates
  - For each discrepancy:
    * Delegate to status-sync-manager with update_task_metadata operation
    * Pass updated_fields object with state.json values
  - status-sync-manager ensures atomic updates

Stage 4: Report Results
  - Display count of tasks synced
  - Display fields updated
  - Display any errors
```

**Estimated Effort**: 6-8 hours

**Benefits**:
- Simpler than current /sync command (200 lines vs 553 lines)
- Avoids needless complexity (per task 330 requirement)
- Omits dry-run mode (per task 330 requirement)
- Uses state.json as authoritative source (per task 279)
- Delegates to status-sync-manager (per task 333)
- Reuses proven range parsing pattern (per task 311)

### Recommendation 2: Reuse Range/List Parsing from /abandon

**Pattern**: Proven in task 311

```bash
parse_task_numbers() {
  # Split by comma
  # For each part:
  #   - If range (N-M): Expand with seq
  #   - If single number: Add to list
  #   - Else: Error
  # Deduplicate and sort
}
```

**Benefits**:
- Proven pattern (task 311 completed successfully)
- Handles ranges, lists, and mixed syntax
- Deduplicates and sorts automatically
- Clear error messages

### Recommendation 3: Use state.json as Authoritative Source

**Approach**: Always prefer state.json values over TODO.md values

**Rationale**:
- Task 279 findings: state.json is authoritative source
- Eliminates need for git blame-based conflict resolution
- Simplifies implementation (per task 330 requirement)

**Benefits**:
- Simpler implementation (no git blame complexity)
- Faster execution (no git blame overhead)
- Aligns with architectural principles

### Recommendation 4: Delegate to status-sync-manager for Atomic Updates

**Approach**: Use `update_task_metadata` operation

**Rationale**:
- Task 333 findings: All workflow commands must delegate to status-sync-manager
- Eliminates manual file manipulation
- Ensures atomicity

**Benefits**:
- Atomic updates (both files or neither)
- No manual file manipulation (no sed, awk, jq)
- Validation and error recovery
- Aligns with architectural principles

### Recommendation 5: No Rollback for Sync Operations

**Approach**: Each task syncs independently, failed tasks reported but don't abort

**Rationale**:
- Sync operations are idempotent (can be retried safely)
- Rollback adds complexity without significant benefit

**Benefits**:
- Simpler implementation
- No rollback logic needed
- User can retry failed tasks individually

---

## Risks & Mitigations

### Risk 1: No Field-Level Conflict Resolution

**Description**: Always preferring state.json may overwrite recent TODO.md changes

**Likelihood**: Low (state.json is authoritative source per architecture)

**Impact**: Medium (user may lose TODO.md edits)

**Mitigation**:
1. Document that state.json is authoritative source
2. Recommend users edit state.json directly or use commands that update both files
3. Provide git diff review after sync
4. Consider adding `--dry-run` mode in future if needed

### Risk 2: Partial Sync on Errors

**Description**: Some tasks may sync successfully while others fail

**Likelihood**: Low (status-sync-manager is reliable)

**Impact**: Low (user can retry failed tasks)

**Mitigation**:
1. Report failed tasks clearly
2. Provide retry instructions
3. Sync operations are idempotent (safe to retry)

### Risk 3: Integration with Existing /task Command

**Description**: Adding `--sync` flag may conflict with existing flags or behavior

**Likelihood**: Low (clear separation between sync and create modes)

**Impact**: Medium (user confusion or errors)

**Mitigation**:
1. Validate flag combinations (error if --sync used with creation flags)
2. Clear error messages
3. Document usage examples
4. Test all flag combinations

### Risk 4: Performance on Large Task Lists

**Description**: Syncing all tasks may be slow if many tasks exist

**Likelihood**: Medium (current TODO.md has 45 active tasks)

**Impact**: Low (sync is infrequent operation)

**Mitigation**:
1. Support task ranges to sync subsets
2. Report progress during sync
3. Consider parallel delegation in future if needed

### Risk 5: Validation Utility Divergence

**Description**: validate_state_sync.py and /task --sync may have different validation logic

**Likelihood**: Medium (two separate implementations)

**Impact**: Low (both are valid approaches)

**Mitigation**:
1. Document differences between utilities
2. Recommend validate_state_sync.py for comprehensive validation
3. Recommend /task --sync for quick sync operations
4. Consider consolidating in future if needed

---

## Appendix: Sources and Citations

### Source 1: Current /sync Command

**File**: .opencode/command/sync.md  
**Lines**: 1-553  
**Relevance**: Comprehensive bidirectional synchronization with git blame-based conflict resolution

**Key Excerpts**:
- Line 4: `description: "Bidirectional synchronization of TODO.md and state.json using git blame timestamps"`
- Line 27: `<role>Sync command agent - Bidirectional synchronization of TODO.md and state.json with field-level precision</role>`
- Lines 34-377: 8-stage workflow with git blame, dry-run mode, extensive validation

### Source 2: /abandon Command Range Parsing

**File**: .opencode/command/abandon.md  
**Lines**: 1-200  
**Relevance**: Proven range/list parsing pattern

**Key Excerpts**:
- Line 8: `**Task Input (required):** $ARGUMENTS (task number, range, or list; e.g., `/abandon 298`, `/abandon 293-295`, `/abandon 302, 303`, `/abandon 293-295, 302, 303`)`
- Lines 25-43: Complete range parsing algorithm
- Lines 104-122: Usage examples

### Source 3: status-sync-manager Atomic Updates

**File**: .opencode/agent/subagents/status-sync-manager.md  
**Lines**: 1-1467  
**Relevance**: Atomic multi-file synchronization mechanism

**Key Excerpts**:
- Lines 374-477: `update_task_metadata_flow` operation
- Lines 232-262: Two-phase commit protocol
- Lines 717-785: Atomic write pattern

### Source 4: validate_state_sync.py Validation Utility

**File**: .opencode/scripts/validate_state_sync.py  
**Lines**: 1-782  
**Relevance**: Validation and repair logic

**Key Excerpts**:
- Lines 54-93: Validation checks
- Lines 188-258: Metadata consistency checks
- Lines 309-324: Status normalization
- Lines 414-447: Description repair logic

### Source 5: Task 279 Findings

**File**: .opencode/specs/TODO.md  
**Lines**: 719-733  
**Relevance**: state.json as authoritative source

**Key Excerpts**:
- Line 729: `When running /implement 276, the command output showed "Extract task 276 details from TODO.md" which indicates that commands and subagents are extracting metadata from TODO.md instead of from the authoritative source (state.json).`
- Line 732: `Establishes state.json as single source of truth, eliminates "Extract task NNN details from TODO.md" messages`

### Source 6: Task 333 Findings

**File**: .opencode/specs/TODO.md  
**Lines**: 63-82  
**Relevance**: Delegation to status-sync-manager requirement

**Key Excerpts**:
- Line 81: `Root cause identified in root-cause-analysis-todo-state-sync-failures.md: commands don't delegate to status-sync-manager for atomic updates. Solution: Add postflight stage to all workflow commands that delegates to status-sync-manager with validated_artifacts array, ensuring both files update atomically or neither updates.`

---

## Conclusion

This research provides a comprehensive analysis of implementing a `--sync` flag for the `/task` command. The recommended approach uses a simplified 4-stage workflow (~200 lines) that:

1. Reuses proven range/list parsing from `/abandon` command
2. Uses state.json as authoritative source (per task 279)
3. Delegates to status-sync-manager for atomic updates (per task 333)
4. Avoids needless complexity (per task 330 requirement)
5. Omits dry-run mode (per task 330 requirement)

**Estimated Effort**: 6-8 hours

**Next Steps**:
1. Create implementation plan based on this research
2. Implement `/task --sync` with 4-stage workflow
3. Test with various task ranges and edge cases
4. Document usage and integration with existing `/task` command
5. Consider future enhancements (parallel delegation, progress reporting)

The simplified approach provides the required functionality while avoiding the complexity of the current `/sync` command's git blame-based conflict resolution. By using state.json as the authoritative source and delegating to status-sync-manager for atomic updates, the implementation aligns with architectural principles and recent task findings (279, 333).
