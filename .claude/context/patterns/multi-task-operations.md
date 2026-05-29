# Multi-Task Operations Pattern

**Created**: 2026-04-02
**Purpose**: Define how workflow commands parse multi-task arguments, dispatch parallel skills, and produce consolidated output
**Audience**: Command developers implementing multi-task support in /research, /plan, /implement

---

## Overview

Workflow commands (`/research`, `/plan`, `/implement`) traditionally accept a single task number. This pattern extends them to accept multiple task numbers using the same range syntax already used by `/task --recover` and `/task --abandon`. When multiple tasks are specified, the command spawns one agent per task in parallel, collects results, and produces a batch commit with consolidated output.

**Design principles**:
- Single-task input falls through to existing flow unchanged (zero overhead for common case)
- Multi-task spawns independent agents with per-task isolation
- Failure of one task never blocks or rolls back other tasks
- Flags apply uniformly to all tasks in the batch

**Scope**: This pattern covers argument parsing, dispatch flow, batch commits, consolidated output, and error handling. It does NOT implement these changes -- tasks 351-353 apply this pattern to each command file.

---

## 1. Argument Parsing

### parse_task_args() Specification

The `parse_task_args()` function wraps the existing `parse_ranges()` function from `routing.md` to separate task numbers from remaining arguments (flags and focus prompts).

**Algorithm**:

```
Input: $ARGUMENTS (raw string from command invocation)

1. Scan from left, consuming characters that are:
   - Digits [0-9]
   - Commas [,]
   - Hyphens [-] between digits (range separator)
   - Whitespace adjacent to the above

2. Stop consuming when encountering:
   - An alphabetic character [a-zA-Z]
   - A flag marker [--]
   - End of input

3. Parse consumed portion through parse_ranges()
4. Remaining portion becomes $REMAINING_ARGS
```

**Pseudocode**:

```bash
parse_task_args() {
  local input="$1"
  local task_spec=""
  local remaining=""

  # Match leading task specification: digits, commas, hyphens, spaces
  # Stop at first alphabetic char or -- flag
  if [[ "$input" =~ ^([0-9][0-9,\ \-]*)(\ +.*)?$ ]]; then
    task_spec="${BASH_REMATCH[1]}"
    remaining="${BASH_REMATCH[2]}"
  else
    echo "[FAIL] No task number found in arguments"
    return 1
  fi

  # Trim trailing whitespace/commas from task_spec
  task_spec=$(echo "$task_spec" | sed 's/[, ]*$//')

  # Parse through existing parse_ranges()
  task_numbers=($(parse_ranges "$task_spec"))

  # Trim leading whitespace from remaining
  remaining=$(echo "$remaining" | sed 's/^[[:space:]]*//')

  echo "TASK_NUMBERS=${task_numbers[*]}"
  echo "REMAINING_ARGS=$remaining"
}
```

### Examples

| Input | task_numbers | remaining_args | Mode |
|-------|-------------|----------------|------|
| `7` | `[7]` | `` | single |
| `7, 22-24, 59` | `[7, 22, 23, 24, 59]` | `` | multi |
| `7 focus on APIs` | `[7]` | `focus on APIs` | single |
| `7, 22-24 --team` | `[7, 22, 23, 24]` | `--team` | multi |
| `42 --team --team-size 3` | `[42]` | `--team --team-size 3` | single |
| `10-12, 15 --force` | `[10, 11, 12, 15]` | `--force` | multi |

---

## 2. Single-Task Fallthrough

When `parse_task_args()` produces exactly one task number, the command proceeds through its existing checkpoint flow unchanged:

```
len(task_numbers) == 1
  -> task_number = task_numbers[0]
  -> Continue to CHECKPOINT 1: GATE IN
  -> Existing single-task flow (no changes)
```

**Backward compatibility guarantees**:
- Single task number (`/research 7`) behaves identically to current implementation
- Single task with focus prompt (`/research 7 focus on APIs`) behaves identically
- Single task with flags (`/research 7 --team`) behaves identically
- Ranges that resolve to one task (`/research 7-7` or `/research 7,7,7`) use single-task flow

---

## 3. Edge Cases

| Input | Resolution | Rationale |
|-------|-----------|-----------|
| `7-7` | Normalize to `[7]`, use single-task flow | Degenerate range |
| `7,7,7` | Deduplicate to `[7]`, use single-task flow | `parse_ranges()` deduplicates |
| `7, 22-24, 22` | Deduplicate to `[7, 22, 23, 24]` | `parse_ranges()` deduplicates and sorts |
| `7 -9` | `task_numbers=[7]`, `remaining="-9"` | Hyphen not between digits is not a range |
| `0` | Rejected by validation step (no task 0) | Task numbers start at 1 |
| (empty) | `[FAIL] No task number found` | Missing required argument |
| `abc` | `[FAIL] No task number found` | No leading digits |
| `7, 22-24 focus on APIs` | `task_numbers=[7,22,23,24]`, `remaining="focus on APIs"` | Focus prompt in multi-task applies to all tasks |

---

## 4. Multi-Task Dispatch Flow

When `parse_task_args()` produces more than one task number, the command enters multi-task mode. This inserts a **STAGE 0: PARSE AND DISPATCH** before the existing checkpoint flow.

### Flow Diagram

```
┌─────────────────────────────────────────────────────────┐
│  STAGE 0: PARSE AND DISPATCH                            │
│                                                         │
│  1. parse_task_args($ARGUMENTS)                         │
│  2. if len(task_numbers) == 1 --> single-task flow      │
│  3. if len(task_numbers) > 1  --> multi-task dispatch    │
│                                                         │
│  MULTI-TASK:                                            │
│  4. Validate all tasks (existence + status)             │
│  5. Generate batch session ID                           │
│  6. Route each task to appropriate skill                │
│  7. Invoke all skills in parallel (one per task)        │
│  8. Collect results from all skills                     │
│  9. Batch git commit (cleanup; may be empty)            │
│  10. Consolidated output                                │
└─────────────────────────────────────────────────────────┘
```

### Dispatch Decision

```
task_numbers = parse_task_args($ARGUMENTS)

if len(task_numbers) == 1:
    # SINGLE-TASK MODE
    task_number = task_numbers[0]
    # Fall through to existing CHECKPOINT 1: GATE IN
    # No changes to existing flow

elif len(task_numbers) > 1:
    # MULTI-TASK MODE
    # Continue to batch validation and dispatch below
```

---

## 5. Batch Validation

Before spawning any agents, validate all tasks exist and have valid status for the requested operation.

```bash
validated_tasks=()
invalid_tasks=()

for task_num in "${task_numbers[@]}"; do
  task_data=$(jq -r --argjson num "$task_num" \
    '.active_projects[] | select(.project_number == $num)' \
    specs/state.json)

  if [ -z "$task_data" ]; then
    invalid_tasks+=("$task_num: not found")
    continue
  fi

  status=$(echo "$task_data" | jq -r '.status')

  # Check status allows the requested operation
  if ! status_allows_operation "$status" "$command"; then
    invalid_tasks+=("$task_num: invalid status [$status]")
    continue
  fi

  validated_tasks+=("$task_num")
done
```

**Status validation per command**:

| Command | Allowed From Status |
|---------|-------------------|
| /research | not_started, researched |
| /plan | researched |
| /implement | planned, implementing (resume) |

**Handling invalid tasks**:

```
if invalid_tasks is not empty:
    Report warnings for each invalid task
    Continue with validated_tasks only

if validated_tasks is empty:
    [FAIL] No valid tasks to process
    Abort entirely
```

Invalid tasks are reported as warnings but do not block valid tasks from proceeding.

---

## 6. Parallel Skill Dispatch

### Architecture: Orchestrator-Loop Skill Invocation

Multi-task dispatch uses parallel Skill tool calls from the command's orchestrator loop. Each task maps to the appropriate skill for that task type, and all skills are invoked in a single message for parallel execution.

```
Command -> [Skill(skill-researcher, task 7), Skill(skill-planner, task 22), ...]
```

This keeps dispatch logic co-located with each command's validation and routing rules, avoiding an extra indirection layer. Each skill runs the full single-task lifecycle (preflight, agent delegation, postflight) independently.

### Batch Session ID

Generate a single session ID for the entire batch operation:

```bash
batch_session_id="sess_$(date +%s)_$(od -An -N3 -tx1 /dev/urandom | tr -d ' ')"
```

Each invoked skill receives a derived per-task session ID:

```
Per-task session: {batch_session_id}_{task_num}
```

### Spawning Pattern

The orchestrator invokes one skill per validated task using parallel Skill tool calls. Routing is per task_type using the same extension manifest lookup used for single-task dispatch:

```
# All invoked in a single message (parallel execution)
For each task_num in validated_tasks:
  Tool: Skill
  Parameters:
    skill: "{skill_name}"  # e.g., "skill-researcher" (routed per task_type)
    args: "task_number={task_num} session_id={batch_session_id}_{task_num} {remaining_args}"
```

Each invoked skill runs the full single-task lifecycle independently:
- Preflight status update (researching/planning/implementing)
- Agent delegation and execution
- Postflight status update
- Artifact creation
- Per-skill git commit (may occur before the batch commit at Step 4)

### Result Collection

After all parallel skills complete, the orchestrator collects their text return values. Each skill returns a brief text summary; the orchestrator reads `.return-meta.json` files in each task directory for structured data if needed:

```
Skill results (text summaries):
  task 7:  "Research completed: specs/007_.../reports/01_....md [RESEARCHED]"
  task 22: "Research completed: specs/022_.../reports/01_....md [RESEARCHED]"
  task 23: "Research failed: Agent timeout. Status: researching"
  task 24: "Research completed: specs/024_.../reports/01_....md [RESEARCHED]"
```

---

## 7. Interaction with --team Flag

Multi-task and team mode are orthogonal features:

| Feature | Scaling Direction | Description |
|---------|------------------|-------------|
| Multi-task | Horizontal (across tasks) | Run same command on multiple tasks |
| Team mode | Vertical (within a task) | Run multiple agents on a single task |

**Combined usage** (`/research 7, 22, 24 --team`):
- Each task gets its own team of agents
- Total agents spawned: `N_tasks * team_size`
- Example: 3 tasks with team_size=2 spawns 6 agents

**Cost warning**: Combining multi-task with `--team` multiplies token usage. For N tasks with team_size T, expect approximately `N * T * single_task_cost`. Use with care.

### Flag Compatibility Table

| Flag | Multi-task behavior |
|------|---------------------|
| `--team` | Applied to ALL tasks in batch (each task gets team mode) |
| `--team-size N` | Applied to ALL tasks uniformly |
| `--force` | Applied to ALL tasks (bypasses status validation) |
| Focus prompt | Applied to ALL tasks (same focus for each) |

**Not supported**: Per-task flags or per-task focus prompts. Users wanting different configurations per task should run separate commands.

---

## 8. Batch Git Commit Format

After all skills complete, the orchestrator produces a single batch git commit covering all successful tasks.

**Note on per-skill commits**: Each invoked skill runs its own postflight, which may produce an individual commit before the batch commit executes. The batch commit at Step 4 is a cleanup/consolidation step that captures any remaining unstaged changes. If per-skill postflight already committed all changes, the batch commit may be empty (which fails gracefully with no effect).

### Full Success

```
{command} tasks {range_summary}: {action}

Tasks: {comma-separated list}
Session: {batch_session_id}
```

**Example**:

```
research tasks 7, 22-24, 59: complete research

Tasks: 7, 22, 23, 24, 59
Session: sess_1743523200_abc123
```

### Partial Success

```
{command} tasks {range_summary}: {action} ({succeeded}/{total} succeeded)

Tasks completed: {comma-separated}
Tasks failed: {num} ({reason})[, {num} ({reason})]
Session: {batch_session_id}
```

**Example**:

```
research tasks 7, 22-24: complete research (3/4 succeeded)

Tasks completed: 7, 22, 24
Tasks failed: 23 (invalid status [IMPLEMENTING])
Session: sess_1743523200_abc123
```

### Commit Scope

The batch commit includes only changes from successful tasks:
- State.json updates for succeeded tasks
- TODO.md status changes for succeeded tasks
- Artifacts created by succeeded agents (reports, plans, summaries)

Failed tasks remain in their "in progress" status and are NOT included in the commit.

---

## 9. Consolidated Output Format

The orchestrator produces a consolidated output displayed to the user after all skills complete.

```markdown
## Batch {Command} Results

Session: {batch_session_id}
Tasks requested: {count}
Succeeded: {count}
Failed: {count}
Skipped: {count}

### Succeeded

| Task | Title | Status | Artifact |
|------|-------|--------|----------|
| #7 | task_title | [RESEARCHED] | specs/007_slug/reports/01_short.md |
| #22 | task_title | [RESEARCHED] | specs/022_slug/reports/01_short.md |

### Failed

| Task | Error |
|------|-------|
| #23 | Invalid status [IMPLEMENTING] |

### Skipped

| Task | Reason |
|------|--------|
| #99 | Not found in state.json |

### Next Steps
- /plan 7, 22, 24, 59
```

**Field definitions**:
- **Succeeded**: Tasks where the agent completed successfully and status was updated
- **Failed**: Tasks that were dispatched but the agent encountered an error
- **Skipped**: Tasks that failed validation before dispatch (not found, wrong status)
- **Next Steps**: Suggested follow-up command using succeeded task numbers

---

## 10. Partial-Success Error Handling

### Principle

Failure of one task MUST NOT block or roll back other tasks. Each agent manages its own task's state independently.

### Error Categories

| Error | When | Handling | User Recovery |
|-------|------|----------|---------------|
| Task not found | Validation (pre-dispatch) | Skip, report in Skipped section | Create task first, re-run |
| Invalid status | Validation (pre-dispatch) | Skip, report in Skipped section | Fix status, re-run |
| Agent timeout | During execution | Mark task partial, report in Failed | Re-run single task: `/{command} {N}` |
| Agent failure | During execution | Keep "in progress" status, report in Failed | Re-run single task: `/{command} {N}` |
| Git conflict | Post-execution commit | Non-blocking, log warning | Manual resolution |

### Per-Task Isolation

Each spawned agent operates independently:
- Writes only its own task's fields in state.json (scoped by project_number)
- Creates artifacts only in its own task directory (`specs/{NNN}_{SLUG}/`)
- Updates only its own task's status in TODO.md

If agent for task 23 fails:
- Task 23 status remains "researching" (in-progress variant)
- Tasks 7, 22, 24 transition to "researched" normally
- The batch commit includes only changes from tasks 7, 22, 24

### Concurrent State Safety

Multiple skills writing to state.json concurrently is safe because:
- Each skill writes to a specific `project_number` entry in `active_projects`
- jq operations are scoped: `select(.project_number == $num)`
- No skill modifies another task's fields

**Known limitation**: Rapid concurrent writes to state.json could cause read-modify-write races in edge cases. Scoped jq writes reduce this risk substantially. A future enhancement may add a consolidated state update after all skills complete if races are observed in practice.

---

## 11. Backward Compatibility

This pattern is fully backward compatible with existing single-task usage:

1. **Single task** (`/research 7`): `parse_task_args()` returns `[7]`, falls through to existing flow
2. **Single task with focus** (`/research 7 focus on APIs`): Parser separates `7` from `focus on APIs`
3. **Single task with flags** (`/research 7 --team`): Parser separates `7` from `--team`
4. **Existing /task flags** (`/task --recover 343-345`): Unaffected -- different command with flag-based routing via `/task` command file

No existing behavior changes. Multi-task mode activates only when multiple task numbers are detected in the argument string.

---

## 12. Command File Modification Guide

Tasks 351-353 apply this pattern to each workflow command. This section summarizes what each command file needs.

### Changes Common to All Three Commands

1. **Add STAGE 0 block** before CHECKPOINT 1: GATE IN
   - Call `parse_task_args($ARGUMENTS)` (inline the pseudocode from Section 1)
   - Add dispatch decision: single-task falls through, multi-task branches to batch dispatch

2. **Add multi-task dispatch branch**
   - Batch validation of all tasks
   - Generate batch session ID
   - Route each task to appropriate skill (per task_type extension lookup)
   - Invoke all skills in a single message (parallel Skill tool calls, one per task)
   - After all skills return: produce batch commit and consolidated output

3. **No changes to single-task flow**
   - Existing GATE IN, DELEGATE, GATE OUT, COMMIT remain unchanged
   - Single-task path is unmodified

### Per-Command Specifics

| Command | Status Validation | Skill Invoked | Action Verb |
|---------|------------------|---------------|-------------|
| `/research` | not_started, researched | skill-researcher (or extension research skill) | "complete research" |
| `/plan` | researched | skill-planner (or extension plan skill) | "create implementation plan" |
| `/implement` | planned, implementing | skill-implementer (or extension implement skill) | "complete implementation" |

### Batch Dispatch Architecture

Multi-task dispatch is handled by the orchestrator loop built into each command file (`/research`, `/plan`, `/implement`), not by a separate batch skill. Each command's MULTI-TASK DISPATCH section implements:

- Task type extraction per task (from state.json)
- Skill routing per task (using existing task-type-based routing from extension manifests)
- Parallel Skill tool calls (one skill per task, all invoked in a single message)
- Result collection from skill text returns (`.return-meta.json` for structured data)
- Consolidated status update and batch git commit

This approach keeps dispatch logic co-located with each command's validation and routing rules, avoiding an additional indirection layer. It is consistent with Section 6, which describes the same orchestrator-loop architecture.

---

## See Also

- `checkpoint-execution.md` -- Three-checkpoint command flow (GATE IN, DELEGATE, GATE OUT)
- `team-orchestration.md` -- Wave-based parallel agent spawning (precedent for parallel Skill/Task calls)
- `skill-lifecycle.md` -- Self-contained skill lifecycle management
- `routing.md` -- `parse_ranges()` function and task-type-based routing tables
