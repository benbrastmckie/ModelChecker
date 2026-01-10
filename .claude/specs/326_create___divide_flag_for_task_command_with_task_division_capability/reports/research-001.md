# Research Report: --divide Flag for /task Command with Task Division Capability

**Task**: 326 - Create --divide flag for /task command with task division capability  
**Started**: 2026-01-06  
**Completed**: 2026-01-06  
**Effort**: 12-16 hours (estimated)  
**Priority**: Medium  
**Dependencies**: None  
**Sources/Inputs**:
- .opencode/command/task.md (task creation command)
- .opencode/command/abandon.md (range/list parsing patterns)
- .opencode/specs/189_research_divide_flag/reports/research-001.md (--divide flag research for /research)
- .opencode/specs/325_create___recover_flag_for_task_command_to_unarchive_projects/reports/research-001.md (--recover flag patterns)
- .opencode/specs/archive/311_refactor_abandon_command_to_support_ranges_and_lists_of_task_numbers/reports/research-001.md (argument parsing)
- .opencode/agent/subagents/status-sync-manager.md (atomic task creation)
- .opencode/agent/subagents/atomic-task-numberer.md (task number allocation)
- .opencode/command/meta.md (task creation with plan artifacts)
- .opencode/specs/state.json (task metadata structure)

**Artifacts**: .opencode/specs/326_create___divide_flag_for_task_command_with_task_division_capability/reports/research-001.md  
**Standards**: status-markers.md, artifact-management.md, tasks.md, report.md

---

## Executive Summary

This research investigates implementing a `--divide` flag for the `/task` command that accepts an existing task number as an argument, analyzes the task description to divide it into an appropriate number of subtasks (1-5), creates the subtask entries atomically, and adds the new task numbers as dependencies to the original parent task. The implementation requires argument parsing for `/task --divide TASK_NUMBER [OPTIONAL_PROMPT]`, AI-driven task analysis to determine natural divisions, atomic task number allocation for multiple tasks, dependency management linking subtasks to parent, and atomic state synchronization across TODO.md and state.json.

**Key Findings**:
1. Current `/task` command supports `--divide` flag for NEW task creation (inline division during creation)
2. Task 189 researched `--divide` flag for `/research` command with topic subdivision patterns
3. Task 311 implemented range/list parsing patterns for `/abandon` command
4. status-sync-manager supports `create_task` operation but NOT bulk creation
5. Atomic task number allocation requires sequential calls to allocate N task numbers
6. Dependency management requires updating parent task metadata after subtask creation
7. AI-driven task analysis can identify 1-5 natural divisions from task description

**Recommended Approach**: Add `/task --divide TASK_NUMBER [OPTIONAL_PROMPT]` syntax, analyze parent task description for natural divisions (bullet points, conjunctions, sequential steps), allocate N task numbers atomically via state.json next_project_number, create N subtasks via status-sync-manager loop delegation, update parent task with subtask dependencies, and create git commit for all changes.

---

## Context & Scope

### Current /task Command Capabilities

The `/task` command (`.opencode/command/task.md`) currently supports:

**Task Creation**:
- Parse description from $ARGUMENTS
- Extract flags: `--priority`, `--effort`, `--language`, `--divide`
- Reformulate description inline (capitalize, punctuate, clarify)
- Detect language from keywords if not provided
- Delegate to status-sync-manager for atomic task creation

**Existing --divide Flag** (for NEW tasks):
```bash
/task "Refactor system: update commands, fix agents, improve docs" --divide
# → Creates 3 tasks:
#    Task 303: "Refactor system (1/3): Update commands."
#    Task 304: "Refactor system (2/3): Fix agents."
#    Task 305: "Refactor system (3/3): Improve docs."
```

**Current Division Logic** (Stage 3: DivideIfRequested):
1. Analyze description for natural divisions (bullet points, "and" conjunctions, commas, sequential steps)
2. Determine number of subtasks (1-5 based on natural divisions found)
3. Generate subtask descriptions (self-contained, clear scope)
4. Create task list with all subtasks
5. Delegate to status-sync-manager for each task

**Limitations**:
- Only works for NEW task creation (during `/task "description" --divide`)
- Does NOT work for EXISTING tasks (cannot divide task 123 after creation)
- No dependency tracking between divided tasks
- No parent-child relationship established

### Requirements for --divide TASK_NUMBER

The new `/task --divide TASK_NUMBER` syntax must:

**Functional Requirements**:
1. Accept existing task number: `/task --divide 326`
2. Accept optional prompt for division guidance: `/task --divide 326 "Focus on implementation phases"`
3. Validate task exists in state.json active_projects
4. Validate task status allows division (not completed, not abandoned)
5. Extract task description from state.json
6. Analyze description to determine natural divisions (1-5 subtasks)
7. Allocate N task numbers atomically (sequential allocation)
8. Create N subtask entries in TODO.md and state.json
9. Update parent task with subtask dependencies
10. Maintain atomic updates (all subtasks created or none)
11. Create git commit for all changes
12. Return subtask numbers and next steps to user

**Non-Functional Requirements**:
1. Performance: Complete within 120s timeout (current /task timeout)
2. Atomicity: All subtasks created or none (rollback on failure)
3. Consistency: Maintain TODO.md and state.json synchronization
4. Usability: Clear error messages, helpful recommendations
5. Backward Compatibility: Existing `/task "description" --divide` syntax still works

---

## Key Findings

### Finding 1: Existing --divide Flag for NEW Task Creation

The current `/task` command already implements `--divide` flag for NEW task creation:

**Stage 3: DivideIfRequested** (from task.md):
```markdown
<stage id="3" name="DivideIfRequested">
  <action>If --divide flag present, divide into 1-5 subtasks</action>
  <process>
    1. Check if --divide flag present:
       - If false: Skip to Stage 4 with single task
       - If true: Continue with division logic
    
    2. Analyze description for natural divisions:
       - Look for bullet points or numbered lists
       - Look for "and" conjunctions
       - Look for comma-separated items
       - Look for sequential steps (first, then, finally)
       - Look for multiple verbs (implement X, add Y, fix Z)
    
    3. Determine number of subtasks (1-5):
       - If no natural divisions found: 1 task (no division)
       - If 2-5 natural divisions found: create that many tasks
       - If >5 divisions found: group into 5 logical subtasks
       - Aim for balanced subtasks (similar complexity)
    
    4. Generate subtask descriptions:
       - Each subtask should be self-contained
       - Each subtask should have clear scope
       - Maintain original priority/effort for all subtasks
       - Number subtasks: "Task 1/3: ...", "Task 2/3: ...", etc.
    
    5. Prepare task list:
       - Array of task objects: [{title, description, priority, effort, language}, ...]
       - Validate each task has all required fields
       - Ensure total subtasks is 1-5
  </process>
</stage>
```

**Implications**:
- Division logic already exists and is well-tested
- Can reuse natural division analysis patterns
- Need to adapt for EXISTING task (read description from state.json instead of $ARGUMENTS)
- Need to add dependency tracking (not currently implemented)

### Finding 2: Task 189 Research on --divide Flag for /research Command

Task 189 researched `--divide` flag for `/research` command with comprehensive topic subdivision patterns:

**Key Patterns from Task 189**:

1. **Subtopic Count**: 3-5 subtopics (hierarchical for complex topics)
   - Simple topics (1-2 dimensions): 3 flat subtopics
   - Moderate topics (3-4 dimensions): 4-5 flat subtopics
   - Complex topics (5+ dimensions): 5 hierarchical subtopics

2. **Subdivision Criteria**:
   - Breadth: Cover distinct aspects of the topic
   - Orthogonality: Minimize overlap between subtopics
   - Depth: Each subtopic should be researchable independently
   - Balance: Roughly equal research effort per subtopic
   - Coherence: Subtopics should relate to central research question

3. **Subdivision Process**:
   - Analyze topic complexity (count dimensions/aspects)
   - Determine subtopic count (3 for simple, 4-5 for moderate/complex)
   - Generate subtopics using criteria
   - Validate subtopics (no overlap, comprehensive coverage, actionable)
   - Record subtopics in metadata

**Implications**:
- Can adapt subdivision criteria for task division
- 3-5 subtasks is optimal range (matches research findings)
- Need to analyze task description complexity
- Need to validate subtasks are self-contained and actionable

### Finding 3: Task 311 Argument Parsing Patterns

Task 311 implemented range/list parsing for `/abandon` command:

**Parsing Pattern** (from task 311 research):
```bash
# Parse task numbers from $ARGUMENTS
parse_task_numbers() {
  local input="$1"
  local task_numbers=()
  
  # Split by comma
  IFS=',' read -ra PARTS <<< "$input"
  
  for part in "${PARTS[@]}"; do
    # Trim whitespace
    part=$(echo "$part" | xargs)
    
    # Check if range pattern (N-M)
    if [[ "$part" =~ ^([0-9]+)-([0-9]+)$ ]]; then
      start="${BASH_REMATCH[1]}"
      end="${BASH_REMATCH[2]}"
      
      # Validate start <= end
      if [ "$start" -gt "$end" ]; then
        echo "Error: Invalid range $start-$end (start > end)"
        return 1
      fi
      
      # Expand range
      for num in $(seq "$start" "$end"); do
        task_numbers+=("$num")
      done
    
    # Check if single number
    elif [[ "$part" =~ ^[0-9]+$ ]]; then
      task_numbers+=("$part")
    
    # Invalid format
    else
      echo "Error: Invalid task number format: '$part'"
      return 1
    fi
  done
  
  # Deduplicate and sort
  task_numbers=($(printf '%s\n' "${task_numbers[@]}" | sort -nu))
  
  echo "${task_numbers[@]}"
}
```

**Implications**:
- Can reuse parsing pattern for `/task --divide TASK_NUMBER`
- Need to validate single task number (not range/list)
- Need to extract optional prompt after task number
- Format: `/task --divide 326 [optional prompt]`

### Finding 4: status-sync-manager create_task Operation

The status-sync-manager supports `create_task` operation for single task creation:

**create_task_flow** (from status-sync-manager.md):
```markdown
<create_task_flow>
  <step_0_validate_inputs>
    - Validate title, description, priority, effort, language
    - Read next_project_number from state.json
    - Validate task number not already in use
  </step_0_validate_inputs>

  <step_1_prepare_entries>
    - Generate task slug from title
    - Format TODO.md entry
    - Format state.json entry
  </step_1_prepare_entries>

  <step_2_prepare_update>
    - Read current TODO.md and state.json
    - Insert TODO.md entry in correct priority section
    - Append entry to active_projects array
    - Increment next_project_number by 1
  </step_2_prepare_update>

  <step_3_commit>
    - Write to temp files with session_id
    - Verify temp files
    - Atomic rename (both files or neither)
    - Clean up temp files
  </step_3_commit>

  <step_4_return>
    - Return task number created
    - Return files updated
  </step_4_return>
</create_task_flow>
```

**Implications**:
- status-sync-manager does NOT support bulk task creation
- Need to call create_task N times for N subtasks (loop delegation)
- Each call increments next_project_number by 1 (sequential allocation)
- Atomic per task, but NOT atomic across all subtasks
- Need rollback mechanism if any subtask creation fails

### Finding 5: Atomic Task Number Allocation

The atomic-task-numberer allocates single task numbers:

**Allocation Pattern** (from atomic-task-numberer.md):
```markdown
<process_flow>
  <step_1>Read TODO.md, parse task numbers</step_1>
  <step_2>Find highest task number</step_2>
  <step_3>Calculate next task number (highest + 1)</step_3>
  <step_4>Return task number</step_4>
</process_flow>
```

**Alternative: state.json next_project_number**:
- state.json tracks next_project_number field
- Incremented by 1 for each task created
- More reliable than parsing TODO.md
- Used by status-sync-manager create_task operation

**Implications**:
- For N subtasks, need to allocate N sequential task numbers
- Can read next_project_number from state.json
- Allocate: next, next+1, next+2, ..., next+N-1
- Update next_project_number to next+N after all subtasks created
- Atomic allocation via state.json lock (temp file pattern)

### Finding 6: Dependency Management

Current task metadata structure (from state.json):
```json
{
  "project_number": 326,
  "project_name": "create___divide_flag_for_task_command",
  "type": "feature",
  "status": "not_started",
  "priority": "medium",
  "language": "meta",
  "description": "Create a --divide flag for the /task command...",
  "effort": "TBD",
  "blocking": [],
  "dependencies": [],
  "created": "2026-01-05T00:00:00Z",
  "last_updated": "2026-01-06T00:00:00Z"
}
```

**Dependencies Field**:
- Array of task numbers that this task depends on
- Example: `"dependencies": [327, 328, 329]` means task 326 depends on 327, 328, 329
- Used for task ordering and blocking detection

**Implications**:
- After creating subtasks, need to update parent task dependencies
- Parent task 326 should have dependencies: [327, 328, 329] (subtask numbers)
- Need to use status-sync-manager update_task_metadata operation
- Atomic update to parent task after all subtasks created

### Finding 7: AI-Driven Task Analysis

Task division requires analyzing task description to identify natural divisions:

**Analysis Patterns** (from task.md Stage 3):
1. **Bullet points or numbered lists**: Each item becomes a subtask
2. **"and" conjunctions**: Split on "and" to create subtasks
3. **Comma-separated items**: Each item becomes a subtask
4. **Sequential steps**: "first", "then", "finally" indicate subtasks
5. **Multiple verbs**: "implement X, add Y, fix Z" creates 3 subtasks

**Example Analysis**:
```
Task Description: "Create a --divide flag for the /task command that accepts a task number as an argument. This flag should divide an existing task into an appropriate number of subtasks, add the new task numbers as dependencies to the original task, and create the new task entries atomically."

Natural Divisions:
1. "accepts a task number as an argument" → Subtask 1: Argument parsing
2. "divide an existing task into an appropriate number of subtasks" → Subtask 2: Task analysis and division
3. "add the new task numbers as dependencies to the original task" → Subtask 3: Dependency management
4. "create the new task entries atomically" → Subtask 4: Atomic task creation

Result: 4 subtasks
```

**Implications**:
- Can use existing division logic from Stage 3
- Need to read task description from state.json (not $ARGUMENTS)
- Need to validate subtasks are actionable and self-contained
- Need to preserve parent task context in subtask descriptions

---

## Detailed Analysis

### Task Division Workflow

**Step 1: Parse Input**
```
Input: /task --divide 326 [optional prompt]
Parse: flag = "--divide", task_number = 326, prompt = [optional]
Validate: task_number is positive integer
```

**Step 2: Validate Parent Task**
```
Read: state.json
Find: task with project_number == 326
Validate: task exists in active_projects
Validate: task status allows division (not completed, not abandoned, not already divided)
Extract: task description, priority, effort, language
```

**Step 3: Analyze Task for Natural Divisions**
```
Input: task description + optional prompt
Analyze: bullet points, conjunctions, commas, sequential steps, multiple verbs
Determine: number of subtasks (1-5)
Generate: subtask descriptions (self-contained, clear scope)
Validate: subtasks are actionable, no overlap, comprehensive coverage
```

**Step 4: Allocate Task Numbers**
```
Read: state.json next_project_number
Allocate: N sequential task numbers (next, next+1, ..., next+N-1)
Reserve: Update next_project_number to next+N (in memory, not committed yet)
```

**Step 5: Create Subtasks Atomically**
```
For each subtask (1 to N):
  Delegate to status-sync-manager:
    - operation: "create_task"
    - title: subtask title
    - description: subtask description
    - priority: parent priority
    - effort: parent effort / N (or "TBD")
    - language: parent language
    - timestamp: current date
    - session_id: unique session ID
  
  Collect task_number from return
  
  If any creation fails:
    - Rollback: Delete created subtasks (loop through created_tasks)
    - Abort: Return error with rollback details
```

**Step 6: Update Parent Task Dependencies**
```
Delegate to status-sync-manager:
  - operation: "update_task_metadata"
  - task_number: 326 (parent)
  - updated_fields: {
      "dependencies": [327, 328, 329, 330],  // subtask numbers
      "status": "blocked",  // optional: mark parent as blocked until subtasks complete
      "blocking_reason": "Waiting for subtasks 327-330 to complete"  // optional
    }
  - timestamp: current date
  - session_id: unique session ID

Validate: Parent task updated successfully
```

**Step 7: Create Git Commit**
```
Stage files:
  - TODO.md (parent task updated, subtasks added)
  - state.json (parent task updated, subtasks added, next_project_number incremented)

Commit:
  - Message: "task: divide task 326 into 4 subtasks (327-330)"
  - Scope: TODO.md, state.json
```

**Step 8: Return Success**
```
Return:
  - status: "completed"
  - parent_task: 326
  - subtasks: [327, 328, 329, 330]
  - files_updated: [TODO.md, state.json]
  - message: "Task 326 divided into 4 subtasks"
  - next_steps: "Use /implement 327 to start first subtask"
```

### Argument Parsing Strategy

**Format**: `/task --divide TASK_NUMBER [OPTIONAL_PROMPT]`

**Parsing Logic**:
```bash
# Stage 1: ParseInput
if [[ "$ARGUMENTS" =~ ^--divide[[:space:]]+([0-9]+)(.*)$ ]]; then
  # --divide flag detected
  task_number="${BASH_REMATCH[1]}"
  optional_prompt="${BASH_REMATCH[2]}"
  optional_prompt=$(echo "$optional_prompt" | xargs)  # trim whitespace
  
  # Validate task_number
  if [ -z "$task_number" ]; then
    echo "Error: Task number required after --divide flag"
    echo "Usage: /task --divide TASK_NUMBER [optional prompt]"
    exit 1
  fi
  
  # Skip to Stage 5 (DivideExistingTask)
  # Do NOT proceed to Stage 2-4 (new task creation)
else
  # Normal task creation flow
  # Continue with existing logic
fi
```

**Validation**:
- Task number is positive integer
- Task exists in state.json active_projects
- Task status is not "completed" or "abandoned"
- Task does not already have dependencies (not already divided)

### Subtask Naming Convention

**Pattern**: `{parent_title} ({index}/{total}): {subtask_aspect}`

**Examples**:
```
Parent: "Create --divide flag for /task command with task division capability"

Subtask 1: "Create --divide flag (1/4): Implement argument parsing and validation"
Subtask 2: "Create --divide flag (2/4): Analyze task description for natural divisions"
Subtask 3: "Create --divide flag (3/4): Create subtasks atomically with dependency tracking"
Subtask 4: "Create --divide flag (4/4): Update parent task and create git commit"
```

**Benefits**:
- Clear parent-child relationship
- Shows progress (1/4, 2/4, etc.)
- Describes specific aspect of subtask
- Maintains context from parent task

### Dependency Management Strategy

**Option 1: Parent Depends on Subtasks** (Recommended)
```json
{
  "project_number": 326,
  "dependencies": [327, 328, 329, 330],
  "status": "blocked",
  "blocking_reason": "Waiting for subtasks 327-330 to complete"
}
```

**Benefits**:
- Clear dependency chain
- Parent cannot be implemented until subtasks complete
- Automatic blocking detection
- Follows standard dependency model

**Option 2: Subtasks Depend on Parent**
```json
{
  "project_number": 327,
  "dependencies": [326],
  "description": "Subtask 1 of task 326"
}
```

**Drawbacks**:
- Circular dependency (parent creates subtasks, subtasks depend on parent)
- Confusing dependency model
- Parent can be implemented before subtasks

**Decision**: Use Option 1 (parent depends on subtasks)

### Rollback Mechanism

**Scenario**: Subtask 3 creation fails after subtasks 1 and 2 created

**Rollback Process**:
```
1. Detect failure: status-sync-manager returns status "failed"
2. Log error: "Failed to create subtask 3 of 4"
3. Rollback created subtasks:
   - For each created subtask (327, 328):
     * Delegate to status-sync-manager with operation "delete_task" (if exists)
     * OR: Manually remove from TODO.md and state.json
4. Restore next_project_number: Decrement by number of created subtasks
5. Return error: "Failed to divide task 326, rolled back 2 subtasks"
6. Recommendation: "Check error details and retry"
```

**Atomic Guarantee**: All subtasks created or none (via rollback)

### Edge Cases

**Case 1: Task Already Divided**
- Parent task already has dependencies
- Solution: Abort with error "Task 326 already has dependencies (already divided?)"
- Recommendation: "Use /task --divide on individual subtasks if needed"

**Case 2: Task Too Simple to Divide**
- Analysis finds no natural divisions (1 subtask)
- Solution: Abort with error "Task 326 cannot be divided (no natural divisions found)"
- Recommendation: "Task is already atomic, implement directly with /implement 326"

**Case 3: Task Description Too Vague**
- Description is too short or generic to analyze
- Solution: Require optional prompt for division guidance
- Error: "Task description too vague, provide division prompt"
- Example: `/task --divide 326 "Divide into phases: research, planning, implementation"`

**Case 4: Subtask Creation Partial Failure**
- 2 of 4 subtasks created, then failure
- Solution: Rollback created subtasks (see Rollback Mechanism)
- Atomic guarantee maintained

**Case 5: Parent Task Update Failure**
- All subtasks created, but parent update fails
- Solution: Log warning, continue (non-critical)
- Subtasks exist and are usable
- User can manually update parent task dependencies

---

## Code Examples

### Example 1: /task Command Flag Parsing

```markdown
<stage id="1" name="ParseInput">
  <action>Parse task description and extract flags</action>
  <process>
    1. Check for --divide flag with task number:
       - Pattern: --divide TASK_NUMBER [optional prompt]
       - If present: Extract task_number and optional_prompt
       - Validate task_number is positive integer
       - Skip to Stage 5 (DivideExistingTask)
       - Do NOT proceed to Stage 2-4 (new task creation)
    
    2. Check for --divide flag without task number (existing behavior):
       - Pattern: "description" --divide
       - If present: Set divide = true
       - Continue with normal task creation flow (Stage 2-4)
    
    3. If neither pattern matches:
       - Continue with normal task creation flow
       - Extract description, priority, effort, language flags
  </process>
  <validation>
    - If --divide TASK_NUMBER: task_number is positive integer
    - If --divide (inline): description is non-empty
  </validation>
  <checkpoint>Input parsed, mode determined (divide existing vs create new)</checkpoint>
</stage>

<stage id="5" name="DivideExistingTask">
  <action>Divide existing task into subtasks</action>
  <process>
    1. Validate parent task:
       - Read state.json
       - Find task by project_number
       - Validate task exists in active_projects
       - Validate status allows division (not completed, not abandoned)
       - Validate task does not already have dependencies
       - Extract: description, priority, effort, language
    
    2. Analyze task for natural divisions:
       - Input: task description + optional_prompt
       - Analyze: bullet points, conjunctions, commas, sequential steps
       - Determine: number of subtasks (1-5)
       - Generate: subtask descriptions (self-contained, clear scope)
       - Validate: subtasks are actionable, no overlap
       - If no divisions found: Abort with error
    
    3. Allocate task numbers:
       - Read next_project_number from state.json
       - Allocate N sequential numbers: next, next+1, ..., next+N-1
       - Prepare to update next_project_number to next+N
    
    4. Create subtasks atomically:
       - For each subtask (1 to N):
         * Delegate to status-sync-manager (create_task)
         * Collect task_number from return
         * If any creation fails: Rollback and abort
    
    5. Update parent task dependencies:
       - Delegate to status-sync-manager (update_task_metadata)
       - Set dependencies to subtask numbers
       - Optionally set status to "blocked"
       - If update fails: Log warning (non-critical)
    
    6. Create git commit:
       - Stage: TODO.md, state.json
       - Commit: "task: divide task {number} into {N} subtasks"
    
    7. Return success:
       - parent_task: task number
       - subtasks: array of subtask numbers
       - files_updated: [TODO.md, state.json]
       - next_steps: "Use /implement {first_subtask} to start"
  </process>
  <checkpoint>Task divided, subtasks created, parent updated, git committed</checkpoint>
</stage>
```

### Example 2: Task Analysis for Natural Divisions

```python
def analyze_task_for_divisions(description, optional_prompt=None):
    """
    Analyze task description to identify natural divisions.
    
    Args:
        description: Task description from state.json
        optional_prompt: Optional user guidance for division
    
    Returns:
        List of subtask descriptions (1-5 items)
    """
    divisions = []
    
    # Pattern 1: Bullet points or numbered lists
    if re.search(r'^\s*[-*•]\s+', description, re.MULTILINE):
        # Extract bullet points
        bullets = re.findall(r'^\s*[-*•]\s+(.+)$', description, re.MULTILINE)
        divisions.extend(bullets[:5])  # Max 5
    
    # Pattern 2: "and" conjunctions
    elif ' and ' in description.lower():
        # Split on "and"
        parts = re.split(r'\s+and\s+', description, flags=re.IGNORECASE)
        divisions.extend(parts[:5])
    
    # Pattern 3: Comma-separated items
    elif description.count(',') >= 2:
        # Split on commas
        parts = [p.strip() for p in description.split(',')]
        divisions.extend(parts[:5])
    
    # Pattern 4: Sequential steps
    elif re.search(r'\b(first|then|finally|next|after)\b', description, re.IGNORECASE):
        # Extract sequential steps
        steps = re.split(r'\b(first|then|finally|next|after)\b', description, flags=re.IGNORECASE)
        steps = [s.strip() for s in steps if s.strip() and s.lower() not in ['first', 'then', 'finally', 'next', 'after']]
        divisions.extend(steps[:5])
    
    # Pattern 5: Multiple verbs (implement X, add Y, fix Z)
    elif len(re.findall(r'\b(implement|add|fix|create|update|remove|refactor)\b', description, re.IGNORECASE)) >= 2:
        # Extract verb phrases
        verbs = re.findall(r'\b(implement|add|fix|create|update|remove|refactor)\s+[^,.]+', description, re.IGNORECASE)
        divisions.extend(verbs[:5])
    
    # Use optional prompt for guidance if no natural divisions found
    if not divisions and optional_prompt:
        # Analyze optional prompt for division guidance
        # Example: "Divide into phases: research, planning, implementation"
        if 'phases' in optional_prompt.lower() or 'steps' in optional_prompt.lower():
            phases = re.findall(r':\s*(.+)$', optional_prompt)
            if phases:
                divisions = [p.strip() for p in phases[0].split(',')][:5]
    
    # Validate divisions
    if not divisions:
        return None  # No natural divisions found
    
    # Clean and format divisions
    divisions = [d.strip().capitalize() for d in divisions if d.strip()]
    
    # Limit to 5 subtasks
    divisions = divisions[:5]
    
    return divisions
```

### Example 3: Subtask Creation with Rollback

```python
def create_subtasks_with_rollback(parent_task, subtask_descriptions, session_id):
    """
    Create subtasks atomically with rollback on failure.
    
    Args:
        parent_task: Parent task metadata
        subtask_descriptions: List of subtask descriptions
        session_id: Unique session ID
    
    Returns:
        List of created subtask numbers or None on failure
    """
    created_subtasks = []
    
    try:
        # Allocate task numbers
        next_number = read_next_project_number()
        subtask_numbers = list(range(next_number, next_number + len(subtask_descriptions)))
        
        # Create each subtask
        for i, description in enumerate(subtask_descriptions):
            # Format subtask title
            title = f"{parent_task['title']} ({i+1}/{len(subtask_descriptions)}): {description}"
            
            # Delegate to status-sync-manager
            result = delegate_to_status_sync_manager(
                operation="create_task",
                title=title,
                description=description,
                priority=parent_task['priority'],
                effort="TBD",  # or parent_task['effort'] / len(subtask_descriptions)
                language=parent_task['language'],
                timestamp=current_date(),
                session_id=session_id
            )
            
            # Check result
            if result['status'] != 'completed':
                raise Exception(f"Failed to create subtask {i+1}: {result['errors']}")
            
            # Collect task number
            task_number = result['metadata']['task_number']
            created_subtasks.append(task_number)
        
        return created_subtasks
    
    except Exception as e:
        # Rollback: Delete created subtasks
        for task_number in created_subtasks:
            try:
                # Delete subtask (remove from TODO.md and state.json)
                delete_task(task_number, session_id)
            except:
                # Log error but continue rollback
                log_error(f"Failed to rollback subtask {task_number}")
        
        # Return None to indicate failure
        return None
```

---

## Decisions

### Decision 1: Syntax for Dividing Existing Tasks

**Question**: What syntax should be used for dividing existing tasks?

**Options**:
1. `/task --divide TASK_NUMBER [optional prompt]`
2. `/divide TASK_NUMBER [optional prompt]` (separate command)
3. `/task TASK_NUMBER --divide [optional prompt]`

**Decision**: `/task --divide TASK_NUMBER [optional prompt]`

**Rationale**:
- Consistent with existing `/task --divide` syntax for new tasks
- Keeps task-related operations in one command
- Clear flag-first pattern (easier to parse)
- Follows pattern of `/task --recover TASK_NUMBER`

### Decision 2: Parent Task Status After Division

**Question**: Should parent task status change after division?

**Options**:
1. Keep status unchanged (e.g., "not_started")
2. Change status to "blocked" until subtasks complete
3. Change status to "divided" (new status)

**Decision**: Change status to "blocked" (optional, user choice)

**Rationale**:
- Parent task cannot be implemented until subtasks complete
- "blocked" status is standard and well-understood
- Blocking reason clearly indicates waiting for subtasks
- Can be made optional via flag (e.g., `--no-block`)

### Decision 3: Subtask Effort Estimation

**Question**: How should subtask effort be estimated?

**Options**:
1. Set all subtasks to "TBD"
2. Divide parent effort equally (e.g., 12h → 3h each for 4 subtasks)
3. Use AI to estimate effort per subtask

**Decision**: Set all subtasks to "TBD" (default)

**Rationale**:
- Effort estimation is complex and error-prone
- Equal division assumes uniform complexity (often wrong)
- AI estimation requires additional research
- "TBD" is safe default, can be updated later
- Can add `--estimate-effort` flag later if needed

### Decision 4: Rollback Strategy

**Question**: How should rollback be handled if subtask creation fails?

**Options**:
1. Delete created subtasks, restore state
2. Keep created subtasks, log error
3. Mark created subtasks as "abandoned"

**Decision**: Delete created subtasks, restore state (Option 1)

**Rationale**:
- Atomic guarantee: all subtasks created or none
- Prevents partial division (confusing state)
- Clean rollback (no orphaned tasks)
- User can retry division after fixing issue

### Decision 5: Dependency Direction

**Question**: Should parent depend on subtasks or vice versa?

**Options**:
1. Parent depends on subtasks (parent.dependencies = [subtask1, subtask2, ...])
2. Subtasks depend on parent (subtask.dependencies = [parent])
3. Bidirectional dependencies

**Decision**: Parent depends on subtasks (Option 1)

**Rationale**:
- Parent cannot be implemented until subtasks complete
- Standard dependency model (task depends on prerequisites)
- Automatic blocking detection
- Clear dependency chain for task ordering

---

## Recommendations

### Recommendation 1: Implement /task --divide TASK_NUMBER Syntax

Add `/task --divide TASK_NUMBER [optional prompt]` syntax to divide existing tasks:
- Parse `--divide TASK_NUMBER` flag in Stage 1
- Validate task exists and allows division
- Analyze task description for natural divisions
- Create subtasks atomically with rollback
- Update parent task dependencies
- Create git commit

**Priority**: High  
**Effort**: 6-8 hours

### Recommendation 2: Add Dependency Management to status-sync-manager

Extend status-sync-manager update_task_metadata operation to support dependency updates:
- Accept `dependencies` field in updated_fields
- Validate dependency task numbers exist
- Update parent task dependencies atomically
- Handle circular dependency detection

**Priority**: High  
**Effort**: 2-3 hours

### Recommendation 3: Add Rollback Mechanism for Subtask Creation

Implement rollback mechanism for atomic subtask creation:
- Track created subtasks during loop delegation
- On failure: Delete created subtasks
- Restore next_project_number
- Return error with rollback details

**Priority**: High  
**Effort**: 2-3 hours

### Recommendation 4: Add Task Division Tests

Create tests for task division scenarios:
- Successful division (2-5 subtasks)
- Task not found
- Task already divided (has dependencies)
- Task too simple (no natural divisions)
- Subtask creation partial failure (rollback)
- Parent task update failure (non-critical)

**Priority**: Medium  
**Effort**: 3-4 hours

### Recommendation 5: Update Documentation

Update documentation for `/task --divide` feature:
- Command usage (add --divide TASK_NUMBER syntax)
- Task division workflow
- Dependency management
- Rollback mechanism
- Error handling

**Priority**: Medium  
**Effort**: 1-2 hours

---

## Risks & Mitigations

### Risk 1: Partial Subtask Creation Failure

**Risk**: Some subtasks created, then failure (partial division)

**Likelihood**: Medium  
**Impact**: High

**Mitigation**:
- Implement rollback mechanism (delete created subtasks)
- Atomic guarantee via rollback
- Test rollback thoroughly
- Log rollback details for debugging

### Risk 2: Parent Task Update Failure

**Risk**: All subtasks created, but parent update fails

**Likelihood**: Low  
**Impact**: Medium

**Mitigation**:
- Treat parent update as non-critical
- Log warning and continue
- Subtasks are usable even without parent update
- User can manually update parent dependencies

### Risk 3: Task Analysis Produces Poor Divisions

**Risk**: AI analysis creates non-actionable or overlapping subtasks

**Likelihood**: Medium  
**Impact**: Medium

**Mitigation**:
- Validate subtasks are self-contained
- Require optional prompt for vague tasks
- Allow user to review and reject divisions
- Provide clear error messages for poor divisions

### Risk 4: Circular Dependency Creation

**Risk**: Parent depends on subtasks, subtasks depend on parent

**Likelihood**: Low  
**Impact**: High

**Mitigation**:
- Use unidirectional dependencies (parent → subtasks only)
- Validate no circular dependencies in status-sync-manager
- Detect and abort on circular dependency

### Risk 5: Task Number Allocation Conflict

**Risk**: Multiple concurrent divisions allocate same task numbers

**Likelihood**: Very Low  
**Impact**: High

**Mitigation**:
- Use state.json next_project_number as single source of truth
- Atomic updates via temp file pattern
- Sequential allocation (no parallelism)
- Validate task numbers not already in use

---

## Effort Estimation

### Phase 1: Argument Parsing and Validation (2-3 hours)
- Add `/task --divide TASK_NUMBER` parsing to Stage 1
- Validate task exists and allows division
- Extract task metadata from state.json
- Add error handling for invalid input

### Phase 2: Task Analysis and Division (3-4 hours)
- Implement task analysis for natural divisions
- Adapt existing division logic from Stage 3
- Add optional prompt support for division guidance
- Validate subtasks are actionable and self-contained

### Phase 3: Atomic Subtask Creation (3-4 hours)
- Allocate N task numbers from next_project_number
- Loop delegation to status-sync-manager for each subtask
- Implement rollback mechanism for partial failures
- Track created subtasks for rollback

### Phase 4: Dependency Management (2-3 hours)
- Update parent task dependencies via status-sync-manager
- Optionally update parent status to "blocked"
- Handle parent update failure (non-critical)

### Phase 5: Git Integration and Testing (2-3 hours)
- Create git commit for all changes
- Add tests for division scenarios
- Test rollback mechanism
- Update documentation

**Total Estimated Effort**: 12-17 hours

---

## Appendix: Sources and Citations

### Source 1: /task Command Specification
- **File**: `.opencode/command/task.md`
- **Key Sections**: ParseInput, DivideIfRequested, CreateTasks
- **Relevance**: Existing --divide flag for new tasks, division logic, delegation patterns

### Source 2: Task 189 Research Report
- **File**: `.opencode/specs/189_research_divide_flag/reports/research-001.md`
- **Key Sections**: Topic subdivision strategy, subtopic count, subdivision criteria
- **Relevance**: Division patterns, 3-5 subtask optimal range, validation criteria

### Source 3: Task 311 Research Report
- **File**: `.opencode/specs/archive/311_refactor_abandon_command_to_support_ranges_and_lists_of_task_numbers/reports/research-001.md`
- **Key Sections**: Argument parsing patterns, range/list syntax
- **Relevance**: Parsing patterns for task numbers, validation, error handling

### Source 4: status-sync-manager Specification
- **File**: `.opencode/agent/subagents/status-sync-manager.md`
- **Key Sections**: create_task_flow, update_task_metadata_flow, atomic write pattern
- **Relevance**: Task creation, dependency updates, atomic operations

### Source 5: atomic-task-numberer Specification
- **File**: `.opencode/agent/subagents/atomic-task-numberer.md`
- **Key Sections**: Task number allocation, next_project_number
- **Relevance**: Sequential task number allocation, atomic allocation

### Source 6: /meta Command Specification
- **File**: `.opencode/command/meta.md`
- **Key Sections**: CreateTasksWithArtifacts, task creation with plan artifacts
- **Relevance**: Multiple task creation patterns, artifact management

### Source 7: state.json Schema
- **File**: `.opencode/specs/state.json`
- **Key Fields**: active_projects, next_project_number, dependencies
- **Relevance**: Task metadata structure, dependency tracking

---

## Conclusion

The `--divide` flag for the `/task` command is a valuable enhancement that enables dividing existing tasks into subtasks with automatic dependency tracking. The implementation builds on existing patterns from the `/task` command's inline division logic, task 189's subdivision research, and task 311's argument parsing patterns.

The recommended approach uses `/task --divide TASK_NUMBER [optional prompt]` syntax, analyzes the parent task description for natural divisions (1-5 subtasks), allocates task numbers sequentially via state.json next_project_number, creates subtasks atomically via loop delegation to status-sync-manager with rollback on failure, and updates the parent task dependencies to link subtasks.

The implementation is estimated at 12-17 hours across 5 phases: argument parsing (2-3h), task analysis (3-4h), atomic subtask creation (3-4h), dependency management (2-3h), and git integration/testing (2-3h). The feature is medium-risk due to rollback complexity and task analysis accuracy, but mitigations are well-defined.

**Next Steps**:
1. Create implementation plan based on this research
2. Implement argument parsing and validation
3. Implement task analysis and division logic
4. Implement atomic subtask creation with rollback
5. Implement dependency management
6. Add tests and documentation
