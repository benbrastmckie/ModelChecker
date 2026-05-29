# Orchestrator Handoff JSON Schema

**Status**: Current architecture — designed by Task 592, implemented by Task 596.

**File location**: `specs/{NNN}_{SLUG}/.orchestrator-handoff.json` (runtime; not checked in)
**Written by**: Skills when `orchestrator_mode: true` in delegation context
**Read by**: `skill-orchestrate` state machine loop

**See Also**: `architecture-spec.md` (Component 5), `orchestrate-state-machine.md`,
`dispatch-agent-spec.md`

---

## Two Distinct Handoff Types

This document covers only the **orchestrator handoff**. Do not confuse with continuation handoffs:

| Type | File | Format | Written by | Read by | Purpose |
|------|------|--------|------------|---------|---------|
| **Orchestrator handoff** | `.orchestrator-handoff.json` | JSON, ≤400 tokens | Skills (orchestrator_mode) | skill-orchestrate | State machine dispatch decisions |
| Continuation handoff | `handoffs/phase-N-handoff-TIMESTAMP.md` | Markdown | Agents (context exhaustion) | Successor agents | Resume after context exhaustion |

These serve different consumers and MUST NOT be conflated. The orchestrator reads structured JSON;
the successor agent reads markdown prose.

---

## Complete JSON Schema

```json
{
  "$schema": "orchestrator-handoff-v1",

  "phase": "research | plan | implement | revise",

  "status": "researched | planned | implemented | partial | failed | blocked",

  "summary": "2-4 sentence description of what was accomplished. Must be concise — this field has a ~100 token budget. Include: what was done, key outcome, any caveats.",

  "artifacts": [
    {
      "type": "report | plan | summary",
      "path": "specs/NNN_slug/type/file.md"
    }
  ],

  "blockers": [
    {
      "description": "What is blocking implementation — be specific enough that a research fork can investigate this without additional context",
      "phase": "phase-N (where blocker was detected)",
      "severity": "hard | soft"
    }
  ],

  "next_action_hint": "plan | implement | revise | none",

  "files_modified": [
    "list of modified file paths (relative to repo root)"
  ],

  "decisions_made": [
    "Key decision 1 (one sentence each)",
    "Key decision 2"
  ],

  "dead_ends": [
    "Approach tried but failed — so the orchestrator does not retry it"
  ],

  "continuation_context": {
    "handoff_path": "specs/NNN_slug/handoffs/phase-N-handoff-TIMESTAMP.md",
    "phases_completed": 2,
    "phases_total": 4
  }
}
```

---

## Field Definitions

### `phase` (required)
Which lifecycle phase just completed.
- `"research"`: `/research` skill completed
- `"plan"`: `/plan` skill completed
- `"implement"`: `/implement` skill completed (full or partial)
- `"revise"`: `/revise` skill completed

### `status` (required)
Outcome of this dispatch cycle.
- `"researched"`: Research complete, report written
- `"planned"`: Plan written, ready for implementation
- `"implemented"`: All plan phases complete
- `"partial"`: Incomplete — see `continuation_context` or `blockers`
- `"failed"`: Non-recoverable failure — implementation cannot continue
- `"blocked"`: Hard blockers prevent progress — escalation required

### `summary` (required)
2-4 sentences describing what was accomplished. **Token budget: ~100 tokens**. Be concise.
The orchestrator reads this to understand cycle outcome without reading full artifacts.

### `artifacts` (required)
List of artifacts written by this cycle. The orchestrator uses these to populate delegation
context for the next cycle (e.g., plan path for implement dispatch).

### `blockers` (optional)
Non-empty only when `status = "partial"` or `status = "blocked"`. Each blocker entry must
contain enough context for a research fork to investigate without reading full artifacts.

**Severity semantics**:
- `"hard"`: Cannot proceed without resolution. Triggers escalation.
- `"soft"`: Can be worked around. Orchestrator may choose to continue anyway.

### `next_action_hint` (optional)
Suggested next action. The orchestrator's state machine may override this hint. It is advisory only.

### `files_modified` (optional)
Paths of files changed during this cycle. Used by the orchestrator to include in downstream
delegation context (e.g., "the plan was revised to include these changes").

### `decisions_made` (optional)
Key decisions that downstream cycles should be aware of. Prevents downstream agents from
re-investigating already-settled questions.

### `dead_ends` (optional)
Approaches tried but failed. The orchestrator passes these to downstream delegation context
to prevent repetition.

### `continuation_context` (optional, present when `status = "partial"`)
Points to the continuation handoff file written by the agent. The orchestrator reads
`handoff_path` and passes it in the next implement dispatch as `continuation_context`.

**Note**: `continuation_context` and `blockers` can both be present (partial completion with
identified blockers). The orchestrator handles blockers first via escalation.

---

## Token Budget Constraints

The full `.orchestrator-handoff.json` object MUST stay under **400 tokens**. This is the mechanism
that keeps orchestrator context flat across cycles.

Field-level budgets:
| Field | Max Tokens |
|-------|-----------|
| `summary` | ~100 |
| `artifacts` (all entries) | ~50 |
| `blockers` (all entries) | ~100 |
| `decisions_made` (all entries) | ~50 |
| `dead_ends` (all entries) | ~50 |
| `files_modified` (all entries) | ~30 |
| `continuation_context` | ~20 |
| Schema overhead (field names, JSON structure) | ~50 |

If content would exceed 400 tokens, truncate `decisions_made` and `dead_ends` first (these are
advisory). Never truncate `status`, `summary`, or `blockers`.

---

## Writing Contract

### When to Write

Skills MUST write `.orchestrator-handoff.json` when and ONLY when `"orchestrator_mode": true`
appears in the delegation context received from the skill wrapper.

```bash
# In skill SKILL.md, after receiving delegation context:
orchestrator_mode=$(echo "$delegation_context" | jq -r '.orchestrator_mode // "false"')

if [ "$orchestrator_mode" = "true" ]; then
  write_orchestrator_handoff
fi
```

When NOT in orchestrator mode (normal `/research`, `/plan`, `/implement` invocation), skills do
NOT write this file. The file's presence signals orchestrator dispatch.

### File Path

```bash
handoff_path="specs/${padded_num}_${project_name}/.orchestrator-handoff.json"
```

The filename is static (not timestamped). Each dispatch cycle overwrites the previous handoff.

**Exception**: If concurrent `/orchestrate` invocations are possible, include session_id:
```bash
handoff_path="specs/${padded_num}_${project_name}/.orchestrator-handoff-${session_id}.json"
```

The orchestrator reads its own session's file using the same session_id it wrote to the
loop guard.

### When to Write `continuation_context`

Write `continuation_context` only when the skill returns `status = "partial"` AND a continuation
handoff file was written by the agent. The continuation handoff path comes from the agent's
`.return-meta.json` `partial_progress.handoff_path` field.

### `orchestrator_mode` Flag in Continuation Context

When skill-implementer runs in orchestrator_mode and returns partial, it MUST preserve the
`orchestrator_mode` flag in the continuation_context embedded in the orchestrator handoff:

```json
{
  "status": "partial",
  "continuation_context": {
    "handoff_path": "specs/.../handoffs/phase-2-handoff-T.md",
    "phases_completed": 2,
    "phases_total": 4,
    "orchestrator_mode": true
  }
}
```

This ensures the next implement dispatch (via the orchestrator's re-dispatch) still operates
in orchestrator mode and does not re-enable the inner continuation loop.

---

## Reading Contract

The orchestrator reads the handoff after each dispatch:

```bash
handoff_file="specs/${padded_num}_${project_name}/.orchestrator-handoff.json"

# Safety: check file exists before reading
if [ ! -f "$handoff_file" ]; then
  echo "[orchestrate] ERROR: handoff not written by skill (orchestrator_mode not detected?)"
  exit 1
fi

# Read only what the state machine needs — do NOT load full artifacts
handoff=$(cat "$handoff_file")
status=$(echo "$handoff" | jq -r '.status')
blockers=$(echo "$handoff" | jq -c '.blockers // []')
next_hint=$(echo "$handoff" | jq -r '.next_action_hint // "none"')
continuation=$(echo "$handoff" | jq -c '.continuation_context // null')
artifacts=$(echo "$handoff" | jq -c '.artifacts // []')
```

The orchestrator NEVER reads the actual research reports, plan files, or implementation summaries
during its state machine loop. It reads ONLY the 400-token handoff object.

---

## Example Handoff Objects

### Successful Research

```json
{
  "$schema": "orchestrator-handoff-v1",
  "phase": "research",
  "status": "researched",
  "summary": "Researched shared command infrastructure patterns across research.md, plan.md, and implement.md. Found ~525 lines of identical duplication across 3 commands. Identified 3 extraction candidates: parse-command-args.sh, command-gate-in.sh, command-gate-out.sh.",
  "artifacts": [
    {"type": "report", "path": "specs/593_extract_shared_workflow_utilities/reports/01_extraction-research.md"}
  ],
  "blockers": [],
  "next_action_hint": "plan",
  "files_modified": [],
  "decisions_made": [
    "Extraction to .claude/scripts/ is preferred over context documents (scripts can be executed)"
  ],
  "dead_ends": []
}
```

### Successful Implementation

```json
{
  "$schema": "orchestrator-handoff-v1",
  "phase": "implement",
  "status": "implemented",
  "summary": "Implemented all 3 shared command scripts. parse-command-args.sh, command-gate-in.sh, and command-gate-out.sh created. research.md, plan.md, implement.md updated to source shared scripts. All verification tests passed.",
  "artifacts": [
    {"type": "summary", "path": "specs/593_extract_shared_workflow_utilities/summaries/01_extraction-summary.md"}
  ],
  "blockers": [],
  "next_action_hint": "none",
  "files_modified": [
    ".claude/scripts/parse-command-args.sh",
    ".claude/scripts/command-gate-in.sh",
    ".claude/scripts/command-gate-out.sh",
    ".claude/commands/research.md",
    ".claude/commands/plan.md",
    ".claude/commands/implement.md"
  ],
  "decisions_made": [
    "Command files now source shared scripts via 'source .claude/scripts/NAME.sh'",
    "Existing update-task-status.sh and validate-artifact.sh left unchanged"
  ],
  "dead_ends": []
}
```

### Partial with Continuation

```json
{
  "$schema": "orchestrator-handoff-v1",
  "phase": "implement",
  "status": "partial",
  "summary": "Completed phases 1-2 of 4 (parse-command-args.sh and command-gate-in.sh created). Context exhaustion during phase 3. Continuation handoff written at specified path.",
  "artifacts": [
    {"type": "summary", "path": "specs/593_extract_shared_workflow_utilities/summaries/01_extraction-summary.md"}
  ],
  "blockers": [],
  "next_action_hint": "implement",
  "files_modified": [
    ".claude/scripts/parse-command-args.sh",
    ".claude/scripts/command-gate-in.sh"
  ],
  "decisions_made": [
    "parse-command-args.sh exports FOCUS_PROMPT as remaining text after all flags stripped"
  ],
  "dead_ends": [],
  "continuation_context": {
    "handoff_path": "specs/593_extract_shared_workflow_utilities/handoffs/phase-3-handoff-20260522T120000Z.md",
    "phases_completed": 2,
    "phases_total": 4,
    "orchestrator_mode": true
  }
}
```

### Blocked with Escalation Required

```json
{
  "$schema": "orchestrator-handoff-v1",
  "phase": "implement",
  "status": "partial",
  "summary": "Implemented parse-command-args.sh successfully. Blocked at command-gate-in.sh: the current update-task-status.sh script does not export SESSION_ID, which is required by the gate-in design.",
  "artifacts": [],
  "blockers": [
    {
      "description": "update-task-status.sh does not export SESSION_ID; command-gate-in.sh needs to generate SESSION_ID independently or update-task-status.sh needs modification",
      "phase": "phase-2",
      "severity": "hard"
    }
  ],
  "next_action_hint": "revise",
  "files_modified": [".claude/scripts/parse-command-args.sh"],
  "decisions_made": [],
  "dead_ends": [
    "Tried sourcing update-task-status.sh to get SESSION_ID — it does not set this variable"
  ]
}
```

---

## Relationship to Continuation Handoffs

The orchestrator handoff and continuation handoff are written by different components and read by
different consumers:

```
skill-implementer (in orchestrator_mode):
  ├── Writes: handoffs/phase-2-handoff-T.md   (for successor agent)
  └── Writes: .orchestrator-handoff.json      (for skill-orchestrate)
              └── continuation_context.handoff_path = "handoffs/phase-2-handoff-T.md"

skill-orchestrate (next cycle):
  ├── Reads: .orchestrator-handoff.json       (400 tokens)
  │          └── sees continuation_context.handoff_path
  └── Passes: continuation_context to next implement dispatch
              └── successor agent reads: handoffs/phase-2-handoff-T.md
```

The two files are never confused because:
1. They are in different locations (`.orchestrator-handoff.json` vs. `handoffs/*.md`)
2. They use different formats (JSON vs. Markdown)
3. They are read by different components (skill-orchestrate vs. successor agent)
