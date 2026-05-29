# Unified Workflow Architecture Specification

**Status**: Current architecture — designed by Task 592, implemented by Tasks 593-599.
Complements `system-overview.md` which provides a higher-level overview.

**Last Updated**: 2026-05-22
**Designed by**: Task 592 (design_unified_workflow_architecture)
**Implements**: Tasks 593-599

> **See Also**: `system-overview.md` (current architecture), `orchestrate-state-machine.md`,
> `dispatch-agent-spec.md`, `handoff-schema.md`, `extension-system.md`

---

## Overview

The unified workflow refactor addresses seven cross-cutting concerns identified by task 591 team
research and designed in task 592. Each concern is implemented by a dedicated task (593-599) following
an intentional dependency ordering that minimizes rework.

**Pre-refactor pain points** (resolved by tasks 593-599):
- ~525 lines of duplicated arg parsing and gate logic across 3 commands
- ~210 lines of duplicated lifecycle stages across 3 core skills
- No autonomous orchestration loop (manual `/research` → `/plan` → `/implement` sequence)
- Fork-vs-subagent decision logic scattered (or absent)
- Extensions copy full skill lifecycle instead of hooking into it
- Nested continuation loops create inconsistent orchestrator state views

**Current system** (post-refactor):
- Commands are ~150-200 line routing-only controllers
- Skills are ~130-200 line unique-logic wrappers
- `/orchestrate` provides fire-and-forget autonomous lifecycle management
- `dispatch_agent()` centralizes fork-vs-subagent logic
- Extension hooks replace full lifecycle copying

---

## Dependency Ordering

| Wave | Tasks | Blocked by |
|------|-------|------------|
| 1 | 593 (shared utilities) | — |
| 2 | 598 (context budgets) | 593 |
| 3 | 594 (skill base) | 598 |
| 4 | 595 (refactor commands), 596 (/orchestrate) | 594 |
| 5 | 597 (task/revise/todo/review) | 595 |
| 6 | 599 (extensions + docs) | all |

See Appendix A for the full dependency graph.

---

## Component 1: Shared Command Infrastructure

**Implemented by**: Task 593
**File locations**:
```
.claude/scripts/
├── parse-command-args.sh        # NEW: parse task numbers + flags
├── command-gate-in.sh           # NEW: session_id gen + task lookup + validation
├── command-gate-out.sh          # NEW: artifact verification + defensive status fix
├── update-task-status.sh        # EXISTING (unchanged)
└── validate-artifact.sh         # EXISTING (unchanged)
```

### `parse-command-args.sh`

**Purpose**: Parse `$ARGUMENTS` string → task number list + remaining flags + focus prompt.

**Signature**:
```bash
# Usage: source .claude/scripts/parse-command-args.sh "$ARGUMENTS"
# Exports:
#   TASK_NUMBERS    - space-separated list of integers
#   REMAINING_ARGS  - string of remaining args after task numbers
#   TEAM_MODE       - "true" or "false"
#   TEAM_SIZE       - integer 2-4
#   EFFORT_FLAG     - "fast", "hard", or ""
#   MODEL_FLAG      - "haiku", "sonnet", "opus", or ""
#   CLEAN_FLAG      - "true" or "false"
#   FORCE_FLAG      - "true" or "false"  (implement only)
#   FOCUS_PROMPT    - remaining text after all flags removed
```

**Algorithm**:
1. Regex-match leading `[0-9][0-9,\ \-]*` to extract `task_spec`.
2. Expand ranges: `22-24` → `22 23 24`.
3. Scan `remaining_args` for known flags, setting export vars.
4. Strip all recognized flags from `remaining_args` → `FOCUS_PROMPT`.
5. Exit 1 with message if no task numbers found.

### `command-gate-in.sh`

**Purpose**: CHECKPOINT 1 logic — session ID generation, task lookup, terminal status guard.

**Signature**:
```bash
# Usage: source .claude/scripts/command-gate-in.sh "$task_number" "$operation"
# operation: "research" | "plan" | "implement" | "revise"
# Exports:
#   SESSION_ID     - sess_{timestamp}_{random}
#   TASK_TYPE      - from state.json
#   TASK_STATUS    - from state.json
#   PROJECT_NAME   - from state.json
#   DESCRIPTION    - from state.json
#   PADDED_NUM     - printf "%03d" task_number
# Exit 1 if task not found or terminal status
```

**Key behaviors**:
- Generates `SESSION_ID` using `sess_$(date +%s)_$(od -An -N3 -tx1 /dev/urandom | tr -d ' ')`
- Checks terminal statuses (completed, abandoned, expanded) → ABORT
- Displays `[{operation_label}] Task {N}: {project_name}`

### `command-gate-out.sh`

**Purpose**: CHECKPOINT 2 logic — artifact verification and defensive status correction.

**Signature**:
```bash
# Usage: source .claude/scripts/command-gate-out.sh "$task_number" "$operation" "$session_id"
# Reads skill return from: specs/{NNN}_{SLUG}/.return-meta.json
# Applies defensive correction if state.json status stale
# Exit 1 on critical validation failure (non-blocking on artifact link failure)
```

### What Stays in Each Command File

After extraction, each command retains only:
1. YAML frontmatter (allowed-tools, argument-hint, model)
2. Anti-bypass constraint (PROHIBITION section)
3. Source + dispatch block (~30 lines)
4. Multi-task batch loop (~40 lines)
5. Extension routing table (research.md) or single-skill routing (plan.md)
6. Error handling section

**Target size**: 150-200 lines per command (vs. 500 today).

**Savings**: ~525 lines eliminated across 3 commands.

---

## Component 2: Shared Skill Base Pattern

**Implemented by**: Task 594 (depends on Task 598 for context budget constraints)
**File locations**:
```
.claude/scripts/
├── skill-base.sh                # NEW: shared skill lifecycle stages
└── postflight-workflow.sh       # NEW: shared postflight helper
```

### Architecture Decision

Use a **sourced shell script library** (`skill-base.sh`) rather than a context document. Skills need
to execute shell commands (jq, file operations), not just read reference text.

The skill body after refactoring:
```
[Frontmatter]
# Skill description (30 lines)
# Skill-specific context collection (Stage 4 variants, ~80 lines)
# Stage 5: Subagent invocation (unique subagent_type, ~30 lines)
# Source skill-base.sh for shared postflight
```

### `skill-base.sh` — Function Inventory

```bash
# skill_validate_input "$task_number"
# → jq lookup in state.json; exports TASK_DATA, TASK_TYPE, TASK_STATUS, etc.
# → exit 1 if task not found

# skill_preflight_update "$task_number" "$operation" "$session_id"
# → calls update-task-status.sh preflight

# skill_create_postflight_marker "$padded_num" "$project_name" "$session_id" "$skill_name" "$operation"
# → writes .postflight-pending file

# skill_read_artifact_number "$task_number" "$padded_num" "$project_name"
# → reads next_artifact_number from state.json or falls back to directory scan
# → exports ARTIFACT_NUMBER, ARTIFACT_PADDED

# skill_read_metadata "$padded_num" "$project_name"
# → reads .return-meta.json
# → exports SUBAGENT_STATUS, ARTIFACT_PATH, ARTIFACT_TYPE, ARTIFACT_SUMMARY, MEMORY_CANDIDATES

# skill_validate_artifact "$status" "$artifact_path"
# → calls validate-artifact.sh --fix (non-blocking)

# skill_postflight_update "$task_number" "$operation" "$session_id" "$status"
# → calls update-task-status.sh postflight (only on success status)

# skill_increment_artifact_number "$task_number"
# → jq increment next_artifact_number in state.json
# → research only (planner/implementer skip this)

# skill_propagate_memory_candidates "$task_number" "$memory_candidates"
# → append to state.json entry (append semantics)

# skill_link_artifacts "$task_number" "$artifact_path"
# → jq state.json update + link-artifact-todo.sh

# skill_cleanup "$padded_num" "$project_name"
# → rm -f .postflight-pending .postflight-loop-guard .return-meta.json
```

### Hook Points for Skill-Specific Logic

Each skill provides exactly:
1. **Context collection** (Stage 4 variants): unique per skill
2. **Delegation context construction**: unique fields per skill
3. **Agent invocation** (Stage 5): unique `subagent_type` per skill
4. **Continuation loop** (skill-implementer only): see Component 7

Everything else sources from `skill-base.sh`.

### Target Skill Sizes

| Skill | Current | Target | Lines Eliminated |
|-------|---------|--------|-----------------|
| skill-researcher | 558 | 150 | 408 |
| skill-planner | ~450 | 130 | 320 |
| skill-implementer | ~600 | 200 | 400 |

**Total savings**: ~210 lines (unique lifecycle logic stays, duplication is removed).

---

## Component 3: /orchestrate State Machine

**Implemented by**: Task 596
**File locations**:
```
.claude/commands/orchestrate.md    # NEW: entry point, argument parsing
.claude/skills/skill-orchestrate/
└── SKILL.md                       # NEW: state machine + dispatch logic (~200 lines)
```

### Architecture Decision

`/orchestrate` is fire-and-forget (autonomous loop by default). No confirmation gates between phases.
Blocker escalation is the safety mechanism. The state machine is simple enough to live in the skill
body (Pattern C: Orchestrator/Routing skill) — no dedicated agent needed.

### State Machine Summary

| State | Action | Next State |
|-------|--------|------------|
| not_started | dispatch(research) | researched (via handoff) |
| researched | dispatch(plan) | planned (via handoff) |
| planned | dispatch(implement, orchestrator_mode=true) | implemented OR partial+continue |
| implementing | dispatch(implement, orchestrator_mode=true) — resume | same as planned |
| partial + handoff | read handoff, re-dispatch implement | implementing |
| partial + blockers | fork(research_blocker) → revise → implement | implementing |
| partial + no handoff + MAX_CYCLES | report, exit | — |
| blocked | research_fork → revise → implement | implementing |
| completed/abandoned | report, exit | — (terminal) |

See `orchestrate-state-machine.md` for the complete state table, transition diagram, and
blocker escalation 5-step sequence.

### Key Properties

- **Context flatness**: Orchestrator reads only the 400-token `.orchestrator-handoff.json` after each
  dispatch. Never inlines full agent output into orchestrator context.
- **MAX_CYCLES = 5** per invocation. Left in `partial` with user notification on limit.
- **Loop guard**: `specs/{NNN}_{SLUG}/.orchestrator-loop-guard` (see `orchestrate-state-machine.md`
  for schema).

---

## Component 4: dispatch_agent() Function

**Implemented by**: Task 596
**File location**: `.claude/scripts/dispatch-agent.sh`

### Full Function Signature

```bash
# dispatch_agent() — encapsulates fork-vs-named-subagent decision
#
# Usage:
#   dispatch_agent "$agent_type" "$prompt" "$context_json" "$is_blocker_escalation"
#
# Parameters:
#   agent_type              - Named agent (e.g. "general-research-agent"), or "" for fork
#   prompt                  - Full prompt string to pass to Agent tool
#   context_json            - Delegation context JSON string
#   is_blocker_escalation   - "true" | "false"
#     "true": omit subagent_type (fork path)
#     "false": use agent_type as subagent_type (named subagent path)
#
# Internal decision:
#   IF is_blocker_escalation == "true":
#     → Agent tool call WITHOUT subagent_type
#     → FORK_SUBAGENT=1 applies (if env var set)
#     → parent cache prefix inherited (~90% token reduction)
#   ELSE:
#     → Agent tool call WITH subagent_type="$agent_type"
#     → Fresh context, full cost
#
# Returns:
#   Writes handoff to: specs/{NNN}_{SLUG}/.orchestrator-handoff.json
#   Exit code 0 on success, 1 on agent failure
```

### Decision Rationale

`is_blocker_escalation` is a **semantic signal** (not a TTL heuristic). The orchestrator always
knows why it is dispatching:
- **Blocker escalation**: Same session, guaranteed warm cache, no named agent needed → fork
- **State transition**: Crosses conversation boundaries, guaranteed cold → named subagent

This eliminates fragile cache TTL measurement.

See `dispatch-agent-spec.md` for full specification and future-proofing notes.

---

## Component 5: Structured Handoff Object

**Implemented by**: Task 596 (orchestrator handoff); existing continuation handoffs unchanged
**File**: `specs/{NNN}_{SLUG}/.orchestrator-handoff.json` (written by skills; read by orchestrator)

### Two Distinct Handoff Types

| Type | File | Format | Written by | Read by |
|------|------|--------|------------|---------|
| Orchestrator handoff | `.orchestrator-handoff.json` | JSON, ~400 tokens | Skills (when orchestrator_mode=true) | skill-orchestrate |
| Continuation handoff | `handoffs/phase-N-handoff-TIMESTAMP.md` | Markdown | Agents (context exhaustion) | Successor agents |

### Orchestrator Handoff JSON Schema (Overview)

```json
{
  "$schema": "orchestrator-handoff-v1",
  "phase": "research | plan | implement | revise",
  "status": "researched | planned | implemented | partial | failed | blocked",
  "summary": "2-4 sentence description of what was accomplished",
  "artifacts": [{"type": "report | plan | summary", "path": "specs/NNN_slug/type/file.md"}],
  "blockers": [{"description": "...", "phase": "...", "severity": "hard | soft"}],
  "next_action_hint": "plan | implement | revise | none",
  "files_modified": ["..."],
  "decisions_made": ["..."],
  "dead_ends": ["..."],
  "continuation_context": {
    "handoff_path": "path to continuation handoff (partial only)",
    "phases_completed": 2,
    "phases_total": 4
  }
}
```

**Token budget**: Full handoff must stay under 400 tokens. `summary` constrained to ~4 sentences.

See `handoff-schema.md` for complete field definitions, writing contract, reading contract, and
example handoff objects.

### orchestrator_mode Detection

Skills write the orchestrator handoff ONLY when `"orchestrator_mode": true` appears in their
delegation context. In normal `/research`, `/plan`, `/implement` invocations this file is not written.

---

## Component 6: Extension Lifecycle Hooks

**Implemented by**: Task 599
**Schema location**: `manifest.json` `hooks` object (in each extension directory)

### manifest.json Schema Additions

```json
{
  "name": "nix",
  "version": "1.0.0",
  "hooks": {
    "preflight": "scripts/nix-preflight.sh",
    "context_injection": "scripts/nix-context.sh",
    "postflight": "scripts/nix-postflight.sh",
    "verification": "scripts/nix-verify.sh"
  }
}
```

All hook fields are optional. Absent hooks are silently skipped.

### Hook Execution Contract

```bash
# Each hook receives positional arguments:
# $1 = task_number (integer)
# $2 = task_type (string, e.g. "nix")
# $3 = task_dir (path, e.g. "specs/242_configure_nixos")
# $4 = session_id (string)
# $5 = operation (string: "research" | "plan" | "implement")
```

Hooks MUST: exit 0 on success, exit 1 on fatal failure (skill aborts), write to stdout for logging,
NOT modify state.json directly.

Hooks MAY: write files to `$task_dir/` for context injection, set environment variables.

Hooks are called with `set -e` disabled (non-fatal). Failures are logged but do not block skill
completion.

### Hook Invocation Points in `skill-base.sh`

| Stage | Function | Hook Called |
|-------|----------|------------|
| Stage 2 | `skill_preflight_update()` | `hooks.preflight` |
| Stage 4 | `skill_prepare_delegation()` | `hooks.context_injection` |
| Stage 6a | `skill_validate_artifact()` | `hooks.verification` |
| Stage 7 | `skill_postflight_update()` | `hooks.postflight` |

### Extension Skill After Hook Integration

Target extension skill size: **30-50 lines** (vs. 400-600 lines today). The skill body becomes:
1. Frontmatter
2. Stage 4: Call `hooks.context_injection` to gather domain-specific context
3. Stage 5: Invoke subagent with domain-specific `subagent_type`
4. Source `skill-base.sh` for all other stages

---

## Component 7: Nested Loop Resolution

**Implemented by**: Task 596 (orchestrator) + Task 594 (skill-implementer flag)

### Architecture Decision

**Exclusive alternatives**: When `/orchestrate` dispatches skill-implementer, it passes
`"orchestrator_mode": true` in the delegation context. Skill-implementer detects this flag and
**disables its inner continuation loop** (`max_continuations = 0`). The outer orchestrator loop
handles all continuation at the phase level.

Layered loops (inner + outer) are unreliable: the inner loop could run 3 continuation cycles and
return "implemented", while the orchestrator's state view would be inconsistent.

### Implementation

**In skill-implementer** (Stage 5c — loop guard init):
```bash
# Read orchestrator_mode from delegation context
orchestrator_mode=$(echo "$delegation_context" | jq -r '.orchestrator_mode // "false"')

if [ "$orchestrator_mode" = "true" ]; then
  max_continuations=0  # Disable inner loop; orchestrator drives
else
  max_continuations=3  # Normal inner loop behavior
fi
```

### Flag Propagation Pattern

The `orchestrator_mode` flag MUST be preserved across continuation chains:
```json
{
  "continuation_context": {
    "is_successor": true,
    "continuation_number": 1,
    "handoff_path": "...",
    "orchestrator_mode": true
  }
}
```

---

## Cross-Cutting Concern: Context Budget Architecture

**Note**: Full design belongs to Task 598. This section states constraints for tasks 593-597.

### Four-Tier Loading Model

| Tier | Loaded When | Budget | Content |
|------|-------------|--------|---------|
| 1 (always) | Every invocation | ~500 lines | Anti-stop patterns, return-metadata, checkpoint-execution |
| 2 (command) | On command entry | ~500 lines | Routing tables, argument docs, anti-bypass |
| 3 (agent) | At agent spawn | ~3-5K lines | Full workflow patterns, domain context |
| 4 (on-demand) | Via `@`-ref in agent | Unbounded | Detailed guides, templates, examples |

### Critical Constraints for Tasks 593-597

- Commands MUST NOT load Tier 3 context (agent-level context stays with agents)
- Current research.md, plan.md, implement.md embed agent-level context inline → must move to Tier 3
- Command files: ≤ 200 lines after Task 593 extraction
- Skill files: ≤ 200 lines after Task 594 extraction

### Budget Caps (Task 598 to enforce)

| Agent Type | Context Budget |
|------------|---------------|
| Sonnet workers | ≤ 8K tokens |
| Opus planners | ≤ 15K tokens |
| Haiku utilities | ≤ 2K tokens |

---

## Appendix A: Dependency Graph

```
592 (this task: design) ─────────────────────┐
                                              │
593 (shared utilities) ──────────────────────┤
  └─ extracts: parse-command-args.sh          │
               command-gate-in.sh             │
               command-gate-out.sh            │
               postflight-workflow.sh         │
                              │               │
                              ▼               │
598 (progressive disclosure) ◄───────────────┘
  └─ establishes: context budgets per tier
                  context index tier tags
                              │
                              ▼
594 (skill base) ─── depends on 598 budgets ──┐
  └─ extracts: skill-base.sh                  │
                              │               │
          ┌───────────────────┘               │
          ▼                   ▼               │
595 (refactor commands)  596 (/orchestrate)   │
  └─ research/plan/impl   └─ state machine    │
     slim to ~150L            dispatch_agent   │
                              blocker escalation│
                                              │
597 (task/revise/todo/review)                 │
  └─ unrelated to shared base                 │
                              │               │
                              ▼               │
                    599 (extensions) ◄────────┘
                      └─ hooks in manifest.json
                         thin extension skills
```

---

## Appendix B: New File Location Summary

Files to be created across Tasks 593-599:

```
.claude/scripts/
├── parse-command-args.sh         (task 593)
├── command-gate-in.sh            (task 593)
├── command-gate-out.sh           (task 593)
├── postflight-workflow.sh        (task 593)
├── skill-base.sh                 (task 594)
└── dispatch-agent.sh             (task 596)

.claude/commands/
└── orchestrate.md                (task 596)

.claude/skills/skill-orchestrate/
└── SKILL.md                      (task 596)

.claude/context/formats/
└── orchestrator-handoff.md       (task 596)

.claude/context/patterns/
└── orchestrator-mode.md          (task 596)
```

---

## Appendix C: Duplication Baseline

**Command-level duplication** (confirmed identical across research.md, plan.md, implement.md):

| Duplicated Block | Lines per command | Total waste |
|------------------|-------------------|-------------|
| `parse_task_args()` function | ~30 | ~90 lines |
| Flag parsing (STAGE 1.5) | ~50 | ~150 lines |
| Batch validation loop | ~25 | ~75 lines |
| CHECKPOINT 1 (GATE IN) lookup+validate | ~30 | ~90 lines |
| CHECKPOINT 2 (GATE OUT) defensive checks | ~25 | ~75 lines |
| CHECKPOINT 3 COMMIT | ~15 | ~45 lines |

**Total command duplication: ~525 lines** (each command ~500 lines; now ~150-200 lines each).

**Skill-level duplication** (near-identical across skill-researcher, skill-planner, skill-implementer):

| Duplicated Block | Lines per skill |
|------------------|-----------------|
| Stage 1: Input validation | ~25 |
| Stage 2: Preflight status update | ~15 |
| Stage 3: Postflight marker creation | ~20 |
| Stage 3a: Artifact number read | ~15 |
| Stage 6: Read metadata file | ~20 |
| Stage 6a: Validate artifact | ~15 |
| Stage 7: Update status | ~15 |
| Stage 7a: Memory candidates propagation | ~20 |
| Stage 8: Link artifacts | ~35 |
| Stage 9: Cleanup | ~10 |
| Stage 10: Return brief summary | ~15 |

**Total skill duplication: ~210 lines** (each skill ~500-560 lines; now ~130-200 lines each).
