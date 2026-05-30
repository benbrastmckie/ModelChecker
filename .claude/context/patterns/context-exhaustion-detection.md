# Context Exhaustion Detection Pattern

**Created**: 2026-05-04
**Purpose**: Provide agents with heuristics to self-monitor context pressure and trigger handoffs before hitting limits
**Audience**: Agent developers, skill implementers
**Related**: `subagent-continuation-loop.md`, `handoff-artifact.md`, `progress-file.md`

---

## Overview

Context exhaustion is an **expected event**, not a failure. Agents should monitor their own context usage and proactively write handoff artifacts before reaching critical limits. This pattern provides concrete heuristics for detecting context pressure and deciding when to hand off.

**Design Principle**: Plan FOR context exhaustion, not against it. Handoffs are normal boundaries in long-running tasks.

---

## Detection Signals

Agents should monitor for these signals of context pressure:

### 1. Tool Call Volume

**Threshold**: After every 10 tool calls, assess remaining capacity.

**Hard limit**: If tool calls exceed ~50 and the current phase is not nearly complete, proactively write a handoff.

**Rationale**: Each Read/Write/Edit/Bash tool call consumes context. 50+ calls typically indicates significant context accumulation, especially when file contents are large.

### 2. Re-Read Detection

**Signal**: Finding yourself re-reading files you already read earlier in the session.

**Interpretation**: This is a strong signal of context pressure. When earlier reads have been evicted from context, the agent must re-read, creating a feedback loop that accelerates exhaustion.

**Action**: Before re-reading a file for the second time, consider writing a handoff instead.

### 3. Pre-Operation Risk Assessment

**Rule**: Before starting any operation that reads 3+ files simultaneously, check if a handoff would be safer.

**Example**: If you're about to grep + read 5 source files to understand a cross-cutting concern, and you're already 30+ tool calls into the session, write a handoff first.

### 4. Phase Boundary Check

**Rule**: When completing a phase or objective, evaluate whether to start the next phase or hand off.

**Guideline**:
- If current phase took >30 tool calls, hand off before starting the next phase
- If <20 tool calls remain before the estimated limit, hand off immediately
- Natural phase boundaries are the safest handoff points

---

## Handoff Trigger Thresholds

| Context Used | Tool Calls | Recommended Action |
|--------------|------------|-------------------|
| <30% | <15 | Continue normally |
| 30-50% | 15-30 | Monitor closely, prepare for handoff |
| 50-70% | 30-45 | Hand off at next natural boundary (phase end, objective complete) |
| 70-80% | 45-50 | Hand off immediately — do not start new operations |
| >80% | >50 | Write emergency handoff with minimal context, return partial |

**Note**: These are heuristics, not exact measurements. Different models and contexts have different effective limits. The agent should err on the side of caution.

---

## Handoff Writing Protocol

When context pressure triggers a handoff:

### 1. Update Progress File FIRST

Before writing anything else, update the progress file to reflect exact current state:

```json
{
  "phase": 3,
  "phase_name": "Implement validation framework",
  "last_updated": "2026-05-04T12:00:00Z",
  "objectives": [
    {"id": 1, "description": "Define types", "status": "done"},
    {"id": 2, "description": "Implement validators", "status": "in_progress", "note": "2 of 5 done"}
  ],
  "current_objective": 2,
  "handoff_count": 1
}
```

### 2. Write Handoff Artifact

Follow the template from `handoff-artifact.md`:

```markdown
# Phase 3 Handoff - 20260504T120000Z

## Immediate Next Action
Implement the date validator in validators/date.lua, following the pattern established by string and number validators.

## Current State
- **File**: /home/user/project/src/validators/date.lua
- **Location**: Line 1, new file
- **Work state**: String and number validators complete; need date, URL, and custom type validators

## Key Decisions Made
1. Use table-based registry: Allows runtime extension without modifying core code
2. Return `(valid, error_message)` tuple: Consistent with Lua error handling patterns

## What NOT to Try
1. Schema-based validation: Overkill for current type set

## Critical Context (max 5 items)
- Registry is at `/src/validators/init.lua`
- Each validator must register itself via `register(name, fn)`
- Error messages should include field name for debugging

## References (read only if stuck)
- Plan: specs/259_configure_feature/plans/02_implementation-plan.md, Phase 3
- Progress: specs/259_configure_feature/progress/phase-3-progress.json
```

### 3. Increment Handoff Count

Update `handoff_count` in the progress file to track how many times this phase has been handed off.

### 4. Return Partial with Handoff Path

Write metadata with:

```json
{
  "status": "partial",
  "partial_progress": {
    "stage": "context_exhaustion_handoff",
    "details": "Handoff written for successor. See handoff artifact for current state.",
    "handoff_path": "specs/259_configure_feature/handoffs/phase-3-handoff-20260504T120000Z.md",
    "phases_completed": 2,
    "phases_total": 5
  },
  "artifacts": [
    {
      "type": "handoff",
      "path": "specs/259_configure_feature/handoffs/phase-3-handoff-20260504T120000Z.md",
      "summary": "Context exhaustion handoff for phase 3 with state and approach constraints"
    }
  ]
}
```

---

## Anti-Patterns

### Do NOT

1. **Push to the absolute limit** — Writing a handoff requires ~5-10 tool calls. Leave margin for this.
2. **Write vague handoffs** — "Continue working on the feature" is useless. Be specific about the next action.
3. **Skip the progress file update** — The progress file is the successor's primary resume point.
4. **Include full file contents in handoffs** — Handoffs must be one screen (~40 lines). Reference files, don't inline them.
5. **Hand off mid-edit** — Complete the current file operation before handing off. A handoff in the middle of an incomplete edit creates confusion.

### DO

1. **Hand off at natural boundaries** — Phase ends, objective completions, test passes
2. **Write handoffs before risky operations** — Large refactors, multi-file changes, new dependencies
3. **Keep handoffs concrete** — Specific file paths, line numbers, function names
4. **Document failed approaches** — Save successors from retrying dead ends
5. **Update progress file first** — Always ensure progress reflects reality before handing off

---

## Model-Specific Considerations

| Model | Typical Tool Call Limit | Recommended Handoff Threshold |
|-------|------------------------|------------------------------|
| Claude Haiku | ~30 | 20 tool calls |
| Claude Sonnet | ~50 | 35 tool calls |
| Claude Opus | ~60 | 45 tool calls |

**Note**: These are approximate guidelines. Actual limits depend on:
- File sizes being read
- Complexity of operations
- Amount of generated content
- Concurrent context from system prompts

Agents should use the heuristics (re-read detection, operation risk) in addition to raw tool call counts.

---

## Successor Context Minimization

When a successor starts from a handoff, it should NOT:
- Re-read the full plan unless the handoff explicitly says to
- Re-discover context that the handoff already captures
- Re-try approaches listed in "What NOT to Try"

The successor SHOULD:
- Read the handoff artifact first
- Read the progress file second
- Resume from the indicated objective
- Consult references only if stuck

---

## Related Documentation

- [Subagent Continuation Loop](subagent-continuation-loop.md) - Skill-level loop that consumes handoffs
- [Handoff Artifact Schema](../formats/handoff-artifact.md) - Handoff document template and schema
- [Progress File Schema](../formats/progress-file.md) - Progress tracking format
- [Return Metadata Format](../formats/return-metadata-file.md) - Metadata with `handoff_path` and `partial_progress`
