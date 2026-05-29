---
name: skill-nix-research
description: Conduct Nix/NixOS/Home Manager research using MCP-NixOS, web docs, and codebase exploration. Invoke for nix research tasks.
allowed-tools: Agent, Bash, Edit, Read, Write
---

# Nix Research Skill

Thin wrapper that delegates Nix research to `nix-research-agent` subagent.

## Trigger Conditions

This skill activates when:
- Task type is "nix"
- Research is needed for Nix, NixOS, or Home Manager configuration
- Package definitions or module patterns need to be gathered

## Execution Flow

### Stage 1: Input Validation
Validate task_number exists and task_type is "nix".

### Stage 2: Preflight Status Update
Update status to "researching" BEFORE invoking subagent.

### Stage 3: Prepare Delegation Context

Domain-specific context for the nix-research-agent:
- MCP-NixOS tools for package/option lookup (when available)
- NixOS module patterns from `.claude/extensions/nix/context/`
- Local .nix files (flake.nix, home.nix, modules/)

```json
{
  "session_id": "sess_{timestamp}_{random}",
  "delegation_depth": 1,
  "delegation_path": ["orchestrator", "research", "skill-nix-research"],
  "timeout": 3600,
  "task_context": {
    "task_number": N,
    "task_name": "{project_name}",
    "description": "{description}",
    "task_type": "nix"
  },
  "focus_prompt": "{optional focus}",
  "metadata_file_path": "specs/{NNN}_{SLUG}/.return-meta.json"
}
```

### Stage 4: Invoke Subagent
Use Agent tool with subagent_type: "nix-research-agent".

### Stage 4b: Self-Execution Fallback

**CRITICAL**: If you performed the work above WITHOUT using the Agent tool (i.e., you read files,
wrote artifacts, or updated metadata directly instead of spawning a subagent), you MUST write a
`.return-meta.json` file now before proceeding to postflight. Use the schema from
`return-metadata-file.md` with the appropriate status value for this operation.

If you DID use the Agent tool, skip this stage -- the subagent already wrote the metadata.

## Postflight (ALWAYS EXECUTE)

The following stages MUST execute after work is complete, whether the work was done by a
subagent or inline (Stage 4b). Do NOT skip these stages for any reason.

### Stage 5: Parse Subagent Return
Read the metadata file from `specs/{N}_{SLUG}/.return-meta.json`.

### Stage 6: Update Task Status (Postflight)
Update state.json and TODO.md based on result.

### Stage 7: Link Artifacts
Add research artifact to state.json. Update TODO.md per `@.claude/context/patterns/artifact-linking-todo.md` with `field_name=**Research**`, `next_field=**Plan**`.

### Stage 8: Git Commit
Commit changes with session ID.

### Stage 9: Return Brief Summary

## Return Format

Brief text summary (NOT JSON).
