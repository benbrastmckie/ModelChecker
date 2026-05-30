---
name: skill-nix-implementation
description: Implement Nix configuration changes from plans. Invoke for nix implementation tasks.
allowed-tools: Agent, Bash, Edit, Read, Write
---

# Nix Implementation Skill

Thin wrapper that delegates Nix configuration implementation to `nix-implementation-agent` subagent.

## Trigger Conditions

This skill activates when:
- Task type is "nix"
- /implement command targets a Nix task
- NixOS modules, Home Manager configs, or flake changes need to be created using Nix

## Execution Flow

### Stage 1: Input Validation
Validate task_number exists, task_type is "nix", and an implementation plan is present.

### Stage 2: Preflight Status Update
Update status to "implementing" BEFORE invoking subagent.

### Stage 3: Prepare Delegation Context

Domain-specific context for the nix-implementation-agent:
- Nix style guide from `.claude/extensions/nix/context/`
- MCP-NixOS for package/option validation (when available)
- Verification: `nix flake check`, `nixos-rebuild build --flake .#hostname`

```json
{
  "session_id": "sess_{timestamp}_{random}",
  "delegation_depth": 1,
  "delegation_path": ["orchestrator", "implement", "skill-nix-implementation"],
  "timeout": 7200,
  "task_context": {
    "task_number": N,
    "task_name": "{project_name}",
    "description": "{description}",
    "task_type": "nix"
  },
  "plan_path": "specs/{NNN}_{SLUG}/plans/MM_{short-slug}.md",
  "metadata_file_path": "specs/{NNN}_{SLUG}/.return-meta.json"
}
```

### Stage 4: Invoke Subagent
Use Agent tool with subagent_type: "nix-implementation-agent".

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
Add artifact to state.json with summary. Update TODO.md per `@.claude/context/patterns/artifact-linking-todo.md` with `field_name=**Summary**`, `next_field=**Description**`.

### Stage 8: Git Commit
Commit changes with session ID.

### Stage 9: Return Brief Summary

## MUST NOT (Postflight Boundary)

After the agent returns, this skill MUST NOT:

1. **Edit .nix files** - All Nix config work is done by agent
2. **Run nix flake check** - Verification is done by agent
3. **Analyze or grep source** - Analysis is agent work
4. **Write summary/reports** - Artifact creation is agent work

> **PROHIBITION**: If the subagent returned partial or failed status, the lead skill MUST NOT attempt to continue, complete, or "fill in" the subagent's work. Report the partial/failed status and let the user re-run `/implement` to resume.

The postflight phase is LIMITED TO:
- Reading agent metadata file
- Updating state.json via jq
- Updating TODO.md status marker via Edit
- Linking artifacts in state.json
- Git commit
- Cleanup of temp/marker files

Reference: @.claude/context/standards/postflight-tool-restrictions.md

## Return Format

Brief text summary (NOT JSON).
