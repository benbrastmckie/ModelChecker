#!/usr/bin/env bash
# skill-base.sh — Shared skill lifecycle functions
#
# SOURCING SEMANTICS:
#   This file must be sourced within the SAME Bash tool invocation as function calls.
#   Exported variables do NOT persist across separate Bash invocations in Claude Code.
#   Pattern: source this file, then call functions, all within one bash block.
#
#   Example usage in a SKILL.md bash block:
#     source .claude/scripts/skill-base.sh
#     skill_validate_input "$task_number"
#     skill_preflight_update "$task_number" "research" "$session_id"
#
# VARIABLE EXPORTS:
#   skill_validate_input  -> TASK_DATA, TASK_TYPE, TASK_STATUS, PROJECT_NAME, PADDED_NUM, TASK_DIR
#   skill_read_artifact_number -> ARTIFACT_NUMBER, ARTIFACT_PADDED
#   skill_read_metadata   -> SUBAGENT_STATUS, ARTIFACT_PATH, ARTIFACT_TYPE, ARTIFACT_SUMMARY, MEMORY_CANDIDATES
#
# CONTEXT BUDGET DEFAULTS (overridable by task 598 tier enforcement):
#   SKILL_CONTEXT_BUDGET defaults to 8000 (sonnet workers) or 15000 (opus planners).
#   Override before sourcing: SKILL_CONTEXT_BUDGET=15000 source skill-base.sh
SKILL_CONTEXT_BUDGET="${SKILL_CONTEXT_BUDGET:-8000}"

# ─────────────────────────────────────────────────────────────────────────────
# EXTENSION HOOKS: Lifecycle hook invocation for loaded extensions.
#
# Extensions may declare hook scripts in manifest.json under a top-level
# "hooks" object (distinct from "provides.hooks" which are file-copy targets):
#
#   "hooks": {
#     "preflight": "scripts/my-preflight.sh",
#     "context_injection": "scripts/my-context.sh",
#     "verification": "scripts/my-verify.sh",
#     "postflight": "scripts/my-postflight.sh"
#   }
#
# Hook scripts are called with 5 positional args:
#   $1 = task_number   $2 = task_type   $3 = task_dir   $4 = session_id   $5 = operation
#
# Missing hook keys or absent extensions.json are silently skipped.
# ─────────────────────────────────────────────────────────────────────────────

# skill_get_extension_dir: Map task_type to extension directory via extensions.json
# Usage: skill_get_extension_dir "$task_type"
# Outputs: absolute path to extension directory, or empty string if not found
skill_get_extension_dir() {
  local task_type="$1"
  local extensions_json=".claude/extensions.json"
  if [ ! -f "$extensions_json" ]; then
    return 0
  fi
  # Find extension with matching task_type
  local ext_name
  ext_name=$(jq -r --arg tt "$task_type" \
    '.loaded_extensions // [] | .[] | select(.task_type == $tt) | .name' \
    "$extensions_json" 2>/dev/null | head -1)
  if [ -z "$ext_name" ] || [ "$ext_name" = "null" ]; then
    return 0
  fi
  echo ".claude/extensions/${ext_name}"
}

# skill_run_extension_hook: Execute a lifecycle hook for the current task_type
# Usage: skill_run_extension_hook "$hook_name" "$task_number" "$task_type" "$task_dir" "$session_id" "$operation"
# hook_name: preflight | context_injection | verification | postflight
# Silently skips if: extensions.json missing, extension not loaded, hook not declared, script not found
skill_run_extension_hook() {
  local hook_name="$1"
  local task_number="$2"
  local task_type="$3"
  local task_dir="$4"
  local session_id="$5"
  local operation="$6"

  local ext_dir
  ext_dir=$(skill_get_extension_dir "$task_type")
  if [ -z "$ext_dir" ]; then
    return 0
  fi

  local manifest="${ext_dir}/manifest.json"
  if [ ! -f "$manifest" ]; then
    return 0
  fi

  local hook_script
  hook_script=$(jq -r --arg h "$hook_name" '.hooks[$h] // empty' "$manifest" 2>/dev/null)
  if [ -z "$hook_script" ]; then
    return 0
  fi

  local hook_path="${ext_dir}/${hook_script}"
  if [ ! -x "$hook_path" ]; then
    return 0
  fi

  echo "[skill-base] Running extension hook: ${hook_name} (${hook_path})"
  "$hook_path" "$task_number" "$task_type" "$task_dir" "$session_id" "$operation" || \
    echo "[skill-base] WARNING: Extension hook '${hook_name}' exited non-zero (non-blocking)"
}

# ORCHESTRATOR MODE: Support for skill-orchestrate dispatch (task 596).
# When orchestrator_mode=true in delegation context, skills call skill_write_orchestrator_handoff()
# in their postflight to produce .orchestrator-handoff.json for the state machine loop.
# See: .claude/docs/architecture/handoff-schema.md

# ─────────────────────────────────────────────────────────────────────────────
# Stage 1: Validate input task number
# Usage: skill_validate_input "$task_number"
# Exports: TASK_DATA, TASK_TYPE, TASK_STATUS, PROJECT_NAME, PADDED_NUM, TASK_DIR
# Exit 1 if task not found or in terminal state
skill_validate_input() {
  local task_number="$1"
  PADDED_NUM=$(printf "%03d" "$task_number")
  TASK_DATA=$(jq -r --argjson num "$task_number" \
    '.active_projects[] | select(.project_number == $num)' \
    specs/state.json)
  if [ -z "$TASK_DATA" ]; then
    echo "ERROR: Task $task_number not found in state.json" >&2
    exit 1
  fi
  TASK_TYPE=$(echo "$TASK_DATA" | jq -r '.task_type // "general"')
  TASK_STATUS=$(echo "$TASK_DATA" | jq -r '.status')
  PROJECT_NAME=$(echo "$TASK_DATA" | jq -r '.project_name')
  DESCRIPTION=$(echo "$TASK_DATA" | jq -r '.description // ""')
  TASK_DIR="specs/${PADDED_NUM}_${PROJECT_NAME}"
  # Block terminal states
  if [ "$TASK_STATUS" = "completed" ] || [ "$TASK_STATUS" = "abandoned" ] || [ "$TASK_STATUS" = "expanded" ]; then
    echo "ERROR: Task $task_number is in terminal state [$TASK_STATUS]" >&2
    exit 1
  fi
  export TASK_DATA TASK_TYPE TASK_STATUS PROJECT_NAME DESCRIPTION PADDED_NUM TASK_DIR
}

# ─────────────────────────────────────────────────────────────────────────────
# Stage 2: Update status to in-progress variant
# Usage: skill_preflight_update "$task_number" "$operation" "$session_id"
# operation: "research" | "plan" | "implement" | "revise"
# Calls extension hook: hooks.preflight (after status update)
skill_preflight_update() {
  local task_number="$1"
  local operation="$2"
  local session_id="$3"
  bash .claude/scripts/update-task-status.sh preflight "$task_number" "$operation" "$session_id"
  # Extension hook: preflight (runs after status update)
  skill_run_extension_hook "preflight" "$task_number" "${TASK_TYPE:-}" "${TASK_DIR:-}" "$session_id" "$operation"
}

# ─────────────────────────────────────────────────────────────────────────────
# Stage 3: Create postflight-pending marker file
# Usage: skill_create_postflight_marker "$padded_num" "$project_name" "$session_id" "$skill_name" "$operation"
skill_create_postflight_marker() {
  local padded_num="$1"
  local project_name="$2"
  local session_id="$3"
  local skill_name="$4"
  local operation="$5"
  local task_dir="specs/${padded_num}_${project_name}"
  mkdir -p "$task_dir"
  cat > "${task_dir}/.postflight-pending" << EOF
{
  "session_id": "${session_id}",
  "skill": "${skill_name}",
  "operation": "${operation}",
  "reason": "Postflight pending: status update, artifact linking, git commit",
  "created": "$(date -u +%Y-%m-%dT%H:%M:%SZ)",
  "stop_hook_active": false
}
EOF
}

# ─────────────────────────────────────────────────────────────────────────────
# Stage 4: Extension context injection (hook invocation only)
# Usage: skill_context_injection "$task_number" "$session_id" "$operation"
# Calls extension hook: hooks.context_injection
# This function provides a call site for extensions to inject domain-specific
# context before agent delegation. The hook receives task metadata via positional args.
skill_context_injection() {
  local task_number="$1"
  local session_id="$2"
  local operation="${3:-research}"
  skill_run_extension_hook "context_injection" "$task_number" "${TASK_TYPE:-}" "${TASK_DIR:-}" "$session_id" "$operation"
}

# ─────────────────────────────────────────────────────────────────────────────
# Stage 3a: Read artifact number for this task
# Usage: skill_read_artifact_number "$task_number" "$padded_num" "$project_name" "$artifact_dir" "$mode"
# mode: "current" (researcher: use next_artifact_number as-is)
#        "prev"    (planner/implementer: use next_artifact_number - 1)
# Exports: ARTIFACT_NUMBER, ARTIFACT_PADDED
skill_read_artifact_number() {
  local task_number="$1"
  local padded_num="$2"
  local project_name="$3"
  local artifact_dir="$4"  # "reports/" | "plans/" | "summaries/"
  local mode="${5:-prev}"
  local next_num
  next_num=$(jq -r --argjson num "$task_number" \
    '.active_projects[] | select(.project_number == $num) | .next_artifact_number // 1' \
    specs/state.json)
  if [ "$next_num" = "null" ] || [ -z "$next_num" ]; then
    # Legacy fallback: count existing artifacts in directory
    local count
    count=$(ls "specs/${padded_num}_${project_name}/${artifact_dir}"*[0-9][0-9]*.md 2>/dev/null | wc -l)
    ARTIFACT_NUMBER=$((count + 1))
  elif [ "$mode" = "current" ]; then
    ARTIFACT_NUMBER="$next_num"
  else
    # mode = "prev": planner/implementer share the same round as preceding research
    if [ "$next_num" -le 1 ]; then
      ARTIFACT_NUMBER=1
    else
      ARTIFACT_NUMBER=$((next_num - 1))
    fi
  fi
  ARTIFACT_PADDED=$(printf "%02d" "$ARTIFACT_NUMBER")
  export ARTIFACT_NUMBER ARTIFACT_PADDED
}

# ─────────────────────────────────────────────────────────────────────────────
# Stage 6: Read agent metadata file
# Usage: skill_read_metadata "$padded_num" "$project_name"
# Exports: SUBAGENT_STATUS, ARTIFACT_PATH, ARTIFACT_TYPE, ARTIFACT_SUMMARY, MEMORY_CANDIDATES
skill_read_metadata() {
  local padded_num="$1"
  local project_name="$2"
  local meta_file="specs/${padded_num}_${project_name}/.return-meta.json"
  if [ ! -f "$meta_file" ] || ! jq empty "$meta_file" 2>/dev/null; then
    echo "Error: Invalid or missing metadata file: $meta_file" >&2
    SUBAGENT_STATUS="failed"
    ARTIFACT_PATH=""
    ARTIFACT_TYPE=""
    ARTIFACT_SUMMARY="Agent did not write metadata"
    MEMORY_CANDIDATES="[]"
  else
    SUBAGENT_STATUS=$(jq -r '.status' "$meta_file")
    ARTIFACT_PATH=$(jq -r '.artifacts[0].path // ""' "$meta_file")
    ARTIFACT_TYPE=$(jq -r '.artifacts[0].type // ""' "$meta_file")
    ARTIFACT_SUMMARY=$(jq -r '.artifacts[0].summary // ""' "$meta_file")
    MEMORY_CANDIDATES=$(jq -c '.memory_candidates // []' "$meta_file")
  fi
  export SUBAGENT_STATUS ARTIFACT_PATH ARTIFACT_TYPE ARTIFACT_SUMMARY MEMORY_CANDIDATES
}

# ─────────────────────────────────────────────────────────────────────────────
# Stage 6a: Validate artifact exists and meets format requirements (non-blocking)
# Usage: skill_validate_artifact "$status" "$artifact_path" "$artifact_kind" ["$task_number" "$session_id" "$operation"]
# artifact_kind: "report" | "plan" | "summary"
# Validation only runs when status matches a success state
# Calls extension hook: hooks.verification (after artifact validation)
skill_validate_artifact() {
  local status="$1"
  local artifact_path="$2"
  local artifact_kind="$3"
  local task_number="${4:-}"
  local session_id="${5:-}"
  local operation="${6:-}"
  if [ "$status" != "failed" ] && [ -n "$artifact_path" ] && [ -f "$artifact_path" ]; then
    echo "Validating ${artifact_kind} artifact..."
    if ! bash .claude/scripts/validate-artifact.sh "$artifact_path" "$artifact_kind" --fix 2>/dev/null; then
      echo "WARNING: ${artifact_kind} artifact has format issues (non-blocking). Review output above."
    fi
  fi
  # Extension hook: verification (runs after artifact validation, non-blocking)
  if [ -n "$task_number" ]; then
    skill_run_extension_hook "verification" "$task_number" "${TASK_TYPE:-}" "${TASK_DIR:-}" "$session_id" "$operation"
  fi
}

# ─────────────────────────────────────────────────────────────────────────────
# Stage 7: Update status to completed variant
# Usage: skill_postflight_update "$task_number" "$operation" "$session_id" "$status"
# Only updates state when status is a success value (researched/planned/implemented)
# Calls extension hook: hooks.postflight (after status update, non-blocking)
skill_postflight_update() {
  local task_number="$1"
  local operation="$2"
  local session_id="$3"
  local status="$4"
  case "$status" in
    researched|planned|implemented)
      bash .claude/scripts/update-task-status.sh postflight "$task_number" "$operation" "$session_id"
      ;;
    *)
      echo "[skill-base] Non-success status '${status}' — postflight status update skipped"
      ;;
  esac
  # Extension hook: postflight (runs after status update, non-blocking)
  skill_run_extension_hook "postflight" "$task_number" "${TASK_TYPE:-}" "${TASK_DIR:-}" "$session_id" "$operation"
}

# ─────────────────────────────────────────────────────────────────────────────
# Stage 7a: Increment artifact number in state.json (research only)
# Usage: skill_increment_artifact_number "$task_number"
# Research is the only operation that advances the sequence counter.
skill_increment_artifact_number() {
  local task_number="$1"
  python3 -c "
import json
with open('specs/state.json', 'r') as f:
    state = json.load(f)
for p in state['active_projects']:
    if p['project_number'] == $task_number:
        p['next_artifact_number'] = p.get('next_artifact_number', 1) + 1
        break
with open('specs/state.json', 'w') as f:
    json.dump(state, f, indent=2)
    f.write('\n')
"
}

# ─────────────────────────────────────────────────────────────────────────────
# Stage 7b: Propagate memory candidates to state.json (append semantics)
# Usage: skill_propagate_memory_candidates "$task_number" "$memory_candidates"
# Appends to any existing candidates so research + implementation candidates coexist.
skill_propagate_memory_candidates() {
  local task_number="$1"
  local memory_candidates="$2"
  if [ "$memory_candidates" != "[]" ] && [ -n "$memory_candidates" ]; then
    python3 -c "
import json
with open('specs/state.json', 'r') as f:
    state = json.load(f)
new_candidates = json.loads('''$memory_candidates''')
for p in state['active_projects']:
    if p['project_number'] == $task_number:
        existing = p.get('memory_candidates', [])
        p['memory_candidates'] = existing + new_candidates
        break
with open('specs/state.json', 'w') as f:
    json.dump(state, f, indent=2)
    f.write('\n')
"
  fi
}

# ─────────────────────────────────────────────────────────────────────────────
# Stage 8: Link artifacts to state.json and TODO.md
# Usage: skill_link_artifacts "$task_number" "$artifact_path" "$artifact_type" "$artifact_summary" "$field_name" "$next_field"
# artifact_type: "research" | "plan" | "summary"
# field_name:   '**Research**' | '**Plan**' | '**Summary**'
# next_field:   '**Plan**' (research) | '**Description**' (plan/summary)
# Uses two-step jq pattern to avoid Issue #1132 (!=  escaping bug)
skill_link_artifacts() {
  local task_number="$1"
  local artifact_path="$2"
  local artifact_type="$3"
  local artifact_summary="$4"
  local field_name="${5:-'**Summary**'}"
  local next_field="${6:-'**Description**'}"
  if [ -n "$artifact_path" ]; then
    # Step 1: Remove existing artifacts of same type (use "| not" pattern — Issue #1132 safe)
    jq --arg atype "$artifact_type" \
      '(.active_projects[] | select(.project_number == '"$task_number"')).artifacts =
        [(.active_projects[] | select(.project_number == '"$task_number"')).artifacts // [] | .[] | select(.type == $atype | not)]' \
      specs/state.json > specs/tmp/state.json && mv specs/tmp/state.json specs/state.json
    # Step 2: Add new artifact entry
    jq --arg path "$artifact_path" \
       --arg type "$artifact_type" \
       --arg summary "$artifact_summary" \
      '(.active_projects[] | select(.project_number == '"$task_number"')).artifacts += [{"path": $path, "type": $type, "summary": $summary}]' \
      specs/state.json > specs/tmp/state.json && mv specs/tmp/state.json specs/state.json
    # Link in TODO.md
    bash .claude/scripts/link-artifact-todo.sh "$task_number" "$field_name" "$next_field" "$artifact_path" 2>/dev/null || \
      echo "WARNING: link-artifact-todo.sh exited non-zero (non-blocking)"
  fi
}

# ─────────────────────────────────────────────────────────────────────────────
# Stage 9/10: Cleanup temporary files
# Usage: skill_cleanup "$padded_num" "$project_name"
# Removes .postflight-pending, .postflight-loop-guard, .return-meta.json
# Note: Implementer also removes .continuation-loop-guard inline (after calling this)
skill_cleanup() {
  local padded_num="$1"
  local project_name="$2"
  local task_dir="specs/${padded_num}_${project_name}"
  rm -f "${task_dir}/.postflight-pending" \
        "${task_dir}/.postflight-loop-guard" \
        "${task_dir}/.return-meta.json" 2>/dev/null || true
}

# ─────────────────────────────────────────────────────────────────────────────
# Orchestrator Mode: Write .orchestrator-handoff.json for skill-orchestrate
# Usage: skill_write_orchestrator_handoff "$orchestrator_mode" "$padded_num" "$project_name" \
#          "$phase" "$status" "$summary" "$artifact_path" "$artifact_type" "$next_hint"
#
# Parameters:
#   $1 = orchestrator_mode : "true" | "false" — write only if "true"
#   $2 = padded_num        : zero-padded task number (e.g., "595")
#   $3 = project_name      : task slug (e.g., "my_task_name")
#   $4 = phase             : "research" | "plan" | "implement"
#   $5 = status            : "researched" | "planned" | "implemented" | "partial" | "failed" | "blocked"
#   $6 = summary           : 2-4 sentence summary (~100 token budget; truncated if needed)
#   $7 = artifact_path     : path to primary artifact (may be empty string)
#   $8 = artifact_type     : "report" | "plan" | "summary" (may be empty string)
#   $9 = next_hint         : "plan" | "implement" | "revise" | "none"
#
# Optional (set before calling): ORCHESTRATOR_HANDOFF_CONTINUATION_JSON (JSON object or "null")
#   Example: export ORCHESTRATOR_HANDOFF_CONTINUATION_JSON='{"handoff_path":"...","phases_completed":2,"phases_total":4}'
# Optional (set before calling): ORCHESTRATOR_HANDOFF_PHASES_COMPLETED (integer, default 0)
#   Example: export ORCHESTRATOR_HANDOFF_PHASES_COMPLETED=3
# Optional (set before calling): ORCHESTRATOR_HANDOFF_PHASES_TOTAL (integer, default 0)
#   Example: export ORCHESTRATOR_HANDOFF_PHASES_TOTAL=4
#
# Schema reference: .claude/docs/architecture/handoff-schema.md
# Token budget: full object must be ≤400 tokens; summary is truncated at ~100 tokens.
skill_write_orchestrator_handoff() {
  local orchestrator_mode="$1"
  local padded_num="$2"
  local project_name="$3"
  local phase="$4"
  local status="$5"
  local summary="$6"
  local artifact_path="$7"
  local artifact_type="$8"
  local next_hint="${9:-none}"

  # Guard: only write when orchestrator_mode is explicitly "true"
  if [ "$orchestrator_mode" != "true" ]; then
    return 0
  fi

  local handoff_path="specs/${padded_num}_${project_name}/.orchestrator-handoff.json"

  # Truncate summary at ~100 tokens (~400 chars) to respect token budget
  local truncated_summary
  if [ "${#summary}" -gt 400 ]; then
    truncated_summary="${summary:0:397}..."
  else
    truncated_summary="$summary"
  fi

  # Build artifacts array (empty if no artifact_path)
  local artifacts_json
  if [ -n "$artifact_path" ] && [ -n "$artifact_type" ]; then
    artifacts_json=$(printf '[{"type":"%s","path":"%s"}]' "$artifact_type" "$artifact_path")
  else
    artifacts_json='[]'
  fi

  # Continuation context (set externally if partial with handoff)
  local continuation_json="${ORCHESTRATOR_HANDOFF_CONTINUATION_JSON:-null}"

  # Phase counts (set externally by skill-implementer postflight)
  local phases_completed="${ORCHESTRATOR_HANDOFF_PHASES_COMPLETED:-0}"
  local phases_total="${ORCHESTRATOR_HANDOFF_PHASES_TOTAL:-0}"

  # Write handoff JSON
  jq -n \
    --arg schema "orchestrator-handoff-v1" \
    --arg phase "$phase" \
    --arg status "$status" \
    --arg summary "$truncated_summary" \
    --argjson artifacts "$artifacts_json" \
    --arg next_hint "$next_hint" \
    --argjson phases_completed "$phases_completed" \
    --argjson phases_total "$phases_total" \
    --argjson continuation "$continuation_json" \
    '{
      "$schema": $schema,
      "phase": $phase,
      "status": $status,
      "summary": $summary,
      "artifacts": $artifacts,
      "phases_completed": $phases_completed,
      "phases_total": $phases_total,
      "blockers": [],
      "next_action_hint": $next_hint,
      "files_modified": [],
      "decisions_made": [],
      "dead_ends": [],
      "continuation_context": $continuation
    }' > "$handoff_path" && \
    echo "[skill-base] Orchestrator handoff written: $handoff_path" || \
    echo "[skill-base] WARNING: Failed to write orchestrator handoff to $handoff_path" >&2
}
