#!/usr/bin/env bash
# vault-operation.sh - Execute vault archival operation when task numbering exceeds 1000
#
# Usage: vault-operation.sh <state_json> [--confirmed]
#
# When next_project_number > 1000, this script:
#   1. Detects vault threshold
#   2. Creates vault directory (specs/vault/NN-vault/)
#   3. Moves specs/archive/ into the vault
#   4. Reinitializes specs/archive/ with empty state
#   5. Renumbers active tasks > 1000 by subtracting 1000
#   6. Resets next_project_number to max(renumbered) + 1
#   7. Regenerates Task Order via generate-task-order.sh
#
# The --confirmed flag skips the vault threshold check and proceeds unconditionally.
# Without --confirmed, exits 0 if next_project_number <= 1000 (no-op).
#
# Exit codes:
#   0 - Success (including no-op when threshold not reached)
#   1 - Error (missing arguments, files not found, operation failed)

set -euo pipefail

# --- Arguments ---
state_json="${1:-}"
confirmed=false
if [ "${2:-}" = "--confirmed" ]; then
  confirmed=true
fi

if [ -z "$state_json" ]; then
  echo "Usage: vault-operation.sh <state_json> [--confirmed]" >&2
  exit 1
fi

# --- Validate inputs ---
if [ ! -f "$state_json" ]; then
  echo "error: state.json not found: $state_json" >&2
  exit 1
fi

# --- Paths ---
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"
SPECS_DIR="$PROJECT_ROOT/specs"
ARCHIVE_DIR="$SPECS_DIR/archive"
VAULT_PARENT_DIR="$SPECS_DIR/vault"
TODO_FILE="$SPECS_DIR/TODO.md"
GENERATE_TASK_ORDER="$SCRIPT_DIR/generate-task-order.sh"

# --- Step 5.8.1: Detect vault threshold ---
next_num=$(jq -r '.next_project_number' "$state_json")

if ! $confirmed; then
  if [ "$next_num" -le 1000 ]; then
    # Threshold not reached -- no-op
    exit 0
  fi
fi

echo "Vault threshold reached: next_project_number=$next_num"

# --- Step 5.8.2: Identify tasks to renumber ---
tasks_to_renumber=$(jq -r '
  .active_projects[] |
  select(.project_number > 1000) |
  {
    old_number: .project_number,
    new_number: (.project_number - 1000),
    project_name: .project_name
  }
' "$state_json" 2>/dev/null || echo "[]")

renumber_count=$(echo "$tasks_to_renumber" | jq -s 'length' 2>/dev/null || echo "0")

echo "Active tasks to renumber: $renumber_count"

# --- Step 5.8.4: Create vault directory ---
vault_count=$(jq -r '.vault_count // 0' "$state_json")
new_vault_num=$((vault_count + 1))
vault_dir_name=$(printf "%02d-vault" "$new_vault_num")
vault_path="${VAULT_PARENT_DIR}/${vault_dir_name}"

mkdir -p "$vault_path"
echo "Created vault directory: $vault_path"

# Move archive into vault
if [ -d "$ARCHIVE_DIR" ]; then
  mv "$ARCHIVE_DIR" "${vault_path}/archive"
  echo "Moved specs/archive/ -> ${vault_path}/archive/"

  # Move archive state.json to vault root
  if [ -f "${vault_path}/archive/state.json" ]; then
    mv "${vault_path}/archive/state.json" "${vault_path}/state.json"
    echo "Moved archive/state.json -> vault state.json"
  fi
else
  echo "Note: specs/archive/ not found (skipped)"
  mkdir -p "${vault_path}/archive"
fi

# --- Step 5.8.5: Create vault meta.json ---
current_timestamp=$(date -u +"%Y-%m-%dT%H:%M:%SZ")
archived_count=$(jq -r '.completed_projects | length' "${vault_path}/state.json" 2>/dev/null || echo "0")

jq -n \
  --argjson vault_num "$new_vault_num" \
  --arg created_at "$current_timestamp" \
  --argjson archived_count "$archived_count" \
  --argjson final_task_num "$next_num" \
  '{
    vault_number: $vault_num,
    created_at: $created_at,
    archived_count: $archived_count,
    final_task_number: $final_task_num
  }' > "${vault_path}/meta.json"

echo "Created vault meta.json (archived_count=$archived_count, final_task_number=$next_num)"

# --- Step 5.8.6: Reinitialize archive ---
mkdir -p "$ARCHIVE_DIR"
echo '{ "completed_projects": [] }' > "${ARCHIVE_DIR}/state.json"
echo "Reinitialized specs/archive/ with empty state"

# --- Step 5.8.7: Renumber tasks > 1000 ---
tasks_renumbered=0

if [ "$renumber_count" -gt 0 ]; then
  echo "Renumbering $renumber_count tasks..."

  # Process each task that needs renumbering
  while IFS= read -r task_json; do
    old_num=$(echo "$task_json" | jq -r '.old_number')
    new_num=$(echo "$task_json" | jq -r '.new_number')
    task_name=$(echo "$task_json" | jq -r '.project_name')

    # Update project_number in state.json for this task
    jq --argjson old "$old_num" --argjson new "$new_num" '
      (.active_projects[] | select(.project_number == $old)).project_number = $new
    ' "$state_json" > "${state_json}.tmp" && mv "${state_json}.tmp" "$state_json"

    # Compute padded numbers
    old_padded=$(printf "%04d" "$old_num")
    new_padded=$(printf "%03d" "$new_num")

    # Rename task directory (4-digit -> 3-digit)
    old_dir_padded="${SPECS_DIR}/${old_padded}_${task_name}"
    old_dir_unpadded="${SPECS_DIR}/${old_num}_${task_name}"
    new_dir="${SPECS_DIR}/${new_padded}_${task_name}"

    if [ -d "$old_dir_padded" ]; then
      mv "$old_dir_padded" "$new_dir"
      echo "Renamed: ${old_padded}_${task_name} -> ${new_padded}_${task_name}"
    elif [ -d "$old_dir_unpadded" ]; then
      mv "$old_dir_unpadded" "$new_dir"
      echo "Renamed: ${old_num}_${task_name} -> ${new_padded}_${task_name}"
    else
      echo "Note: no directory found for task $old_num (skipped directory rename)"
    fi

    # Update TODO.md entries -- replace old task number with new
    if [ -f "$TODO_FILE" ]; then
      # Use sed to replace task number references in TODO.md
      sed -i "s/#${old_num}:/#${new_num}:/g" "$TODO_FILE" 2>/dev/null || true
      sed -i "s/#${old_num} /#${new_num} /g" "$TODO_FILE" 2>/dev/null || true
      sed -i "s/(Task ${old_num})/(Task ${new_num})/g" "$TODO_FILE" 2>/dev/null || true
    fi

    tasks_renumbered=$((tasks_renumbered + 1))
    echo "Renumbered task $old_num -> $new_num ($task_name)"

  done < <(echo "$tasks_to_renumber" | jq -c '.')
fi

# --- Step 5.8.8: Reset state ---
max_active=$(jq -r '[.active_projects[].project_number] | max // 0' "$state_json")
new_next_num=$((max_active + 1))

jq --argjson new_next "$new_next_num" \
   --argjson vault_num "$new_vault_num" \
   --arg vault_path "${vault_path}/" \
   --arg created "$current_timestamp" \
   '.next_project_number = $new_next |
    .vault_count = (.vault_count // 0) + 1 |
    .vault_history = (.vault_history // []) + [{
      vault_number: $vault_num,
      vault_dir: $vault_path,
      created_at: $created
    }]' "$state_json" > "${state_json}.tmp"
mv "${state_json}.tmp" "$state_json"

echo "Reset next_project_number to $new_next_num (was $next_num)"
echo "Updated vault_count to $new_vault_num"

# --- Step 5.8.9: Add transition comment to TODO.md ---
if [ -f "$TODO_FILE" ]; then
  current_date=$(date +"%Y-%m-%d")
  comment="<!-- Vault transition: ${current_date} - Archived to ${vault_path}/ -->"

  # Insert comment after the frontmatter (after the closing ---)
  python3 - "$TODO_FILE" "$comment" <<'PYEOF' 2>/dev/null || true
import sys

todo_path = sys.argv[1]
comment = sys.argv[2]

with open(todo_path, 'r') as f:
    content = f.read()

# Find end of YAML frontmatter (second ---)
lines = content.split('\n')
in_frontmatter = False
insert_after = 0
for i, line in enumerate(lines):
    if line.strip() == '---':
        if not in_frontmatter:
            in_frontmatter = True
        else:
            insert_after = i + 1
            break

if insert_after > 0:
    lines.insert(insert_after, comment)
    with open(todo_path, 'w') as f:
        f.write('\n'.join(lines))
    print(f"Added vault transition comment to TODO.md")
PYEOF
fi

# --- Step 5.8.8a: Re-run Task Order Regeneration ---
if [ -f "$GENERATE_TASK_ORDER" ]; then
  bash "$GENERATE_TASK_ORDER" --update-todo "$TODO_FILE" "$state_json" \
    || { echo "Warning: Post-vault Task Order regeneration failed (non-fatal)" >&2; }
  echo "Regenerated Task Order after vault renumbering"
else
  echo "Note: generate-task-order.sh not found -- skipping Task Order regeneration" >&2
fi

# --- Output summary ---
echo ""
echo "Vault operation complete:"
echo "  Vault created: ${vault_path}/"
echo "  Tasks renumbered: $tasks_renumbered"
echo "  New next_project_number: $new_next_num"
echo "  Vault number: $new_vault_num"

exit 0
