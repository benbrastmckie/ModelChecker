#!/usr/bin/env bash
# archive-task.sh - Archive a single task from active state to archive
#
# Usage: archive-task.sh <task_number> <project_name> [--dry-run]
#
# Operations:
#   A. Move task entry from state.json active_projects to archive/state.json completed_projects
#   B. Remove task entry from state.json active_projects
#   C. Remove task entry from TODO.md
#   D. Move task directory from specs/ to specs/archive/
#
# Handles both padded (015_slug) and unpadded (15_slug) directory formats.
#
# Exit codes:
#   0 - Success
#   1 - Error (missing arguments, files not found, jq failure)

set -euo pipefail

# --- Arguments ---
task_number="${1:-}"
project_name="${2:-}"
dry_run=false
if [ "${3:-}" = "--dry-run" ]; then
  dry_run=true
fi

if [ -z "$task_number" ] || [ -z "$project_name" ]; then
  echo "Usage: archive-task.sh <task_number> <project_name> [--dry-run]" >&2
  exit 1
fi

# --- Paths ---
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"
STATE_FILE="$PROJECT_ROOT/specs/state.json"
ARCHIVE_DIR="$PROJECT_ROOT/specs/archive"
ARCHIVE_STATE_FILE="$ARCHIVE_DIR/state.json"
TODO_FILE="$PROJECT_ROOT/specs/TODO.md"

# --- Validate inputs ---
if [ ! -f "$STATE_FILE" ]; then
  echo "error: state.json not found at $STATE_FILE" >&2
  exit 1
fi

# --- Ensure archive directory exists ---
if ! $dry_run; then
  mkdir -p "$ARCHIVE_DIR"
fi

# --- Initialize archive/state.json if missing ---
if [ ! -f "$ARCHIVE_STATE_FILE" ]; then
  if ! $dry_run; then
    echo '{ "archived_projects": [], "completed_projects": [] }' > "$ARCHIVE_STATE_FILE"
  fi
fi

# --- Extract task entry from state.json ---
task_entry=$(jq --argjson num "$task_number" \
  '.active_projects[] | select(.project_number == $num)' \
  "$STATE_FILE" 2>/dev/null)

if [ -z "$task_entry" ] || [ "$task_entry" = "null" ]; then
  echo "error: task $task_number not found in active_projects" >&2
  exit 1
fi

task_status=$(echo "$task_entry" | jq -r '.status // "completed"')

if $dry_run; then
  echo "[dry-run] Would archive task $task_number ($project_name, status: $task_status)"
  # Determine directory
  padded_num=$(printf "%03d" "$task_number")
  if [ -d "$PROJECT_ROOT/specs/${padded_num}_${project_name}" ]; then
    echo "[dry-run] Would move: specs/${padded_num}_${project_name} -> specs/archive/${padded_num}_${project_name}"
  elif [ -d "$PROJECT_ROOT/specs/${task_number}_${project_name}" ]; then
    echo "[dry-run] Would move: specs/${task_number}_${project_name} -> specs/archive/${padded_num}_${project_name}"
  else
    echo "[dry-run] Note: no directory found for task $task_number (would skip)"
  fi
  exit 0
fi

# --- A. Move task entry to archive/state.json ---
# Determine target array in archive based on status
if [ "$task_status" = "abandoned" ]; then
  archive_array="archived_projects"
else
  archive_array="completed_projects"
fi

jq --argjson entry "$task_entry" \
   --arg array "$archive_array" \
   '.[$array] += [$entry]' \
  "$ARCHIVE_STATE_FILE" > "${ARCHIVE_STATE_FILE}.tmp" \
  && mv "${ARCHIVE_STATE_FILE}.tmp" "$ARCHIVE_STATE_FILE"

echo "Archived state entry for task $task_number to $archive_array"

# --- B. Remove task from state.json active_projects ---
# Use del() pattern -- Issue #1132-safe (avoids != operator)
jq --argjson num "$task_number" \
  'del(.active_projects[] | select(.project_number == $num))' \
  "$STATE_FILE" > "${STATE_FILE}.tmp" \
  && mv "${STATE_FILE}.tmp" "$STATE_FILE"

echo "Removed task $task_number from active_projects"

# --- C. Update TODO.md (remove completed/abandoned entry) ---
# This is a best-effort step -- warn on failure but don't abort
if [ -f "$TODO_FILE" ]; then
  # Remove the task block from TODO.md (format: "### N. Title" through next "---" separator)
  # Use line-by-line removal for robustness with multi-line descriptions
  python3 - "$TODO_FILE" "$task_number" <<'PYEOF' 2>/dev/null || true
import sys, re

todo_path = sys.argv[1]
task_num = sys.argv[2]

with open(todo_path, 'r') as f:
    content = f.read()

# Line-by-line block removal anchored on "^### N. " (literal dot + space)
# Handles: multi-line descriptions, last task without trailing "---", partial number matches
lines = content.split('\n')
start_pattern = re.compile(r'^### ' + re.escape(task_num) + r'\. ')
in_block = False
output_lines = []
i = 0
while i < len(lines):
    line = lines[i]
    if not in_block and start_pattern.match(line):
        in_block = True
        i += 1
        continue
    if in_block:
        if line.strip() == '---':
            in_block = False  # consume the separator line
            i += 1
            continue
        i += 1
        continue
    output_lines.append(line)
    i += 1
new_content = '\n'.join(output_lines)

if new_content != content:
    with open(todo_path, 'w') as f:
        f.write(new_content)
    print(f"Removed task {task_num} block from TODO.md")
else:
    print(f"Note: task {task_num} block not found in TODO.md (skipped)", file=sys.stderr)
PYEOF
fi

# --- D. Move project directory to archive ---
padded_num=$(printf "%03d" "$task_number")

# Check padded directory first, then fall back to unpadded for legacy
if [ -d "$PROJECT_ROOT/specs/${padded_num}_${project_name}" ]; then
  src="$PROJECT_ROOT/specs/${padded_num}_${project_name}"
elif [ -d "$PROJECT_ROOT/specs/${task_number}_${project_name}" ]; then
  src="$PROJECT_ROOT/specs/${task_number}_${project_name}"
else
  src=""
fi

# Always archive to padded directory
dst="${ARCHIVE_DIR}/${padded_num}_${project_name}"

if [ -n "$src" ] && [ -d "$src" ]; then
  mv "$src" "$dst"
  echo "Moved: $(basename "$src") -> archive/${padded_num}_${project_name}/"
else
  echo "Note: no directory for task $task_number (skipped)"
fi

exit 0
