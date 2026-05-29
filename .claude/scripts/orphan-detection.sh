#!/usr/bin/env bash
# orphan-detection.sh - Detect orphaned and misplaced task directories
#
# Usage: orphan-detection.sh <specs_dir> <state_json> <archive_state_json>
#
# Scans for project directories not tracked in any state file (orphans)
# and directories in specs/ that are tracked in archive/state.json (misplaced).
#
# Output format (stdout):
#   ---orphaned_in_specs---
#   specs/NNN_slug/
#   ...
#   ---orphaned_in_archive---
#   specs/archive/NNN_slug/
#   ...
#   ---misplaced_in_specs---
#   specs/NNN_slug/
#   ...
#
# Exit codes:
#   0 - Success (even if no orphans found)
#   1 - Error (missing arguments or files)

set -euo pipefail

# --- Arguments ---
specs_dir="${1:-}"
state_json="${2:-}"
archive_state_json="${3:-}"

if [ -z "$specs_dir" ] || [ -z "$state_json" ] || [ -z "$archive_state_json" ]; then
  echo "Usage: orphan-detection.sh <specs_dir> <state_json> <archive_state_json>" >&2
  exit 1
fi

# --- Validate inputs ---
if [ ! -d "$specs_dir" ]; then
  echo "error: specs_dir not found: $specs_dir" >&2
  exit 1
fi

if [ ! -f "$state_json" ]; then
  echo "error: state_json not found: $state_json" >&2
  exit 1
fi

# archive/state.json may not exist yet -- treat as empty
if [ ! -f "$archive_state_json" ]; then
  archive_state_json=""
fi

# --- Helper: check if project number is in state file ---
in_active_projects() {
  local num="$1"
  jq -r --arg n "$num" \
    '.active_projects[] | select(.project_number == ($n | tonumber)) | .project_number' \
    "$state_json" 2>/dev/null
}

in_archive_projects() {
  local num="$1"
  if [ -z "$archive_state_json" ]; then
    echo ""
    return
  fi
  jq -r --arg n "$num" \
    '.completed_projects[] | select(.project_number == ($n | tonumber)) | .project_number' \
    "$archive_state_json" 2>/dev/null
}

# --- Detect orphaned directories in specs/ ---
orphaned_in_specs=()
for dir in "${specs_dir}"/[0-9]*_*/; do
  [ -d "$dir" ] || continue
  project_num=$(basename "$dir" | cut -d_ -f1)

  # Check if in state.json active_projects
  in_active=$(in_active_projects "$project_num")

  # Check if in archive/state.json completed_projects
  in_archive=$(in_archive_projects "$project_num")

  # If not in either, it's an orphan
  if [ -z "$in_active" ] && [ -z "$in_archive" ]; then
    orphaned_in_specs+=("$dir")
  fi
done

# --- Detect orphaned directories in specs/archive/ ---
archive_dir="${specs_dir}/archive"
orphaned_in_archive=()
if [ -d "$archive_dir" ]; then
  for dir in "${archive_dir}"/[0-9]*_*/; do
    [ -d "$dir" ] || continue
    project_num=$(basename "$dir" | cut -d_ -f1)

    # Check if in archive/state.json completed_projects
    in_archive=$(in_archive_projects "$project_num")

    # If not tracked, it's an orphan
    if [ -z "$in_archive" ]; then
      orphaned_in_archive+=("$dir")
    fi
  done
fi

# --- Detect misplaced directories in specs/ ---
# These are in specs/ but tracked in archive/state.json (should be in archive/)
misplaced_in_specs=()
for dir in "${specs_dir}"/[0-9]*_*/; do
  [ -d "$dir" ] || continue
  project_num=$(basename "$dir" | cut -d_ -f1)

  # Skip if already identified as orphan (not tracked anywhere)
  in_active=$(in_active_projects "$project_num")

  # Check if tracked in archive/state.json (should be in archive/)
  in_archive=$(in_archive_projects "$project_num")

  # If in archive state but not in active state, it's misplaced
  if [ -z "$in_active" ] && [ -n "$in_archive" ]; then
    misplaced_in_specs+=("$dir")
  fi
done

# --- Output results ---
echo "---orphaned_in_specs---"
for dir in "${orphaned_in_specs[@]+"${orphaned_in_specs[@]}"}"; do
  echo "$dir"
done

echo "---orphaned_in_archive---"
for dir in "${orphaned_in_archive[@]+"${orphaned_in_archive[@]}"}"; do
  echo "$dir"
done

echo "---misplaced_in_specs---"
for dir in "${misplaced_in_specs[@]+"${misplaced_in_specs[@]}"}"; do
  echo "$dir"
done

exit 0
