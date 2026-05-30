#!/usr/bin/env bash
# roadmap-sync.sh - Scan ROADMAP.md for task matches and apply completion annotations
#
# Usage:
#   Phase A (scan):  roadmap-sync.sh scan  <archivable_tasks_json> <roadmap_path>
#   Phase B (apply): roadmap-sync.sh apply <roadmap_matches_file>  <roadmap_path>
#
# Phase A:
#   Reads archivable tasks from a JSON file (array of state.json active_project entries),
#   separates meta vs non-meta tasks, scans ROADMAP.md for matches via three strategies:
#     1. Explicit roadmap_items field (highest confidence)
#     2. Exact (Task N) reference in ROADMAP.md line
#     3. Summary-based matching (placeholder, not implemented)
#
#   Output (stdout): JSON array of match objects:
#     [{"project_num": N, "status": "completed|abandoned", "match_type": "explicit|exact",
#       "line_num": N, "item_text": "..."}, ...]
#
#   Exit file written to <roadmap_path>.matches.json for use by apply phase.
#
# Phase B:
#   Reads match objects from <roadmap_matches_file> (JSON array).
#   Applies annotations to ROADMAP.md:
#     - Completed + explicit: "- [x] {item_text} *(Completed: Task N, DATE)*"
#     - Completed + exact:    "- [x] {item_text} (Task N) *(Completed: Task N, DATE)*"
#     - Abandoned:            "- [ ] {item_text} (Task N) *(Task N abandoned: reason)*"
#
#   Outputs summary counts to stdout.
#
# IMPORTANT: Meta tasks (task_type: "meta") are excluded from ROADMAP.md matching.
#
# Exit codes:
#   0 - Success
#   1 - Error (missing arguments, file not found, etc.)

set -euo pipefail

# --- Arguments ---
phase="${1:-}"
input_file="${2:-}"
roadmap_path="${3:-}"

if [ -z "$phase" ] || [ -z "$input_file" ] || [ -z "$roadmap_path" ]; then
  echo "Usage:" >&2
  echo "  roadmap-sync.sh scan  <archivable_tasks_json> <roadmap_path>" >&2
  echo "  roadmap-sync.sh apply <roadmap_matches_file>  <roadmap_path>" >&2
  exit 1
fi

if [ "$phase" != "scan" ] && [ "$phase" != "apply" ]; then
  echo "error: phase must be 'scan' or 'apply', got: $phase" >&2
  exit 1
fi

# --- Paths ---
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"

# ============================================================
# PHASE A: SCAN
# ============================================================
if [ "$phase" = "scan" ]; then
  tasks_json="$input_file"

  if [ ! -f "$tasks_json" ]; then
    echo "error: tasks JSON file not found: $tasks_json" >&2
    exit 1
  fi

  # Ensure ROADMAP.md exists -- create with default template if missing
  if [ ! -f "$roadmap_path" ]; then
    echo "Note: ROADMAP.md not found at $roadmap_path -- creating default" >&2
    cat > "$roadmap_path" <<'ROADMAPEOF'
# Project Roadmap

## Phase 1: Current Priorities (High Priority)

- [ ] (No items yet -- add roadmap items here)

## Success Metrics

- (Define success metrics here)
ROADMAPEOF
  fi

  # --- Separate meta and non-meta tasks ---
  # Use file-based jq filter to safely handle task_type comparisons
  tmp_filter="${PROJECT_ROOT}/specs/tmp/roadmap_nonmeta_$$.jq"
  mkdir -p "${PROJECT_ROOT}/specs/tmp"

  cat > "$tmp_filter" <<'JQEOF'
.[] | select(.task_type == "meta" | not) | {
  project_number: .project_number,
  status: .status,
  completion_summary: (.completion_summary // ""),
  roadmap_items: (.roadmap_items // []),
  abandoned_reason: (.abandoned_reason // "")
}
JQEOF

  non_meta_tasks=$(jq -rf "$tmp_filter" "$tasks_json" 2>/dev/null || echo "")
  rm -f "$tmp_filter"

  # --- Initialize match tracking ---
  matches_array="[]"
  roadmap_completed_count=0
  roadmap_abandoned_count=0

  if [ -z "$non_meta_tasks" ]; then
    # No non-meta tasks to match
    echo "$matches_array"
    exit 0
  fi

  # --- Process each non-meta task ---
  while IFS= read -r task_json; do
    [ -z "$task_json" ] && continue

    project_num=$(echo "$task_json" | jq -r '.project_number')
    status=$(echo "$task_json" | jq -r '.status')
    completion_summary=$(echo "$task_json" | jq -r '.completion_summary // ""')
    abandoned_reason=$(echo "$task_json" | jq -r '.abandoned_reason // ""')

    # Extract explicit roadmap_items array
    has_explicit=$(echo "$task_json" | jq -r '.roadmap_items | length')

    # --- Priority 1: Explicit roadmap_items (highest confidence) ---
    if [ "$has_explicit" -gt 0 ]; then
      while IFS= read -r item_text; do
        [ -z "$item_text" ] && continue

        # Escape special regex characters for grep
        escaped_item=$(printf '%s\n' "$item_text" | sed 's/[[\.*^$()+?{|]/\\&/g')
        line_info=$(grep -n "^\s*- \[ \].*${escaped_item}" "$roadmap_path" 2>/dev/null | head -1 || true)

        if [ -n "$line_info" ]; then
          line_num=$(echo "$line_info" | cut -d: -f1)
          match_json=$(jq -n \
            --argjson pn "$project_num" \
            --arg st "$status" \
            --arg mt "explicit" \
            --argjson ln "$line_num" \
            --arg it "$item_text" \
            --arg ar "$abandoned_reason" \
            '{project_num: $pn, status: $st, match_type: $mt, line_num: $ln, item_text: $it, abandoned_reason: $ar}')
          matches_array=$(echo "$matches_array" | jq --argjson m "$match_json" '. += [$m]')
          if [ "$status" = "completed" ]; then
            roadmap_completed_count=$(( roadmap_completed_count + 1 ))
          fi
        fi
      done < <(echo "$task_json" | jq -r '.roadmap_items[]')
      continue  # Skip other matching for this task if explicit items found
    fi

    # --- Priority 2: Exact (Task N) reference matching ---
    matches_raw=$(grep -n "(Task ${project_num})" "$roadmap_path" 2>/dev/null || true)
    if [ -n "$matches_raw" ]; then
      while IFS= read -r match_line; do
        [ -z "$match_line" ] && continue
        line_num=$(echo "$match_line" | cut -d: -f1)
        item_text=$(echo "$match_line" | cut -d: -f2-)

        match_json=$(jq -n \
          --argjson pn "$project_num" \
          --arg st "$status" \
          --arg mt "exact" \
          --argjson ln "$line_num" \
          --arg it "$item_text" \
          --arg ar "$abandoned_reason" \
          '{project_num: $pn, status: $st, match_type: $mt, line_num: $ln, item_text: $it, abandoned_reason: $ar}')
        matches_array=$(echo "$matches_array" | jq --argjson m "$match_json" '. += [$m]')

        if [ "$status" = "completed" ]; then
          roadmap_completed_count=$(( roadmap_completed_count + 1 ))
        elif [ "$status" = "abandoned" ]; then
          roadmap_abandoned_count=$(( roadmap_abandoned_count + 1 ))
        fi
      done <<< "$matches_raw"
      continue
    fi

    # --- Priority 3: Summary-based search (placeholder, not implemented) ---
    # Only for completed tasks with summaries
    if [ -n "$completion_summary" ] && [ "$status" = "completed" ]; then
      # Semantic matching via completion_summary -- future enhancement
      :
    fi

  done < <(echo "$non_meta_tasks" | jq -c '.')

  # Output match array to stdout
  echo "$matches_array"
  echo "roadmap_completed_count=$roadmap_completed_count" >&2
  echo "roadmap_abandoned_count=$roadmap_abandoned_count" >&2

  exit 0
fi

# ============================================================
# PHASE B: APPLY
# ============================================================
if [ "$phase" = "apply" ]; then
  matches_file="$input_file"

  if [ ! -f "$matches_file" ]; then
    echo "error: matches file not found: $matches_file" >&2
    exit 1
  fi

  if [ ! -f "$roadmap_path" ]; then
    echo "error: ROADMAP.md not found: $roadmap_path" >&2
    exit 1
  fi

  matches_json=$(cat "$matches_file")
  match_count=$(echo "$matches_json" | jq 'length')

  if [ "$match_count" = "0" ]; then
    echo "No roadmap matches to apply"
    exit 0
  fi

  # --- Tracking counters ---
  roadmap_completed_annotated=0
  roadmap_abandoned_annotated=0
  roadmap_skipped=0
  roadmap_explicit=0
  roadmap_exact=0

  # --- Process each match ---
  while IFS= read -r match_json; do
    [ -z "$match_json" ] && continue

    project_num=$(echo "$match_json" | jq -r '.project_num')
    status=$(echo "$match_json" | jq -r '.status')
    match_type=$(echo "$match_json" | jq -r '.match_type')
    line_num=$(echo "$match_json" | jq -r '.line_num')
    item_text=$(echo "$match_json" | jq -r '.item_text')
    abandoned_reason=$(echo "$match_json" | jq -r '.abandoned_reason // ""')

    # Get current line content (re-read file each time since edits shift lines)
    # Use item_text for matching instead of line numbers (more robust after edits)
    line_content=$(grep -F "$item_text" "$roadmap_path" 2>/dev/null | head -1 || true)

    if [ -z "$line_content" ]; then
      echo "Note: item not found in ROADMAP.md (may have been moved or edited): $item_text" >&2
      roadmap_skipped=$(( roadmap_skipped + 1 ))
      continue
    fi

    # Skip if already annotated
    if echo "$line_content" | grep -qE '\*(Completed:|\*(Abandoned:|\*(Task [0-9]+ abandoned:'; then
      echo "Skipped: already annotated -- $item_text" >&2
      roadmap_skipped=$(( roadmap_skipped + 1 ))
      continue
    fi

    # Determine current date
    current_date=$(date -u +%Y-%m-%d)

    # Apply annotation based on status and match_type
    if [ "$status" = "completed" ]; then
      if [ "$match_type" = "explicit" ]; then
        # explicit: replace unchecked with checked + annotation
        old_str="- [ ] ${item_text}"
        new_str="- [x] ${item_text} *(Completed: Task ${project_num}, ${current_date})*"
        roadmap_explicit=$(( roadmap_explicit + 1 ))
      else
        # exact: preserve (Task N) reference
        old_str="${item_text}"
        new_str="${item_text} *(Completed: Task ${project_num}, ${current_date})*"
        # Also check the checkbox
        old_str=$(echo "$old_str" | sed 's/- \[ \]/- [x]/')
        roadmap_exact=$(( roadmap_exact + 1 ))
      fi
      roadmap_completed_annotated=$(( roadmap_completed_annotated + 1 ))
    else
      # abandoned -- checkbox stays unchecked
      short_reason="${abandoned_reason:0:50}"
      if [ -z "$short_reason" ]; then
        short_reason="no reason recorded"
      fi

      if [ "$match_type" = "exact" ]; then
        old_str="${item_text}"
        new_str="${item_text} *(Task ${project_num} abandoned: ${short_reason})*"
      else
        old_str="- [ ] ${item_text}"
        new_str="- [ ] ${item_text} *(Task ${project_num} abandoned: ${short_reason})*"
      fi
      roadmap_abandoned_annotated=$(( roadmap_abandoned_annotated + 1 ))
      roadmap_exact=$(( roadmap_exact + 1 ))
    fi

    # Apply the edit using Python for reliable string replacement
    # Write Python script to temp file to avoid heredoc-in-loop issues
    py_script="${PROJECT_ROOT}/specs/tmp/roadmap_apply_$$.py"
    mkdir -p "${PROJECT_ROOT}/specs/tmp"
    printf '%s\n' \
      'import sys' \
      'roadmap_path = sys.argv[1]' \
      'old_str = sys.argv[2]' \
      'new_str = sys.argv[3]' \
      'with open(roadmap_path, "r") as f:' \
      '    content = f.read()' \
      'if old_str not in content:' \
      '    print("Note: old_str not found in ROADMAP.md (skipped)", file=sys.stderr)' \
      '    sys.exit(0)' \
      'new_content = content.replace(old_str, new_str, 1)' \
      'with open(roadmap_path, "w") as f:' \
      '    f.write(new_content)' \
      'print("Applied annotation")' \
      > "$py_script"

    python3 "$py_script" "$roadmap_path" "$old_str" "$new_str" 2>/dev/null || {
      echo "Warning: failed to apply annotation for task $project_num" >&2
      roadmap_skipped=$(( roadmap_skipped + 1 ))
    }
    rm -f "$py_script"

  done < <(echo "$matches_json" | jq -c '.[]')

  # Output summary
  echo "Roadmap annotations applied:"
  echo "  Completed annotated: $roadmap_completed_annotated"
  echo "  Abandoned annotated: $roadmap_abandoned_annotated"
  echo "  Skipped (already annotated): $roadmap_skipped"
  echo "  By match type: explicit=$roadmap_explicit, exact=$roadmap_exact"

  exit 0
fi
