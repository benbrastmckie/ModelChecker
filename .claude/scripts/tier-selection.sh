#!/usr/bin/env bash
# tier-selection.sh - Interactive tiered issue selection for /review task creation
#
# Implements Steps 5.5.6-5.5.7 from /review command:
#   5.5.6 Interactive Group Selection (Tier 1) - AskUserQuestion with multiSelect
#   5.5.7 Granularity Selection (Tier 2) - how to create tasks
#         (includes Tier 3 manual selection when "Show issues and select manually" is chosen)
#
# Note: This script generates AskUserQuestion JSON prompts and parses responses.
#       It does NOT execute AskUserQuestion itself (that requires the /review command context).
#       Instead, it outputs structured prompt JSON to stdout for the caller to execute.
#
# Usage:
#   echo "$grouped_issues" | bash tier-selection.sh --mode tier1
#   echo "$grouped_issues" | bash tier-selection.sh --mode tier2 --selected-groups "$indices"
#   echo "$grouped_issues" | bash tier-selection.sh --mode tier3 --selected-groups "$indices"
#   echo "$grouped_issues" | bash tier-selection.sh --summarize
#
# Options:
#   --mode tier1               Output Tier 1 group selection prompt JSON
#   --mode tier2               Output Tier 2 granularity selection prompt JSON
#   --mode tier3               Output Tier 3 manual issue selection prompt JSON
#   --selected-groups INDICES  Comma-separated group indices selected in Tier 1
#   --file PATH                Read grouped issues from file instead of stdin
#   --summarize                Output a human-readable summary of groups (no prompts)
#
# Input:  JSON array of grouped issue objects (output from issue-grouping.sh)
# Output: AskUserQuestion JSON object to stdout, or selection summary
#
# The caller is expected to:
#   1. Run --mode tier1 -> display prompt -> capture user selection
#   2. Run --mode tier2 with selected indices -> display prompt -> capture granularity choice
#   3. If granularity = "manual": run --mode tier3 -> display prompt -> capture issue selections
#   4. Use final selection to create tasks

set -euo pipefail

# ─── Parse arguments ──────────────────────────────────────────────────────────

MODE=""
SELECTED_GROUPS=""
INPUT_FILE=""
SUMMARIZE=false

while [[ $# -gt 0 ]]; do
  case "$1" in
    --mode)
      MODE="$2"
      shift 2
      ;;
    --selected-groups)
      SELECTED_GROUPS="$2"
      shift 2
      ;;
    --file)
      INPUT_FILE="$2"
      shift 2
      ;;
    --summarize)
      SUMMARIZE=true
      shift
      ;;
    *)
      echo "Unknown argument: $1" >&2
      exit 1
      ;;
  esac
done

# Read input JSON
if [[ -n "$INPUT_FILE" ]]; then
  if [[ ! -f "$INPUT_FILE" ]]; then
    echo "Error: file not found: $INPUT_FILE" >&2
    exit 1
  fi
  GROUPED_ISSUES=$(cat "$INPUT_FILE")
else
  GROUPED_ISSUES=$(cat)
fi

# Validate input is a JSON array
if ! echo "$GROUPED_ISSUES" | jq -e 'type == "array"' > /dev/null 2>&1; then
  echo "Error: input must be a JSON array of grouped issues" >&2
  exit 1
fi

GROUP_COUNT=$(echo "$GROUPED_ISSUES" | jq 'length')

# ─── Summarize mode ───────────────────────────────────────────────────────────

if [[ "$SUMMARIZE" == "true" ]]; then
  echo "$GROUPED_ISSUES" | jq -r '
    if length == 0 then
      "No issue groups found."
    else
      "Issue Groups (\(length) total):\n" +
      (to_entries | map(
        "  [\(.key)] \(.value.label) -- \(.value.item_count) issues" +
        (if (.value.severity_breakdown.critical // 0) > 0 then " [CRITICAL]" else "" end) +
        " (score: \(.value.total_score))"
      ) | join("\n"))
    end
  '
  exit 0
fi

# ─── Tier 1: Group selection prompt ──────────────────────────────────────────

if [[ "$MODE" == "tier1" ]]; then
  if [[ "$GROUP_COUNT" -eq 0 ]]; then
    # No groups -- output empty selection prompt
    jq -n '{
      "question": "No issue groups were found. Proceed without creating tasks?",
      "header": "Review Task Proposals",
      "multiSelect": false,
      "options": [
        {"label": "Continue without tasks", "description": "No issues found to create tasks for"},
        {"label": "Exit", "description": "End the review"}
      ],
      "_no_groups": true
    }'
    exit 0
  fi

  # Build options: one per group + individual issues that didn't cluster
  OPTIONS=$(echo "$GROUPED_ISSUES" | jq '
    map(
      . as $group |
      {
        "label": ("[Group] " + $group.label + " (" + ($group.item_count | tostring) + " " +
                  (if $group.item_count == 1 then "issue" else "issues" end) + ")"),
        "description": (
          # Severity breakdown
          (
            [
              (if ($group.severity_breakdown.critical // 0) > 0
               then "Critical: \($group.severity_breakdown.critical)"
               else empty end),
              (if ($group.severity_breakdown.high // 0) > 0
               then "High: \($group.severity_breakdown.high)"
               else empty end),
              (if ($group.severity_breakdown.medium // 0) > 0
               then "Medium: \($group.severity_breakdown.medium)"
               else empty end),
              (if ($group.severity_breakdown.low // 0) > 0
               then "Low: \($group.severity_breakdown.low)"
               else empty end)
            ] | join(", ")
          ) +
          # File list (truncated)
          (if ($group.file_list | length) > 0
           then " | Files: " + ($group.file_list[0:3] | join(", ")) +
                (if ($group.file_list | length) > 3 then "..." else "" end)
           else ""
           end)
        )
      }
    )
  ')

  jq -n \
    --argjson options "$OPTIONS" \
    '{
      "question": "Which task groups should be created? (select all that apply)",
      "header": "Review Task Proposals",
      "multiSelect": true,
      "options": $options,
      "_tier": 1,
      "_group_count": ($options | length)
    }'
  exit 0
fi

# ─── Tier 2: Granularity selection prompt ─────────────────────────────────────

if [[ "$MODE" == "tier2" ]]; then
  if [[ -z "$SELECTED_GROUPS" ]]; then
    echo "Error: --selected-groups is required for tier2 mode" >&2
    exit 1
  fi

  # Parse selected group indices (comma-separated)
  IFS=',' read -ra SELECTED_INDICES <<< "$SELECTED_GROUPS"

  # Count selected groups and total issues within them
  SELECTED_GROUP_COUNT=${#SELECTED_INDICES[@]}

  TOTAL_ISSUES=$(python3 - "$GROUPED_ISSUES" "$SELECTED_GROUPS" << 'PYEOF'
import sys
import json

groups = json.loads(sys.argv[1])
selected_str = sys.argv[2]
selected_indices = [int(i.strip()) for i in selected_str.split(",") if i.strip()]

total = sum(groups[i]["item_count"] for i in selected_indices if i < len(groups))
print(total)
PYEOF
)

  jq -n \
    --argjson group_count "$SELECTED_GROUP_COUNT" \
    --argjson issue_count "$TOTAL_ISSUES" \
    '{
      "question": "How should selected groups be created as tasks?",
      "header": "Task Granularity",
      "multiSelect": false,
      "options": [
        {
          "label": "Keep as grouped tasks",
          "description": ("Creates " + ($group_count | tostring) + " " +
                          (if $group_count == 1 then "task" else "tasks" end) +
                          " (one per selected group)")
        },
        {
          "label": "Expand into individual tasks",
          "description": ("Creates " + ($issue_count | tostring) + " " +
                          (if $issue_count == 1 then "task" else "tasks" end) +
                          " (one per issue in selected groups)")
        },
        {
          "label": "Show issues and select manually",
          "description": "See all issues in selected groups for manual selection"
        }
      ],
      "_tier": 2,
      "_selected_groups": ($group_count),
      "_total_issues": ($issue_count)
    }'
  exit 0
fi

# ─── Tier 3: Manual issue selection prompt ───────────────────────────────────

if [[ "$MODE" == "tier3" ]]; then
  if [[ -z "$SELECTED_GROUPS" ]]; then
    echo "Error: --selected-groups is required for tier3 mode" >&2
    exit 1
  fi

  # Build options: one per individual issue in selected groups
  OPTIONS=$(python3 - "$GROUPED_ISSUES" "$SELECTED_GROUPS" << 'PYEOF'
import sys
import json

groups = json.loads(sys.argv[1])
selected_str = sys.argv[2]
selected_indices = [int(i.strip()) for i in selected_str.split(",") if i.strip()]

options = []
for idx in selected_indices:
    if idx >= len(groups):
        continue
    group = groups[idx]
    group_label = group.get("label", f"Group {idx}")

    for item in group.get("items", []):
        description = item.get("description", "")
        # Truncate to 60 chars for label
        label = description[:60] + ("..." if len(description) > 60 else "")

        severity = item.get("severity", "low")
        file_path = item.get("file_path", "")
        line = item.get("line", "")
        source = item.get("source", "review")

        if source == "roadmap":
            desc_str = f"roadmap | Phase {item.get('phase', '?')} | From: {group_label}"
        else:
            loc = f"{file_path}:{line}" if file_path and line else (file_path or "")
            desc_str = f"{severity} | {loc} | From: {group_label}".strip(" |")

        options.append({
            "label": label,
            "description": desc_str,
            "_source_item": item
        })

print(json.dumps(options))
PYEOF
)

  ISSUE_COUNT=$(echo "$OPTIONS" | jq 'length')

  jq -n \
    --argjson options "$OPTIONS" \
    --argjson issue_count "$ISSUE_COUNT" \
    '{
      "question": "Select individual issues to create as tasks:",
      "header": "Issue Selection",
      "multiSelect": true,
      "options": ($options | map({
        "label": .label,
        "description": .description
      })),
      "_tier": 3,
      "_total_available": $issue_count,
      "_source_items": ($options | map(._source_item))
    }'
  exit 0
fi

# ─── No mode specified ────────────────────────────────────────────────────────

echo "Error: --mode (tier1|tier2|tier3) or --summarize is required" >&2
exit 1
