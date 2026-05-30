#!/usr/bin/env bash
# issue-grouping.sh - Group review issues into coherent task proposals
#
# Implements Steps 5.5.2-5.5.5 from /review command:
#   5.5.2 Extract grouping indicators
#   5.5.3 Clustering algorithm
#   5.5.4 Group post-processing
#   5.5.5 Score groups for ordering
#
# Usage:
#   echo "$issues_json" | bash issue-grouping.sh
#   bash issue-grouping.sh --file /path/to/issues.json
#
# Input:  JSON array of issue objects (via stdin or --file argument)
# Output: JSON array of grouped issues with scores to stdout
#
# Issue object schema:
#   {
#     "source": "review" | "roadmap",
#     "file_path": "path/to/file.lua" | null,
#     "line": 42 | null,
#     "severity": "critical" | "high" | "medium" | "low",
#     "priority": 1-4 | null,     (optional, derived from severity if absent)
#     "description": "text",
#     "phase": 1 | null,          (roadmap items only)
#     "item_text": "text" | null  (roadmap items only)
#   }
#
# Output schema:
#   [
#     {
#       "label": "src/plugins/ fixes",
#       "file_section": "src/plugins/",
#       "issue_type": "fix",
#       "priority": 3,
#       "key_terms": ["pattern", "match"],
#       "item_count": 2,
#       "severity_breakdown": {"critical": 0, "high": 2, "medium": 0, "low": 0},
#       "file_list": ["lsp.lua"],
#       "max_priority": 3,
#       "total_score": 11,
#       "items": [ ... original issue objects ... ]
#     }
#   ]

set -euo pipefail

# ─── Parse arguments ──────────────────────────────────────────────────────────

INPUT_FILE=""
while [[ $# -gt 0 ]]; do
  case "$1" in
    --file)
      INPUT_FILE="$2"
      shift 2
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
  ALL_ISSUES=$(cat "$INPUT_FILE")
else
  ALL_ISSUES=$(cat)
fi

# Validate input is a JSON array
if ! echo "$ALL_ISSUES" | jq -e 'type == "array"' > /dev/null 2>&1; then
  echo "Error: input must be a JSON array" >&2
  exit 1
fi

ISSUE_COUNT=$(echo "$ALL_ISSUES" | jq 'length')
if [[ "$ISSUE_COUNT" -eq 0 ]]; then
  echo "[]"
  exit 0
fi

# ─── Step 5.5.2: Extract grouping indicators ─────────────────────────────────
#
# Indicator extraction rules:
#   file_section: path prefix up to first-level directory
#                 "src/plugins/lsp.lua:42" -> "src/plugins/"
#                 null for roadmap items
#   issue_type:   Critical/High -> "fix", Medium -> "quality", Low -> "improvement"
#                 roadmap source -> "roadmap"
#   priority:     Critical=4, High=3, Medium=2, Low=1
#   key_terms:    significant words (>4 chars, not stopwords) from description

STOPWORDS="about above after again against before being between both could does down during each even ever from have here into itself just like made many more most must never only other over same should some such than that their them then there therefore these they this through under until upon very were what when which while with your"

# Build enriched issues with indicators using jq
ENRICHED=$(echo "$ALL_ISSUES" | jq --argjson stopwords "$(echo $STOPWORDS | jq -R 'split(" ")')" '
  def extract_file_section(fp):
    if fp == null then null
    else
      # Strip line number suffix (e.g., "file.lua:42" -> "file.lua")
      (fp | split(":")[0]) as $path |
      # Split path into parts
      ($path | split("/")) as $parts |
      if ($parts | length) > 1 then
        # Return prefix up to second-to-last component with trailing slash
        ([$parts[0:($parts | length - 1)][]] | join("/")) + "/"
      else
        ""
      end
    end;

  def severity_to_priority(sev):
    if sev == "critical" then 4
    elif sev == "high" then 3
    elif sev == "medium" then 2
    else 1
    end;

  def severity_to_issue_type(sev):
    if sev == "critical" or sev == "high" then "fix"
    elif sev == "medium" then "quality"
    else "improvement"
    end;

  def extract_key_terms(desc):
    # Split on non-word characters, lowercase, filter length > 4 and not stopwords
    (desc | ascii_downcase | gsub("[^a-z0-9 ]"; " ") | split(" ")) |
    map(select(length > 4)) |
    map(select(. as $w | $stopwords | map(. == $w) | any | not)) |
    unique;

  map(
    . as $issue |
    ($issue.severity // "low") as $sev |
    ($issue.source // "review") as $src |
    {
      "file_section": extract_file_section($issue.file_path),
      "issue_type": (if $src == "roadmap" then "roadmap" else severity_to_issue_type($sev) end),
      "priority": ($issue.priority // severity_to_priority($sev)),
      "key_terms": extract_key_terms($issue.description // ""),
      "original": $issue
    }
  )
')

# ─── Step 5.5.3: Clustering algorithm ────────────────────────────────────────
#
# Algorithm:
#   For each issue:
#     1. Primary match: same file_section AND same issue_type
#     2. Secondary match: 2+ shared key_terms AND same priority
#     3. No match: create new group

# Use Python for the stateful clustering algorithm (jq lacks mutation)
GROUPED=$(python3 - "$ENRICHED" << 'PYEOF'
import sys
import json

enriched = json.loads(sys.argv[1])
groups = []

for item in enriched:
    matched = False

    # Primary match: same file_section AND same issue_type
    for group in groups:
        if (item["file_section"] == group["file_section"] and
                item["issue_type"] == group["issue_type"]):
            group["items"].append(item["original"])
            # Update key_terms union
            group["key_terms"] = list(set(group["key_terms"]) | set(item["key_terms"]))
            # Update max priority
            if item["priority"] > group["priority"]:
                group["priority"] = item["priority"]
            matched = True
            break

    if not matched:
        # Secondary match: 2+ shared key_terms AND same priority
        for group in groups:
            shared = set(item["key_terms"]) & set(group["key_terms"])
            if len(shared) >= 2 and item["priority"] == group["priority"]:
                group["items"].append(item["original"])
                group["key_terms"] = list(set(group["key_terms"]) | set(item["key_terms"]))
                matched = True
                break

    if not matched:
        # No match: create new group
        groups.append({
            "file_section": item["file_section"],
            "issue_type": item["issue_type"],
            "priority": item["priority"],
            "key_terms": item["key_terms"],
            "items": [item["original"]]
        })

print(json.dumps(groups))
PYEOF
)

# ─── Step 5.5.4: Group post-processing ───────────────────────────────────────
#
# 1. Combine small groups (<2 items) into nearest match or "Other" group
# 2. Cap total groups at 10 (merge lowest-priority if exceeded)
# 3. Generate group labels
# 4. Calculate group metadata

POST_PROCESSED=$(python3 - "$GROUPED" << 'PYEOF'
import sys
import json

groups = json.loads(sys.argv[1])

# Step 1: Combine small groups (<2 items)
small_groups = [g for g in groups if len(g["items"]) < 2]
large_groups = [g for g in groups if len(g["items"]) >= 2]

for small in small_groups:
    # Try to merge into nearest large group by key_term overlap
    best_match = None
    best_overlap = 0
    for large in large_groups:
        overlap = len(set(small["key_terms"]) & set(large["key_terms"]))
        if overlap > best_overlap:
            best_overlap = overlap
            best_match = large

    if best_match is not None and best_overlap > 0:
        best_match["items"].extend(small["items"])
        best_match["key_terms"] = list(set(best_match["key_terms"]) | set(small["key_terms"]))
        if small["priority"] > best_match["priority"]:
            best_match["priority"] = small["priority"]
    else:
        # Find or create "Other" group for this issue_type
        other_key = "other_" + small["issue_type"]
        other_group = next((g for g in large_groups if g.get("_other_key") == other_key), None)
        if other_group is None:
            other_group = {
                "file_section": None,
                "issue_type": small["issue_type"],
                "priority": small["priority"],
                "key_terms": small["key_terms"],
                "items": [],
                "_other_key": other_key
            }
            large_groups.append(other_group)
        other_group["items"].extend(small["items"])
        other_group["key_terms"] = list(set(other_group["key_terms"]) | set(small["key_terms"]))
        if small["priority"] > other_group["priority"]:
            other_group["priority"] = small["priority"]

groups = large_groups

# Step 2: Cap total groups at 10
if len(groups) > 10:
    # Sort by priority descending, keep top 9, merge rest into "Other"
    groups.sort(key=lambda g: g["priority"], reverse=True)
    top_groups = groups[:9]
    overflow_groups = groups[9:]

    other_items = []
    other_terms = []
    other_priority = 0
    for g in overflow_groups:
        other_items.extend(g["items"])
        other_terms.extend(g["key_terms"])
        if g["priority"] > other_priority:
            other_priority = g["priority"]

    if other_items:
        top_groups.append({
            "file_section": None,
            "issue_type": "improvement",
            "priority": other_priority,
            "key_terms": list(set(other_terms)),
            "items": other_items
        })
    groups = top_groups

# Step 3 & 4: Generate labels and calculate metadata
def generate_label(group):
    issue_type = group["issue_type"]
    file_section = group["file_section"]

    # Check if all items are roadmap items
    all_roadmap = all(item.get("source") == "roadmap" for item in group["items"])
    if all_roadmap or issue_type == "roadmap":
        # Try to get phase name from items
        phases = [item.get("phase") for item in group["items"] if item.get("phase")]
        if phases:
            return f"Roadmap: Phase {phases[0]}"
        return "Roadmap items"

    # Pluralize issue_type correctly
    plural_map = {"fix": "fixes", "quality": "quality issues", "improvement": "improvements", "roadmap": "roadmap items"}
    type_label = plural_map.get(issue_type, issue_type + "s")

    if file_section:
        # Use directory name as prefix
        dir_name = file_section.rstrip("/").split("/")[-1] if file_section else ""
        if dir_name:
            return f"{dir_name} {type_label}"

    # Fall back to key terms
    if group["key_terms"]:
        term = group["key_terms"][0]
        return f"{term} issues"

    return f"Other {type_label}"

def build_severity_breakdown(items):
    breakdown = {"critical": 0, "high": 0, "medium": 0, "low": 0}
    for item in items:
        sev = item.get("severity", "low")
        if sev in breakdown:
            breakdown[sev] += 1
    return breakdown

def build_file_list(items):
    files = set()
    for item in items:
        fp = item.get("file_path")
        if fp:
            # Extract just filename
            base = fp.split(":")[0].split("/")[-1]
            if base:
                files.add(base)
    return sorted(list(files))

result = []
for group in groups:
    severity_breakdown = build_severity_breakdown(group["items"])
    file_list = build_file_list(group["items"])
    max_priority = max((item.get("priority", 1) for item in group["items"]), default=group["priority"])

    result.append({
        "label": generate_label(group),
        "file_section": group["file_section"],
        "issue_type": group["issue_type"],
        "priority": group["priority"],
        "key_terms": group["key_terms"][:10],  # cap key_terms list
        "item_count": len(group["items"]),
        "severity_breakdown": severity_breakdown,
        "file_list": file_list,
        "max_priority": max_priority,
        "total_score": 0,  # filled in step 5.5.5
        "items": group["items"]
    })

print(json.dumps(result))
PYEOF
)

# ─── Step 5.5.5: Score groups for ordering ───────────────────────────────────
#
# Scoring factors:
#   Contains critical issue:       +10
#   Contains high issue:           +5
#   Group max priority Critical:   +8
#   Group max priority High:       +6
#   Group max priority Medium:     +4
#   Group max priority Low:        +2
#   Number of items (capped at 5): +N
#   Roadmap "Near Term" items:     +3 (roadmap source with phase 1)

SCORED=$(echo "$POST_PROCESSED" | jq '
  map(
    . as $group |
    # Calculate score
    (
      # Contains critical?
      (if ($group.severity_breakdown.critical // 0) > 0 then 10 else 0 end) +
      # Contains high?
      (if ($group.severity_breakdown.high // 0) > 0 then 5 else 0 end) +
      # Max priority bonus
      (if $group.max_priority == 4 then 8
       elif $group.max_priority == 3 then 6
       elif $group.max_priority == 2 then 4
       else 2
       end) +
      # Item count (capped at 5)
      ([$group.item_count, 5] | min) +
      # Roadmap near-term bonus (phase 1 items)
      (if $group.issue_type == "roadmap" then
        ($group.items | map(select(.phase == 1)) | length) * 3
       else 0
       end)
    ) as $score |
    $group | .total_score = $score
  ) |
  # Sort by descending score
  sort_by(-.total_score)
')

echo "$SCORED"
