#!/usr/bin/env bash
# roadmap-integration.sh - Parse ROADMAP.md, cross-reference with state, annotate completed items
#
# Implements Steps 2.5-2.5.3 from /review command:
#   2.5   Parse ROADMAP.md
#   2.5.2 Cross-reference roadmap with project state
#   2.5.3 Annotate completed roadmap items
#
# Usage:
#   bash roadmap-integration.sh --roadmap specs/ROADMAP.md --state specs/state.json
#   bash roadmap-integration.sh --roadmap specs/ROADMAP.md --state specs/state.json --annotate
#
# Options:
#   --roadmap PATH    Path to ROADMAP.md (required)
#   --state PATH      Path to state.json (required)
#   --annotate        Apply high-confidence annotations to ROADMAP.md (default: parse only)
#   --dry-run         Show what annotations would be made without applying them
#
# Output:
#   JSON object with roadmap_state and roadmap_matches to stdout
#   If --annotate: also applies edits to ROADMAP.md and prints annotation summary to stderr
#
# Output schema:
#   {
#     "roadmap_state": {
#       "phases": [...],
#       "status_tables": [...]
#     },
#     "roadmap_matches": [...],
#     "annotation_summary": {
#       "annotations_made": 0,
#       "items_skipped": 0,
#       "skipped_reasons": []
#     }
#   }

set -euo pipefail

# ─── Parse arguments ──────────────────────────────────────────────────────────

ROADMAP_PATH=""
STATE_PATH=""
DO_ANNOTATE=false
DRY_RUN=false

while [[ $# -gt 0 ]]; do
  case "$1" in
    --roadmap)
      ROADMAP_PATH="$2"
      shift 2
      ;;
    --state)
      STATE_PATH="$2"
      shift 2
      ;;
    --annotate)
      DO_ANNOTATE=true
      shift
      ;;
    --dry-run)
      DRY_RUN=true
      DO_ANNOTATE=true
      shift
      ;;
    *)
      echo "Unknown argument: $1" >&2
      exit 1
      ;;
  esac
done

if [[ -z "$ROADMAP_PATH" ]]; then
  echo "Error: --roadmap is required" >&2
  exit 1
fi

if [[ -z "$STATE_PATH" ]]; then
  echo "Error: --state is required" >&2
  exit 1
fi

# ─── Ensure ROADMAP.md exists ────────────────────────────────────────────────

if [[ ! -f "$ROADMAP_PATH" ]]; then
  echo "Note: ROADMAP.md not found at $ROADMAP_PATH, creating default template" >&2
  mkdir -p "$(dirname "$ROADMAP_PATH")"
  cat > "$ROADMAP_PATH" << 'TEMPLATE'
# Project Roadmap

## Phase 1: Current Priorities (High Priority)

- [ ] (No items yet -- add roadmap items here)

## Success Metrics

- (Define success metrics here)
TEMPLATE
fi

if [[ ! -f "$STATE_PATH" ]]; then
  echo "Error: state.json not found at $STATE_PATH" >&2
  exit 1
fi

# ─── Step 2.5: Parse ROADMAP.md ──────────────────────────────────────────────
#
# Extract:
#   Phase headers: ## Phase {N}: {Title} ({Priority})
#   Checkboxes: - [ ] (incomplete) and - [x] (complete)
#   Status tables: pipe-delimited rows with Component/Status/Location
#   Priority markers: (High Priority), (Medium Priority), (Low Priority)

ROADMAP_CONTENT=$(cat "$ROADMAP_PATH")

ROADMAP_STATE=$(python3 - "$ROADMAP_CONTENT" << 'PYEOF'
import sys
import re
import json

content = sys.argv[1]
lines = content.split("\n")

phases = []
status_tables = []
current_phase = None
in_table = False
table_headers = []

for i, line in enumerate(lines):
    # Match phase headers: ## Phase N: Title (Priority)
    phase_match = re.match(r'^## Phase (\d+): (.+?)(?:\s+\((\w+ Priority)\))?$', line)
    if phase_match:
        if current_phase is not None:
            phases.append(current_phase)
        priority_text = phase_match.group(3) or ""
        priority = (priority_text.split()[0] if priority_text else "Medium")
        current_phase = {
            "number": int(phase_match.group(1)),
            "title": phase_match.group(2).strip(),
            "priority": priority,
            "checkboxes": {
                "total": 0,
                "completed": 0,
                "items": []
            }
        }
        in_table = False
        continue

    # Match checkboxes: - [ ] text or - [x] text
    if current_phase is not None:
        checkbox_match = re.match(r'^- \[([ xX])\] (.+)$', line)
        if checkbox_match:
            is_completed = checkbox_match.group(1).lower() == 'x'
            text = checkbox_match.group(2).strip()
            current_phase["checkboxes"]["total"] += 1
            if is_completed:
                current_phase["checkboxes"]["completed"] += 1
            current_phase["checkboxes"]["items"].append({
                "text": text,
                "completed": is_completed
            })
            continue

    # Match status table rows: | **Component** | Status | Location |
    table_row_match = re.match(r'^\|(.+)\|(.+)\|(.+)\|$', line)
    if table_row_match:
        cols = [c.strip() for c in [table_row_match.group(1), table_row_match.group(2), table_row_match.group(3)]]
        # Skip separator rows (--- cells)
        if all(re.match(r'^-+$', c.strip('-')) or c.strip('-') == '' for c in cols):
            continue
        # Skip header rows
        if 'component' in cols[0].lower() or 'status' in cols[1].lower():
            table_headers = cols
            in_table = True
            continue
        if in_table:
            # Strip markdown bold from component name
            component = re.sub(r'\*\*(.+)\*\*', r'\1', cols[0])
            status_tables.append({
                "component": component,
                "status": cols[1],
                "location": cols[2] if len(cols) > 2 else ""
            })
    else:
        in_table = False

# Add last phase
if current_phase is not None:
    phases.append(current_phase)

result = {
    "phases": phases,
    "status_tables": status_tables
}
print(json.dumps(result))
PYEOF
)

# ─── Step 2.5.2: Cross-reference roadmap with project state ──────────────────
#
# Match roadmap items to completed tasks using:
#   1. Item contains (Task N) reference    -> High confidence, auto-annotate
#   2. Item text matches task title        -> Medium confidence, suggest annotation
#   3. Item's file path exists             -> Medium confidence, suggest annotation
#   4. Partial keyword match               -> Low confidence, report only

# Get completed tasks from state.json
COMPLETED_TASKS=$(jq -r '
  .active_projects[] | select(.status == "completed") |
  {
    "number": .project_number,
    "name": .project_name,
    "title": (.description // .project_name),
    "completion_summary": (.completion_summary // ""),
    "roadmap_items": (.roadmap_items // [])
  }
' "$STATE_PATH" 2>/dev/null | jq -s '.' 2>/dev/null || echo "[]")

# Check archive/state.json too if it exists
ARCHIVE_STATE="${STATE_PATH%state.json}archive/state.json"
ARCHIVED_TASKS="[]"
if [[ -f "$ARCHIVE_STATE" ]]; then
  ARCHIVED_TASKS=$(jq -r '
    .completed_projects[] | select(.status == "completed") |
    {
      "number": .project_number,
      "name": .project_name,
      "title": (.description // .project_name),
      "completion_summary": (.completion_summary // ""),
      "roadmap_items": (.roadmap_items // [])
    }
  ' "$ARCHIVE_STATE" 2>/dev/null | jq -s '.' 2>/dev/null || echo "[]")
fi

ALL_COMPLETED=$(echo "$COMPLETED_TASKS $ARCHIVED_TASKS" | jq -s 'add // []')

ROADMAP_MATCHES=$(python3 - "$ROADMAP_STATE" "$ALL_COMPLETED" << 'PYEOF'
import sys
import re
import json

roadmap_state = json.loads(sys.argv[1])
all_completed = json.loads(sys.argv[2])

matches = []

# Build lookup for task by number and by name/title keywords
task_by_number = {}
for task in all_completed:
    task_by_number[task["number"]] = task

def normalize(text):
    """Lowercase and strip punctuation for fuzzy matching."""
    return re.sub(r'[^a-z0-9 ]', ' ', text.lower()).strip()

def keywords(text):
    """Extract significant keywords (>3 chars) from text."""
    words = normalize(text).split()
    stopwords = {'with', 'from', 'that', 'this', 'have', 'been', 'will', 'also', 'into', 'than'}
    return set(w for w in words if len(w) > 3 and w not in stopwords)

for phase in roadmap_state.get("phases", []):
    for item in phase.get("checkboxes", {}).get("items", []):
        item_text = item["text"]
        item_norm = normalize(item_text)
        item_kw = keywords(item_text)

        # Skip already-annotated items (contain "*(Completed:")
        if "*(Completed:" in item_text or "(Completed:" in item_text:
            continue

        # Skip already completed items
        if item.get("completed", False):
            continue

        best_match = None
        best_confidence = None
        best_match_type = None

        # Check 1: Does item contain explicit (Task N) reference?
        task_ref = re.search(r'\(Task (\d+)\)', item_text)
        if task_ref:
            task_num = int(task_ref.group(1))
            if task_num in task_by_number:
                best_match = task_by_number[task_num]
                best_confidence = "high"
                best_match_type = "explicit_task_ref"

        # Check 2: Does completed task have explicit roadmap_items?
        if best_match is None:
            for task in all_completed:
                for ri in task.get("roadmap_items", []):
                    ri_norm = normalize(ri)
                    if ri_norm == item_norm or (len(ri_norm) > 10 and ri_norm in item_norm):
                        best_match = task
                        best_confidence = "high"
                        best_match_type = "explicit_roadmap_item"
                        break
                if best_match:
                    break

        # Check 3: Title match (exact or near-exact)
        if best_match is None:
            for task in all_completed:
                task_title_norm = normalize(task["title"])
                if task_title_norm == item_norm:
                    best_match = task
                    best_confidence = "high"
                    best_match_type = "exact_title_match"
                    break
                # Near-exact: one is a substring of the other
                if len(task_title_norm) > 10:
                    if task_title_norm in item_norm or item_norm in task_title_norm:
                        best_match = task
                        best_confidence = "medium"
                        best_match_type = "title_match"
                        break

        # Check 4: Keyword match (60%+ overlap)
        if best_match is None and len(item_kw) >= 3:
            best_overlap = 0
            for task in all_completed:
                task_kw = keywords(task["title"] + " " + task.get("completion_summary", ""))
                overlap = len(item_kw & task_kw)
                overlap_ratio = overlap / len(item_kw)
                if overlap_ratio >= 0.6 and overlap > best_overlap:
                    best_overlap = overlap
                    best_match = task
                    best_confidence = "low"
                    best_match_type = "keyword_match"

        if best_match is not None:
            # Find completion date (use a placeholder since state.json may not track dates)
            completion_date = best_match.get("completion_date", "")
            if not completion_date:
                # Try to infer from task creation date or use empty
                completion_date = ""

            matches.append({
                "roadmap_item": item_text,
                "phase": phase["number"],
                "match_type": best_match_type,
                "confidence": best_confidence,
                "matched_task": best_match["number"],
                "task_title": best_match["title"],
                "completion_date": completion_date
            })

print(json.dumps(matches))
PYEOF
)

# ─── Step 2.5.3: Annotate completed roadmap items ────────────────────────────
#
# Annotation format:
#   - [x] {item text} *(Completed: Task {N}, {DATE})*
#
# Safety rules:
#   - Skip items already annotated (contain "*(Completed:")
#   - Preserve existing formatting and indentation
#   - One edit per item (no batch edits)
#   - Only high-confidence matches auto-annotate

ANNOTATIONS_MADE=0
ITEMS_SKIPPED=0
SKIPPED_REASONS=()

if [[ "$DO_ANNOTATE" == "true" ]]; then
  # Process high-confidence matches
  HIGH_CONF_MATCHES=$(echo "$ROADMAP_MATCHES" | jq '[.[] | select(.confidence == "high")]')
  MATCH_COUNT=$(echo "$HIGH_CONF_MATCHES" | jq 'length')

  for i in $(seq 0 $((MATCH_COUNT - 1))); do
    MATCH=$(echo "$HIGH_CONF_MATCHES" | jq ".[$i]")
    ITEM_TEXT=$(echo "$MATCH" | jq -r '.roadmap_item')
    TASK_NUM=$(echo "$MATCH" | jq -r '.matched_task')
    COMPLETION_DATE=$(echo "$MATCH" | jq -r '.completion_date // ""')

    # Safety check: skip if already annotated
    if grep -q "*(Completed:" "$ROADMAP_PATH" 2>/dev/null && \
       grep -q "$ITEM_TEXT" "$ROADMAP_PATH" 2>/dev/null; then
      # Check if this specific line is already annotated
      MATCHING_LINE=$(grep -F "$ITEM_TEXT" "$ROADMAP_PATH" 2>/dev/null | head -1)
      if echo "$MATCHING_LINE" | grep -q "*(Completed:"; then
        ITEMS_SKIPPED=$((ITEMS_SKIPPED + 1))
        SKIPPED_REASONS+=("already_annotated")
        continue
      fi
    fi

    # Build annotation suffix
    if [[ -n "$COMPLETION_DATE" ]]; then
      ANNOTATION_SUFFIX="*(Completed: Task $TASK_NUM, $COMPLETION_DATE)*"
    else
      ANNOTATION_SUFFIX="*(Completed: Task $TASK_NUM)*"
    fi

    # Build old and new strings for sed substitution
    OLD_LINE="- [ ] $ITEM_TEXT"
    NEW_LINE="- [x] $ITEM_TEXT $ANNOTATION_SUFFIX"

    if [[ "$DRY_RUN" == "true" ]]; then
      echo "[dry-run] Would annotate: $OLD_LINE" >&2
      echo "[dry-run]           with: $NEW_LINE" >&2
      ANNOTATIONS_MADE=$((ANNOTATIONS_MADE + 1))
    else
      # Apply annotation: replace first occurrence of the unchecked item
      # Use a temp file to avoid in-place issues
      TMPFILE=$(mktemp)
      # Replace only the first match of this exact line
      awk -v old="$OLD_LINE" -v new="$NEW_LINE" '
        !replaced && $0 == old {
          print new
          replaced = 1
          next
        }
        { print }
      ' "$ROADMAP_PATH" > "$TMPFILE"

      if diff -q "$TMPFILE" "$ROADMAP_PATH" > /dev/null 2>&1; then
        # No change was made (line not found as exact match)
        ITEMS_SKIPPED=$((ITEMS_SKIPPED + 1))
        SKIPPED_REASONS+=("line_not_found_exact")
        rm -f "$TMPFILE"
      else
        mv "$TMPFILE" "$ROADMAP_PATH"
        ANNOTATIONS_MADE=$((ANNOTATIONS_MADE + 1))
        echo "Annotated: Task $TASK_NUM -> $ITEM_TEXT" >&2
      fi
    fi
  done

  # Report skipped medium/low confidence matches
  MEDIUM_LOW_COUNT=$(echo "$ROADMAP_MATCHES" | jq '[.[] | select(.confidence == "medium" or .confidence == "low")] | length')
  if [[ "$MEDIUM_LOW_COUNT" -gt 0 ]]; then
    ITEMS_SKIPPED=$((ITEMS_SKIPPED + MEDIUM_LOW_COUNT))
    for i in $(seq 0 $((MEDIUM_LOW_COUNT - 1))); do
      SKIPPED_REASONS+=("low_confidence")
    done
  fi
fi

# ─── Build output JSON ────────────────────────────────────────────────────────

if [[ ${#SKIPPED_REASONS[@]} -eq 0 ]]; then
  SKIPPED_REASONS_JSON="[]"
else
  SKIPPED_REASONS_JSON=$(printf '%s\n' "${SKIPPED_REASONS[@]}" | jq -R . | jq -s .)
fi

jq -n \
  --argjson roadmap_state "$ROADMAP_STATE" \
  --argjson roadmap_matches "$ROADMAP_MATCHES" \
  --argjson annotations_made "$ANNOTATIONS_MADE" \
  --argjson items_skipped "$ITEMS_SKIPPED" \
  --argjson skipped_reasons "$SKIPPED_REASONS_JSON" \
  '{
    "roadmap_state": $roadmap_state,
    "roadmap_matches": $roadmap_matches,
    "annotation_summary": {
      "annotations_made": $annotations_made,
      "items_skipped": $items_skipped,
      "skipped_reasons": $skipped_reasons
    }
  }'
