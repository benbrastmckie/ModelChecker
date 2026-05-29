#!/usr/bin/env bash
# validate-context-budgets.sh
# Validates agent context budgets against tier caps for index.json
#
# Usage: validate-context-budgets.sh [--verbose] [--index PATH]
#
# Exit codes:
#   0 - All agents within budget (or documented exceptions only)
#   1 - One or more agents exceed budget cap without documented exception

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"
INDEX_FILE="${REPO_ROOT}/.claude/context/index.json"
VERBOSE=false
VIOLATIONS=0
WARNINGS=0

# Parse arguments
while [[ $# -gt 0 ]]; do
  case "$1" in
    --verbose) VERBOSE=true; shift ;;
    --index) INDEX_FILE="$2"; shift 2 ;;
    --help)
      echo "Usage: $0 [--verbose] [--index PATH]"
      echo ""
      echo "Validates agent context budgets against tier caps."
      echo "Reads index.json and computes per-agent token totals."
      echo ""
      echo "Options:"
      echo "  --verbose    List all entries per agent"
      echo "  --index PATH Path to index.json (default: .claude/context/index.json)"
      exit 0
      ;;
    *) echo "Unknown argument: $1"; exit 1 ;;
  esac
done

if [[ ! -f "$INDEX_FILE" ]]; then
  echo "ERROR: index.json not found at $INDEX_FILE" >&2
  exit 1
fi

# Verify JSON validity
if ! jq empty "$INDEX_FILE" 2>/dev/null; then
  echo "ERROR: index.json is not valid JSON" >&2
  exit 1
fi

echo "=== Context Budget Validation ==="
echo "Index: $INDEX_FILE"
echo ""

# Budget caps per agent class (tokens)
declare -A CAPS=(
  ["meta-builder-agent"]=15000
  ["planner-agent"]=15000
  ["general-implementation-agent"]=8000
  ["general-research-agent"]=8000
  ["neovim-implementation-agent"]=8000
  ["neovim-research-agent"]=8000
  ["nix-implementation-agent"]=8000
  ["nix-research-agent"]=8000
  ["code-reviewer-agent"]=8000
  ["spawn-agent"]=8000
)

# Documented exceptions (agents that cannot meet strict cap with minimum essential context)
# Format: agent=actual_realistic_cap (with justification)
declare -A EXCEPTIONS=(
  ["general-implementation-agent"]="8048:return-metadata-file(4016)+checkpoint-execution(2032)+progress-file(2000) is minimum irreducible set"
)

echo "--- Agent Budget Check ---"
printf "%-35s %8s %8s %12s\n" "Agent" "Tokens" "Cap" "Status"
printf "%s\n" "$(printf '%.0s-' {1..67})"

for agent in "${!CAPS[@]}"; do
  cap="${CAPS[$agent]}"

  # Compute total tokens for this agent
  total=$(jq --arg agent "$agent" \
    '[.entries[] | select(any(.load_when.agents[]?; . == $agent)) | .line_count] | add // 0' \
    "$INDEX_FILE")
  total_tokens=$((total * 8))

  # Check for documented exception
  exception=""
  if [[ -v "EXCEPTIONS[$agent]" ]]; then
    exception_data="${EXCEPTIONS[$agent]}"
    exception_cap="${exception_data%%:*}"
    exception_reason="${exception_data#*:}"
    exception="(exception: $exception_reason)"
  fi

  if [[ $total_tokens -le $cap ]]; then
    status="OK"
    printf "%-35s %8s %8s %12s\n" "$agent" "$total_tokens" "$cap" "OK"
  elif [[ -n "$exception" && $total_tokens -le "${exception_cap:-0}" ]]; then
    status="OK (exception)"
    printf "%-35s %8s %8s %12s\n" "$agent" "$total_tokens" "$cap" "OK*"
    WARNINGS=$((WARNINGS + 1))
    if [[ "$VERBOSE" == "true" ]]; then
      echo "    * Documented exception: $exception_reason"
    fi
  else
    status="OVER by $((total_tokens - cap))"
    printf "%-35s %8s %8s %12s\n" "$agent" "$total_tokens" "$cap" "OVER:$((total_tokens - cap))"
    VIOLATIONS=$((VIOLATIONS + 1))
  fi

  if [[ "$VERBOSE" == "true" ]]; then
    echo "  Entries for $agent:"
    jq -r --arg agent "$agent" \
      '.entries[] | select(any(.load_when.agents[]?; . == $agent)) | "    Tier \(.tier // "?") \(.line_count * 8) tok  \(.path)"' \
      "$INDEX_FILE" | sort -t' ' -k3 -rn
    echo ""
  fi
done

echo ""

# Tier 1 check
echo "--- Tier 1 Check ---"
tier1_lines=$(jq '[.entries[] | select(.load_when.always == true) | .line_count] | add // 0' "$INDEX_FILE")
tier1_count=$(jq '[.entries[] | select(.load_when.always == true)] | length' "$INDEX_FILE")
tier1_target=500
echo "Always-loaded entries: $tier1_count (target: 2)"
echo "Always-loaded total lines: $tier1_lines (target: ≤$tier1_target)"
if [[ $tier1_lines -le $tier1_target ]]; then
  echo "Status: OK"
else
  echo "Status: OVER by $((tier1_lines - tier1_target)) lines"
  VIOLATIONS=$((VIOLATIONS + 1))
fi
if [[ "$VERBOSE" == "true" ]]; then
  echo "Tier 1 entries:"
  jq -r '.entries[] | select(.load_when.always == true) | "  \(.line_count)L  \(.path)"' "$INDEX_FILE"
fi
echo ""

# All entries have tier field
echo "--- Tier Classification Check ---"
missing_tier=$(jq '[.entries[] | select(.tier == null)] | length' "$INDEX_FILE")
total_entries=$(jq '.entries | length' "$INDEX_FILE")
echo "Total entries: $total_entries"
echo "Entries with tier field: $((total_entries - missing_tier))"
if [[ $missing_tier -eq 0 ]]; then
  echo "Status: OK (all entries have tier)"
else
  echo "Status: FAIL ($missing_tier entries missing tier field)"
  VIOLATIONS=$((VIOLATIONS + 1))
  if [[ "$VERBOSE" == "true" ]]; then
    echo "Missing tier:"
    jq -r '.entries[] | select(.tier == null) | "  \(.path)"' "$INDEX_FILE"
  fi
fi
echo ""

# No dead entries (never-loaded, not Tier 4)
# Dead = not Tier 4, not always-loaded, no agents, no commands, no task_types, no skills, no languages
echo "--- Dead Entry Check ---"
dead_count=$(jq '
  [.entries[] | select(
    .tier != 4 and
    (.load_when.always == false or (.load_when.always == null)) and
    ((.load_when.agents // []) | length) == 0 and
    ((.load_when.commands // []) | length) == 0 and
    ((.load_when.task_types // []) | length) == 0 and
    ((.load_when.skills // []) | length) == 0 and
    ((.load_when.languages // []) | length) == 0
  )] | length' "$INDEX_FILE")
if [[ $dead_count -eq 0 ]]; then
  echo "Dead entries (never auto-loaded, not Tier 4): 0 -- OK"
else
  echo "Dead entries found: $dead_count"
  VIOLATIONS=$((VIOLATIONS + 1))
  jq -r '
    .entries[] | select(
      .tier != 4 and
      (.load_when.always == false or (.load_when.always == null)) and
      ((.load_when.agents // []) | length) == 0 and
      ((.load_when.commands // []) | length) == 0 and
      ((.load_when.task_types // []) | length) == 0 and
      ((.load_when.skills // []) | length) == 0 and
      ((.load_when.languages // []) | length) == 0
    ) | "  \(.path) (Tier \(.tier // "?"))"' "$INDEX_FILE"
fi
echo ""

# No Tier 3 entries with both agents AND commands
echo "--- Double-Loading Check ---"
double_loaded=$(jq '[.entries[] | select(.tier == 3 and (.load_when.agents | length) > 0 and (.load_when.commands | length) > 0)] | length' "$INDEX_FILE")
if [[ $double_loaded -eq 0 ]]; then
  echo "Tier 3 entries with both agents and commands: 0 -- OK"
else
  echo "Double-loaded Tier 3 entries: $double_loaded (VIOLATION)"
  VIOLATIONS=$((VIOLATIONS + 1))
  if [[ "$VERBOSE" == "true" ]]; then
    jq -r '.entries[] | select(.tier == 3 and (.load_when.agents | length) > 0 and (.load_when.commands | length) > 0) | "  \(.path)"' "$INDEX_FILE"
  fi
fi
echo ""

# Summary
echo "=== Summary ==="
echo "Violations: $VIOLATIONS"
if [[ $WARNINGS -gt 0 ]]; then
  echo "Documented exceptions: $WARNINGS (OK* entries)"
  echo "  * general-implementation-agent: 8,048 tokens vs 8,000 cap"
  echo "    Minimum essential set cannot be reduced below this value:"
  echo "    - formats/return-metadata-file.md (4,016 tok) -- critical for all subagents"
  echo "    - patterns/checkpoint-execution.md (2,032 tok) -- critical for phase tracking"
  echo "    - formats/progress-file.md (2,000 tok) -- critical for resumable execution"
fi

if [[ $VIOLATIONS -eq 0 ]]; then
  echo ""
  echo "All checks passed!"
  exit 0
else
  echo ""
  echo "FAIL: $VIOLATIONS violation(s) found"
  exit 1
fi
