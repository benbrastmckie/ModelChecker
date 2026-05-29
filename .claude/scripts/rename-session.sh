#!/usr/bin/env bash
# Rename the active OpenCode session in the current TUI instance.
# Usage: rename-session.sh "New Title"
# Discovers the TUI port via ss, finds the busy session, PATCHes the title.
# No-op when no OpenCode TUI is running (safe to call from Claude Code context).
set -euo pipefail

title="${1:-}"
if [ -z "$title" ]; then
  echo "Usage: rename-session.sh \"New Title\"" >&2
  exit 1
fi

cwd="$(pwd)"

# Find TUI port matching current working directory
port=""
while IFS= read -r line; do
  p=$(echo "$line" | grep -oP ':\K\d+(?=\s)')
  pid=$(echo "$line" | grep -oP 'pid=\K\d+')
  [ -z "$p" ] || [ -z "$pid" ] && continue
  proc_cwd=$(readlink -f "/proc/$pid/cwd" 2>/dev/null) || continue
  proc_cmd=$(tr '\0' ' ' < "/proc/$pid/cmdline" 2>/dev/null) || continue
  echo "$proc_cmd" | grep -q "serve" && continue
  if [ "$proc_cwd" = "$cwd" ]; then
    port="$p"
    break
  fi
  [ -z "$port" ] && port="$p"
done < <(ss -tlnp 2>/dev/null | grep opencode)

if [ -z "$port" ]; then
  exit 0
fi

base="http://127.0.0.1:${port}"

# Find the busy session (the one running this command)
busy_id=$(curl -sf "${base}/session/status" 2>/dev/null \
  | python3 -c "
import sys, json
data = json.load(sys.stdin)
for sid, info in data.items():
    if isinstance(info, dict) and info.get('type') == 'busy':
        print(sid)
        break
" 2>/dev/null) || true

if [ -z "$busy_id" ]; then
  busy_id=$(curl -sf "${base}/session" 2>/dev/null \
    | python3 -c "
import sys, json
data = json.load(sys.stdin)
if isinstance(data, list) and data:
    best = max(data, key=lambda s: (s.get('time',{}).get('updated',0)))
    print(best['id'])
" 2>/dev/null) || true
fi

if [ -z "$busy_id" ]; then
  exit 0
fi

json_body=$(python3 -c "import json,sys; print(json.dumps({'title': sys.argv[1]}))" "$title")
curl -sf -X PATCH "${base}/session/${busy_id}" \
  -H "Content-Type: application/json" \
  -d "$json_body" \
  >/dev/null 2>&1 || true
