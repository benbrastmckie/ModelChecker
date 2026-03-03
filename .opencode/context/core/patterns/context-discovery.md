# Context Discovery Patterns

Machine-readable context discovery via `index.json` queries.

## jq Query Patterns

### Find Context by Agent

```bash
jq -r '.entries[] | select(.load_when.agents[]? == "lean-implementation-agent") | .path' .opencode/context/index.json
```

### Find Context by Language

```bash
jq -r '.entries[] | select(.load_when.languages[]? == "lean4") | .path' .opencode/context/index.json
```

### Find Context by Command

```bash
jq -r '.entries[] | select(.load_when.commands[]? == "/implement") | .path' .opencode/context/index.json
```

### Get Line Counts for Budget Calculation

```bash
jq -r '.entries[] | select(.load_when.agents[]? == "planner-agent") | "\(.line_count)\t\(.path)"' .opencode/context/index.json
```

### Find Always-Loaded Context

```bash
jq -r '.entries[] | select(.load_when.always == true) | .path' .opencode/context/index.json
```

## Index Entry Schema

Each entry in `index.json` follows this schema:

```json
{
  "path": "relative/path/to/file.md",
  "domain": "core|project",
  "subdomain": "orchestration|patterns|lean4|etc",
  "topics": ["topic1", "topic2"],
  "keywords": ["keyword1", "keyword2"],
  "summary": "One-line description",
  "line_count": 150,
  "load_when": {
    "agents": ["agent-name"],
    "commands": ["/command"],
    "languages": ["language"],
    "always": false
  }
}
```

## Usage in Agents

Agents should query the index at startup to discover relevant context:

1. Query by agent name to find directly-relevant context
2. Query by language if task language is known
3. Sum line counts to stay within context budget
4. Load files in priority order (always-loaded first, then agent-specific)
