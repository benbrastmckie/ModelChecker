---
name: skill-lean-research
description: Research Lean 4 and Mathlib for theorem proving tasks. Invoke for Lean-language research using LeanSearch, Loogle, and lean-lsp tools.
allowed-tools: Read, Write, Edit, Glob, Grep, mcp__lean-lsp__lean_leansearch, mcp__lean-lsp__lean_loogle, mcp__lean-lsp__lean_leanfinder, mcp__lean-lsp__lean_local_search, mcp__lean-lsp__lean_hover_info
context: fork
---

# Lean Research Skill

Specialized research agent for Lean 4 theorem proving tasks.

## Trigger Conditions

This skill activates when:
- Task language is "lean"
- Research involves Mathlib, theorems, or proofs
- Lean-specific tools are needed

## Research Tools

### lean_leansearch (3 req/30s)
Natural language → Mathlib theorems
```
Query: "sum of two even numbers is even"
Returns: Relevant theorem names and signatures
```

### lean_loogle (3 req/30s)
Type pattern → Mathlib lemmas
```
Query: "(?a → ?b) → List ?a → List ?b"
Returns: Matching type signatures
```

### lean_leanfinder (10 req/30s)
Semantic/conceptual search
```
Query: "commutativity of addition on natural numbers"
Returns: Conceptually related theorems
```

### lean_local_search
Fast local declaration search
```
Query: "Frame"
Returns: Local project declarations matching name
```

### lean_hover_info
Get type signature and documentation
```
Position: file:line:column
Returns: Full type and docstring
```

## Research Strategy

### 1. Local First
Always check local project first:
```
1. lean_local_search for existing definitions
2. Grep for related code
3. Read relevant .lean files
```

### 2. Mathlib Search
Search Mathlib for relevant theorems:
```
1. lean_leansearch for natural language queries
2. lean_loogle for type patterns
3. lean_leanfinder for concepts
```

### 3. Verify Findings
Confirm found theorems exist and are applicable:
```
1. lean_local_search to verify names
2. lean_hover_info for full signatures
```

## Execution Flow

```
1. Receive task context (description, focus)
2. Extract key concepts (theorems, types, properties)
3. Search local project for related code
4. Search Mathlib using appropriate tools
5. Verify findings with hover_info
6. Analyze proof patterns
7. Create research report
8. Return results
```

## Research Report Format

```markdown
# Lean Research Report: Task #{N}

**Task**: {title}
**Date**: {date}
**Focus**: {focus}

## Summary

{Overview of findings}

## Local Project Findings

### Related Definitions
- `Namespace.Definition` - {description}

### Related Theorems
- `Namespace.theorem_name` - {what it proves}

## Mathlib Findings

### Relevant Theorems
| Name | Type | Relevance |
|------|------|-----------|
| `Theorem.name` | `Type` | {why useful} |

### Proof Patterns
{Common patterns found in similar proofs}

### Required Imports
```lean
import Mathlib.Tactic
import Mathlib.{Specific.Module}
```

## Recommended Approach

1. {Step 1 with specific theorems to use}
2. {Step 2}

## Proof Sketch

```lean
theorem target_theorem : Statement := by
  -- Use {theorem1} for first step
  -- Apply {theorem2} to transform
  -- Finish with {tactic}
```

## Potential Challenges

- {Challenge and how to address}

## References

- {Mathlib doc links}
```

## Return Format

```json
{
  "status": "completed",
  "summary": "Found N relevant theorems for proof",
  "artifacts": [
    {
      "path": ".claude/specs/{N}_{SLUG}/reports/research-001.md",
      "type": "research",
      "description": "Lean research report"
    }
  ],
  "theorems_found": [
    {"name": "Theorem.name", "relevance": "high"}
  ],
  "imports_needed": [
    "Mathlib.Specific.Module"
  ],
  "proof_approach": "Description of recommended approach"
}
```
