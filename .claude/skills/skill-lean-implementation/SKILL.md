---
name: skill-lean-implementation
description: Implement Lean 4 proofs and definitions using lean-lsp tools. Invoke for Lean-language implementation tasks.
allowed-tools: Read, Write, Edit, Glob, Grep, Bash(lake *), mcp__lean-lsp__lean_goal, mcp__lean-lsp__lean_diagnostic_messages, mcp__lean-lsp__lean_hover_info, mcp__lean-lsp__lean_completions, mcp__lean-lsp__lean_multi_attempt, mcp__lean-lsp__lean_local_search
context: fork
---

# Lean Implementation Skill

Execute Lean 4 theorem proving and definition implementation.

## Trigger Conditions

This skill activates when:
- Task language is "lean"
- /implement command targets a Lean task
- Proofs or definitions need to be written

## Core Tools

### lean_goal (Use Constantly!)
Check proof state at position:
```
Omit column for before/after comparison
"no goals" = proof complete
```

### lean_diagnostic_messages
Get compiler errors/warnings:
```
Check after every edit
"no goals to be solved" = remove tactics
```

### lean_hover_info
Type signatures and docs:
```
Column at START of identifier
Essential for understanding APIs
```

### lean_completions
IDE autocomplete:
```
Use on incomplete code after . or partial name
```

### lean_multi_attempt
Test tactics without editing:
```
Try: ["simp", "ring", "omega", "aesop"]
Returns goal state for each
```

## Implementation Strategy

### 1. Plan Review
Load and understand the implementation plan:
- What theorems/definitions to create
- What proof approach to use
- What imports are needed

### 2. File Setup
Ensure proper structure:
```lean
import Mathlib.Tactic
import Logos.Layer{N}.Dependencies

namespace Logos.Layer{N}

-- Implementation goes here

end Logos.Layer{N}
```

### 3. Iterative Proof Development

For each theorem/definition:
```
1. Write initial structure
2. Check goals with lean_goal
3. Apply tactics
4. Check diagnostics
5. Iterate until complete
6. Verify no errors
```

### 4. Tactic Selection

Use lean_multi_attempt to find working tactics:
```
Common effective tactics:
- simp [lemma1, lemma2]
- ring, omega (arithmetic)
- aesop (automated reasoning)
- exact h, apply lemma
- constructor, cases, induction
```

## Execution Flow

```
1. Receive task context with plan
2. Load plan and find resume point
3. Set up or modify .lean file
4. For each theorem/definition:
   a. Write initial code
   b. Check lean_goal for proof state
   c. Apply tactics iteratively
   d. Verify with lean_diagnostic_messages
   e. Continue until "no goals"
5. Run lake build to verify
6. Create implementation summary
7. Return results
```

## Proof Development Loop

```
while goals_remain:
    1. lean_goal → see current state
    2. Identify what tactic to try
    3. Edit file with tactic
    4. lean_diagnostic_messages → check errors
    5. If error: adjust and retry
    6. If progress: continue
    7. lean_goal → verify progress
```

## Common Patterns

### Simple Proof
```lean
theorem simple : P → P := fun h => h
```

### Tactic Proof
```lean
theorem tactic_proof : Statement := by
  intro h
  apply lemma
  exact h
```

### Complex Proof
```lean
theorem complex : ∀ x, P x → Q x := by
  intro x hP
  induction x with
  | base => simp [hP]
  | step n ih =>
    apply step_lemma
    exact ih hP
```

## Verification

After implementation:
```bash
lake build
```

Check:
- No `sorry` remaining
- No axioms unless intentional
- All theorems compile

## Return Format

```json
{
  "status": "completed|partial",
  "summary": "Implemented N theorems",
  "artifacts": [
    {
      "path": "Logos/Layer{N}/File.lean",
      "type": "implementation",
      "description": "Lean implementation"
    }
  ],
  "theorems_implemented": [
    "Namespace.theorem1",
    "Namespace.theorem2"
  ],
  "sorry_count": 0,
  "build_status": "success"
}
```

## Error Handling

### Proof Stuck
1. Use lean_multi_attempt with varied tactics
2. Search for relevant lemmas
3. Try different proof approach
4. Document blocker if truly stuck

### Type Mismatch
1. Use lean_hover_info to check types
2. Add explicit type annotations
3. Look for conversion lemmas

### Missing Import
1. Search with lean_local_search
2. Add required import
3. Rebuild
