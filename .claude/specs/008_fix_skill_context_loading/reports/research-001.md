# Research Report: Task #8

**Task**: Fix skill context loading in model-checker skill
**Date**: 2026-01-11
**Focus**: Understanding `context: fork` and proper context loading

## Summary

The model-checker skill (and all other skills) currently uses `context: fork` in frontmatter, which is a placeholder indicating context forking behavior. The user wants the model-checker skill specifically to load appropriate context files from `.claude/context/project/modelchecker/` instead. Four relevant context files exist that should be loaded for the model-checker skill.

## Findings

### 1. Current State of SKILL.md

The model-checker skill at `.claude/skills/skill-model-checker/SKILL.md` has:

```yaml
---
name: skill-model-checker
description: Research and develop semantic theories using ModelChecker with Z3 SMT solver...
allowed-tools: Read, Write, Edit, Glob, Grep, Bash(PYTHONPATH=* pytest *), ...
context: fork
---
```

The `context: fork` is used consistently across **all 9 skills** in the system. It appears to be a standard placeholder indicating the skill should fork context from the parent.

### 2. Available ModelChecker Context Files

Four context files exist in `.claude/context/project/modelchecker/`:

| File | Purpose | Size |
|------|---------|------|
| `architecture.md` | System architecture overview - packages, data flow, Z3 integration | ~166 lines |
| `theories.md` | Theory library overview - logos, exclusion, imposition, bimodal | ~241 lines |
| `z3-patterns.md` | Z3 solver patterns and best practices | ~365 lines |
| `installation.md` | Installation assistance context | ~242 lines |

### 3. Context Loading Strategy

According to `.claude/docs/guides/context-management.md`, context should be:
- **Lazy loaded**: Load files only when needed
- **Documented in skill**: List what context is loaded
- **Minimal**: Avoid loading entire directories

The recommended approach in skills is to add a "Context Loading" section:

```markdown
## Context Loading

This skill loads:
- `project/modelchecker/architecture.md` - For system understanding
- `project/modelchecker/theories.md` - For theory patterns
- `project/modelchecker/z3-patterns.md` - For Z3 specifics
```

### 4. What `context: fork` Means

Based on ARCHITECTURE.md and templates, `context: fork` indicates the skill inherits context from its parent (the orchestrator/command that invoked it). This is the standard pattern across all skills.

The issue is that there's no explicit instruction in the skill about which context files to load for ModelChecker-specific work.

### 5. Related Context Files to Consider

Additional context that may be relevant for the model-checker skill:

- `project/logic/domain/kripke-semantics-overview.md` - Already referenced in CLAUDE.md
- `core/standards/testing.md` - For TDD patterns
- `core/standards/error-handling.md` - For error patterns

## Recommendations

### Option A: Add Context Loading Section (Recommended)

Add a dedicated "Context Loading" section to SKILL.md that explicitly lists which context files should be read during skill execution. Keep `context: fork` for the parent behavior but add explicit loading instructions.

**Implementation**:
1. Add a "## Context Loading" section to SKILL.md
2. List the 4 modelchecker context files with when/why to load them
3. Optionally list related logic domain context
4. Keep `context: fork` in frontmatter (maintains parent behavior)

### Option B: Replace `context: fork` with explicit paths

Change the frontmatter `context:` field to list specific files:

```yaml
context:
  - project/modelchecker/architecture.md
  - project/modelchecker/theories.md
  - project/modelchecker/z3-patterns.md
```

**Consideration**: This may not work if the frontmatter schema expects `fork` as a string value. Would need to verify frontmatter parsing behavior.

### Option C: Hybrid approach

Keep `context: fork` but add context file references inline with `@` notation as used in CLAUDE.md:

```markdown
See also:
- @.claude/context/project/modelchecker/architecture.md
- @.claude/context/project/modelchecker/theories.md
```

## References

- `.claude/skills/skill-model-checker/SKILL.md` - Current skill definition
- `.claude/context/project/modelchecker/` - 4 context files
- `.claude/docs/guides/context-management.md` - Context loading guidance
- `.claude/docs/guides/creating-skills.md` - Skill creation guide
- `.claude/ARCHITECTURE.md` - System architecture

## Next Steps

1. Decide on approach (A, B, or C)
2. Update SKILL.md with explicit context loading instructions
3. Test that the skill properly loads context during execution
4. Consider updating other skills similarly if this pattern proves effective
