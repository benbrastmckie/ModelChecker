# Implementation Plan: Task #8

**Task**: Fix skill context loading in model-checker skill
**Version**: 001
**Created**: 2026-01-11
**Language**: meta

## Overview

Add explicit context loading instructions to the model-checker skill (`SKILL.md`) so it properly loads context files from `.claude/context/project/modelchecker/` instead of relying only on `context: fork`. Following the research recommendations, we will use **Option A** (add a Context Loading section) combined with the `@` reference notation for clarity.

## Phases

### Phase 1: Add Context Loading Section

**Estimated effort**: 15 minutes
**Status**: [NOT STARTED]

**Objectives**:
1. Add a "Context Loading" section to SKILL.md
2. Document which context files should be loaded and when
3. Use `@` notation for file references (consistent with CLAUDE.md patterns)

**Files to modify**:
- `.claude/skills/skill-model-checker/SKILL.md` - Add context loading section

**Steps**:
1. Read the current SKILL.md content
2. Identify the appropriate location for the Context Loading section (after Trigger Conditions)
3. Add the section with:
   - Core ModelChecker context files (architecture, theories, z3-patterns)
   - Installation context for troubleshooting scenarios
   - Related logic domain context (kripke-semantics-overview)
4. Use `@.claude/context/...` notation for references

**Context to add**:
```markdown
## Context Loading

Load these context files as needed during skill execution:

### Core ModelChecker Context (Always Load)
- @.claude/context/project/modelchecker/architecture.md - System architecture and package structure
- @.claude/context/project/modelchecker/theories.md - Theory library overview (logos, exclusion, imposition, bimodal)
- @.claude/context/project/modelchecker/z3-patterns.md - Z3 solver patterns and best practices

### Domain Context (Load When Relevant)
- @.claude/context/project/logic/domain/kripke-semantics-overview.md - Modal semantics background

### Installation Context (Load for Troubleshooting)
- @.claude/context/project/modelchecker/installation.md - Installation and CLI usage
```

**Verification**:
- SKILL.md contains a "Context Loading" section
- References use `@` notation
- All four modelchecker context files are referenced

---

### Phase 2: Update Related Documentation

**Estimated effort**: 10 minutes
**Status**: [NOT STARTED]

**Objectives**:
1. Update context-management.md example to reference this skill as a pattern
2. Verify consistency with other skill documentation patterns

**Files to modify**:
- `.claude/docs/guides/context-management.md` - Add reference to model-checker skill as example (optional)

**Steps**:
1. Check if context-management.md would benefit from a real example
2. If so, add a brief note about skill-model-checker as an example of proper context loading
3. Verify no other documentation needs updating

**Verification**:
- Documentation is consistent
- Model-checker skill serves as a pattern for other skills

---

## Dependencies

- None - this is a standalone documentation change

## Risks and Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Context files don't exist | Low | Low | All 4 files verified during research |
| `@` notation not recognized | Low | Low | This is already used in CLAUDE.md |
| Breaking existing skill behavior | Low | Very Low | Only adding documentation, not changing frontmatter |

## Success Criteria

- [ ] SKILL.md has a "Context Loading" section
- [ ] All 4 modelchecker context files are referenced
- [ ] Logic domain context (kripke-semantics) is referenced
- [ ] References use `@.claude/context/...` notation
- [ ] No breaking changes to existing skill functionality

## Rollback Plan

Revert the SKILL.md changes via git:
```bash
git checkout HEAD~1 -- .claude/skills/skill-model-checker/SKILL.md
```
