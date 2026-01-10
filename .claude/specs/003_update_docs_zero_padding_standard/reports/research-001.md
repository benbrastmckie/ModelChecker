# Research Report: Task #3

**Task**: Update documentation for zero-padding standard
**Date**: 2026-01-10
**Focus**: Identify files needing updates for `{NNN}_{SLUG}` directory convention

## Summary

The zero-padding convention (`printf "%03d"` → 001, 012, 345) was implemented in the core rule files (state-management.md, artifact-formats.md) and command files. However, many documentation and context files still use `{N}_{SLUG}` or show unpadded examples. A targeted update is needed to maintain consistency without bloating documentation.

## Findings

### Already Updated (No Changes Needed)

The authoritative sources have been updated:
- `.claude/rules/state-management.md` - Has "Project Number Format" section
- `.claude/rules/artifact-formats.md` - Has "Directory Naming Convention" section
- `.claude/commands/task.md` - Uses `printf "%03d"`
- `.claude/commands/research.md` - Uses `directory` field from state.json
- `.claude/commands/plan.md` - Uses `directory` field from state.json
- `.claude/commands/meta.md` - Uses zero-padded format

### High Priority Updates (Primary Documentation)

Files that users reference directly:

1. **`.claude/CLAUDE.md`** (lines 47, 81, 89)
   - Shows `{NUMBER}_{SLUG}` and `{N}_{SLUG}` in Task Artifact Paths section
   - Should use `{NNN}_{SLUG}` or add note referencing state-management.md

### Low Priority Updates (Secondary/Reference Files)

These inherit conventions from primary sources:

2. **`.claude/ARCHITECTURE.md`** (line 292) - Uses `{N}_{SLUG}`
3. **`.claude/commands/implement.md`** - Uses `{N}_{SLUG}` in several places
4. **`.claude/commands/revise.md`** - Uses `{N}_{SLUG}`
5. **`.claude/commands/todo.md`** - Uses `{N}_{SLUG}`
6. **`.claude/docs/README.md`** - Uses `{N}_{SLUG}` in examples
7. **Skills files** - Multiple uses in skill-planner, skill-researcher, etc.
8. **Context files** - Show hardcoded examples like `321_topic`

### Context File Examples (Hardcoded Numbers)

These use realistic examples with unpadded numbers:
- `specs/321_topic`, `specs/123_topic`, `specs/258_modal_logic_automation`
- These are documentation examples, not templates
- **Recommendation**: Leave as-is since they illustrate existing conventions

## Recommendations

1. **Minimal approach**: Only update CLAUDE.md (the entry point users see first)
2. **Add cross-reference**: Point to state-management.md "Project Number Format" section
3. **Don't update**: Hardcoded examples in context files (they're historical examples)
4. **Don't update**: Every `{N}_` reference - the convention is self-evident from CLAUDE.md

## References

- `.claude/rules/state-management.md` - Authoritative "Project Number Format" section
- Git commit e10820d1 - Original zero-padding implementation

## Next Steps

Update only `.claude/CLAUDE.md`:
1. Change `{NUMBER}_{SLUG}` → `{NNN}_{SLUG}` in Task Artifact Paths section
2. Add one-line note: "See state-management.md for formatting details"
3. Optionally update `{N}_{SLUG}` references if they appear misleading
