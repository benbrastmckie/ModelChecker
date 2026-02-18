# Improve Slash Command Document Organization Implementation Plan

## Metadata
- **Date**: 2025-09-30
- **Feature**: Update slash commands for better document organization in root specs/
- **Scope**: Modify .claude/commands/ to use correct subdirectories
- **Estimated Phases**: 2
- **Standards File**: /home/benjamin/Documents/Philosophy/Projects/ModelChecker/CLAUDE.md
- **Related Research**: specs/research/101_slash_command_document_placement.md

## Overview

This plan updates slash commands (`/report`, `/debug`, `/plan`, `/refactor`, `/implement`) to properly organize documents in the root `specs/` directory using the correct subdirectory structure. Currently, some commands reference `specs/reports/` which doesn't exist (the actual directory is `specs/research/`).

### Current Issues

1. **Wrong Directory References**: Commands reference `specs/reports/` but actual directory is `specs/research/`
2. **Inconsistent Terminology**: "reports" vs "research" terminology is mixed
3. **Missing Subdirectory Guidance**: Commands don't clearly specify which subdirectory to use for different document types
4. **Debug Command Ambiguity**: `/debug` creates "reports" but should create debug analyses

### Current specs/ Structure

```
specs/
├── baselines/        # Test regression baselines
├── debug/            # Debugging analyses (22 files)
├── findings/         # Lessons learned (16 files)
├── fixes/            # Bug fix documentation (9 files)
├── implementation/   # Implementation summaries (2 files)
├── plans/            # Implementation plans (52 files)
└── research/         # Research reports (101 files)
```

**Note**: There is NO `specs/reports/` directory.

## ✅ IMPLEMENTATION COMPLETE

## Success Criteria

- [x] All slash commands reference correct subdirectories
- [x] `/report` creates files in `specs/research/`
- [x] `/debug` creates files in `specs/debug/`
- [x] `/plan` creates files in `specs/plans/`
- [x] `/refactor` creates files in `specs/research/`
- [x] `/implement` creates summaries in `specs/implementation/`
- [x] All command descriptions use consistent terminology
- [x] Commands include clear guidance on subdirectory selection
- [x] specs/README.md updated if needed

## Technical Design

### Subdirectory Usage Rules

| Command | Output Type | Target Directory | Numbering |
|---------|-------------|------------------|-----------|
| `/report` | Research reports | `specs/research/` | Sequential (NNN) |
| `/debug` | Debug analyses | `specs/debug/` | Sequential (NNN) |
| `/plan` | Implementation plans | `specs/plans/` | Sequential (NNN) |
| `/refactor` | Refactoring analysis reports | `specs/research/` | Sequential (NNN) |
| `/implement` | Implementation summaries | `specs/implementation/` | Matches plan number |
| `/document` | Documentation updates | N/A (updates existing docs) | N/A |

### Document Type Classification

1. **Research Reports** (`specs/research/`):
   - Topic investigations
   - Technology comparisons
   - Architectural analyses
   - Refactoring analyses
   - General research findings

2. **Debug Analyses** (`specs/debug/`):
   - Bug investigations
   - Root cause analyses
   - Problem diagnostics
   - Issue documentation

3. **Implementation Plans** (`specs/plans/`):
   - Feature implementation plans
   - Refactoring plans
   - Architecture changes
   - Migration strategies

4. **Implementation Summaries** (`specs/implementation/`):
   - Post-implementation reports
   - Lessons learned from implementation
   - Actual changes made vs planned

5. **Findings** (`specs/findings/`):
   - Quick insights
   - Important discoveries
   - Outcome summaries
   - Best practices identified

### Path Update Strategy

Replace all instances of:
- `specs/reports/` → `specs/research/` (for /report, /refactor)
- `specs/reports/` → `specs/debug/` (for /debug)
- Keep `specs/plans/` as-is
- Keep `specs/summaries/` → `specs/implementation/` mapping

## Implementation Phases

### Phase 1: Update Command Files [COMPLETED]
**Objective**: Correct all directory references in slash command files
**Complexity**: Low

Tasks:
- [x] Update `.claude/commands/report.md` to use `specs/research/` instead of `specs/reports/`
- [x] Update `.claude/commands/debug.md` to use `specs/debug/` instead of `specs/reports/`
- [x] Update `.claude/commands/refactor.md` to use `specs/research/` instead of `specs/reports/`
- [x] Update `.claude/commands/implement.md` to reference `specs/implementation/` (already correct)
- [x] Update `.claude/commands/plan.md` - verify uses `specs/plans/` (already correct)
- [x] Update `.claude/commands/list-reports.md` to search `specs/research/` and `specs/debug/`
- [x] Review all command descriptions for terminology consistency
- [x] Update command frontmatter descriptions if needed

Testing:
```bash
# Verify all updated files use correct paths
grep -r "specs/reports" .claude/commands/
# Should return NO results

# Verify correct paths are used
grep "specs/research" .claude/commands/report.md
grep "specs/debug" .claude/commands/debug.md
grep "specs/plans" .claude/commands/plan.md
grep "specs/implementation" .claude/commands/implement.md
```

### Phase 2: Add Subdirectory Selection Guidance [COMPLETED]
**Objective**: Improve commands with clear logic for choosing subdirectories
**Complexity**: Low

Tasks:
- [x] Add "Document Type Selection" section to report.md explaining when to use research/ vs debug/
- [x] Update debug.md to clarify it creates debug analyses, not general reports
- [x] Add examples to each command showing typical file paths
- [x] Ensure numbering logic searches correct subdirectory
- [x] Add note about subdirectory structure to each command's documentation
- [x] Update specs/README.md if directory descriptions need clarification
- [x] Create test documents with each command to verify organization

Testing:
```bash
# Manual testing - run each command and verify placement
# 1. Test /report
/report "test topic for research"
# Verify creates: specs/research/NNN_test_topic_for_research.md

# 2. Test /debug
/debug "test bug investigation"
# Verify creates: specs/debug/NNN_test_bug_investigation.md

# 3. Test /plan
/plan "test feature implementation"
# Verify creates: specs/plans/NNN_test_feature_implementation.md

# 4. Test /refactor
/refactor "test module"
# Verify creates: specs/research/NNN_refactoring_test_module.md

# Clean up test files afterward
rm specs/research/*test*.md specs/debug/*test*.md specs/plans/*test*.md
```

## Detailed Changes

### 1. report.md Updates

**Current (Line 4)**:
```markdown
description: Research a topic and create a comprehensive report in the appropriate specs/reports/ directory
```

**Updated**:
```markdown
description: Research a topic and create a comprehensive report in specs/research/ directory
```

**Current (Line 22)**:
```markdown
- Most appropriate location for the specs/reports/ directory
```

**Updated**:
```markdown
- Target location: specs/research/ at project root
```

**Current (Line 32)**:
```markdown
- Checking for existing reports in the target `specs/reports/` directory
```

**Updated**:
```markdown
- Checking for existing reports in `specs/research/` directory
```

**Current (Line 67)**:
```markdown
- Located in `[relevant-dir]/specs/reports/NNN_[topic-name].md`
```

**Updated**:
```markdown
- Located in `specs/research/NNN_[topic-name].md`
```

**Additional Changes**:
- Remove "Location Determination" section (lines 24-28) - use fixed location
- Simplify to always use `./specs/research/`
- Update all example paths in documentation

### 2. debug.md Updates

**Current (Line 4)**:
```markdown
description: Investigate issues and create diagnostic report without code changes
```

**Updated**:
```markdown
description: Investigate issues and create diagnostic analysis in specs/debug/ directory
```

**Current (Line 64)**:
```markdown
- Create numbered report in `specs/reports/` directory
```

**Updated**:
```markdown
- Create numbered debug analysis in `specs/debug/` directory
```

**Current (Line 146)**:
```markdown
specs/reports/NNN_debug_[issue_name].md
```

**Updated**:
```markdown
specs/debug/NNN_[issue_name].md
```

**Additional Changes**:
- Rename "Debug Report" to "Debug Analysis" throughout
- Update all references from "report" to "analysis" for clarity
- Change numbering to check `specs/debug/` directory

### 3. refactor.md Updates

**Current (Line 94)**:
```markdown
I'll create a comprehensive refactoring report in `specs/reports/`:
```

**Updated**:
```markdown
I'll create a comprehensive refactoring analysis report in `specs/research/`:
```

**Current (Line 97)**:
```markdown
- Check existing reports in appropriate `specs/reports/` directory
```

**Updated**:
```markdown
- Check existing reports in `specs/research/` directory
```

**Current (Line 99)**:
```markdown
- Name format: `NNN_refactoring_[scope].md`
```

**Updated**:
```markdown
- Name format: `NNN_refactoring_analysis_[scope].md`
```

### 4. list-reports.md Updates

**Current (Line 18)**:
```markdown
I'll search for all reports in `specs/reports/` directories throughout the codebase and provide:
```

**Updated**:
```markdown
I'll search for all reports in `specs/research/` and `specs/debug/` directories and provide:
```

**Additional Changes**:
- Update search pattern to include both research/ and debug/
- Categorize results by type (research vs debug)
- Show which directory each report is in

### 5. implement.md Updates

**Current (Line 109)**:
```markdown
- Location: Same directory as the plan, in `specs/summaries/`
```

**Updated**:
```markdown
- Location: `specs/implementation/` at project root
```

**Note**: This is already mostly correct, just needs terminology update from "summaries" to "implementation"

### 6. plan.md Updates

**Current (Line 15)**:
```markdown
- **Research Reports**: Any paths to specs/reports/*.md files in arguments
```

**Updated**:
```markdown
- **Research Reports**: Any paths to specs/research/*.md files in arguments
```

**Current (Line 38-42)**:
```markdown
### 3. Location Determination
I'll find the deepest directory that encompasses all relevant files by:
- Identifying components that will be modified or created
- Finding common parent directories
- Selecting the most specific directory for the plan
```

**Updated**:
```markdown
### 3. Plan Location
All implementation plans are created in the root `specs/plans/` directory for consistency and easy discovery.
```

**Current (Line 45)**:
```markdown
- Checking existing plans in the target `specs/plans/` directory
```

**Updated**:
```markdown
- Checking existing plans in `specs/plans/` directory
```

**Current (Line 106)**:
```markdown
- Path: `[relevant-dir]/specs/plans/NNN_feature_name.md`
```

**Updated**:
```markdown
- Path: `specs/plans/NNN_feature_name.md`
```

## Testing Strategy

### Unit Tests (Command File Validation)

```bash
# Test 1: No references to specs/reports/
! grep -r "specs/reports" .claude/commands/
echo "PASS: No specs/reports references" || echo "FAIL: Found specs/reports"

# Test 2: Correct paths in each command
grep -q "specs/research" .claude/commands/report.md && echo "PASS: report.md"
grep -q "specs/debug" .claude/commands/debug.md && echo "PASS: debug.md"
grep -q "specs/plans" .claude/commands/plan.md && echo "PASS: plan.md"
grep -q "specs/implementation" .claude/commands/implement.md && echo "PASS: implement.md"
```

### Integration Tests (Actual Command Usage)

1. **Test /report command**:
   ```bash
   # Run: /report "test research topic"
   # Expected: Creates specs/research/10X_test_research_topic.md
   ```

2. **Test /debug command**:
   ```bash
   # Run: /debug "test bug description"
   # Expected: Creates specs/debug/0XX_test_bug_description.md
   ```

3. **Test /plan command**:
   ```bash
   # Run: /plan "test feature"
   # Expected: Creates specs/plans/10X_test_feature.md
   ```

4. **Test /list-reports command**:
   ```bash
   # Run: /list-reports
   # Expected: Shows reports from both specs/research/ and specs/debug/
   ```

### Validation Criteria

- ✅ All commands create documents in correct subdirectories
- ✅ No command references non-existent `specs/reports/`
- ✅ Numbering sequences work correctly in each subdirectory
- ✅ Command descriptions accurately reflect behavior
- ✅ Test documents can be created and cleaned up successfully

## Documentation Requirements

### Files to Update

1. **.claude/commands/report.md**
   - Change all `specs/reports/` to `specs/research/`
   - Remove "Location Determination" complexity
   - Use fixed path: `./specs/research/`

2. **.claude/commands/debug.md**
   - Change `specs/reports/` to `specs/debug/`
   - Update terminology: "report" → "analysis"
   - Fix output path format

3. **.claude/commands/refactor.md**
   - Change `specs/reports/` to `specs/research/`
   - Update report naming convention

4. **.claude/commands/plan.md**
   - Change `specs/reports/` to `specs/research/` in examples
   - Simplify location logic to fixed path

5. **.claude/commands/implement.md**
   - Update `specs/summaries/` to `specs/implementation/`

6. **.claude/commands/list-reports.md**
   - Search both `specs/research/` and `specs/debug/`
   - Categorize results by directory

### Optional: Update specs/README.md

If directory descriptions need clarification:
- Emphasize `research/` contains general research and analyses
- Clarify `debug/` contains bug-specific investigations
- Note the distinction between the two

## Dependencies

- No code dependencies
- No external tools required
- Only modifies .claude/commands/ markdown files

## Risk Assessment

### Risks: Very Low

1. **Backward Compatibility**: ✅ No breaking changes
   - Commands create new documents; don't modify existing ones
   - Old documents in correct locations stay valid

2. **User Impact**: ✅ Minimal
   - Users see clearer, more consistent behavior
   - Documents appear in expected locations

3. **Rollback**: ✅ Trivial
   - Simple git revert if issues arise
   - No data loss possible

### Mitigation Strategies

1. **Testing**: Test each command after updates
2. **Documentation**: Clear commit message explaining changes
3. **Validation**: Grep for any remaining incorrect paths

## Notes

### Why This Approach?

1. **Simplicity**: Fixed paths are easier to understand than complex location detection
2. **Consistency**: All documents of same type go to same place
3. **Discoverability**: Users know exactly where to find documents
4. **Maintainability**: No complex algorithms to maintain

### Supersedes Previous Research

The research report 101 recommended multi-level specs/ with location detection. This plan instead:
- Uses single root specs/ directory
- Organizes by document TYPE (research, debug, plans) not code location
- Simpler and more maintainable for this project

### Future Considerations

If the project grows and truly needs module-specific specs:
- Could add module prefix to filenames (e.g., `NNN_exclusion_theory_bug.md`)
- Could add subdirectories within research/ (e.g., `research/theory_lib/`)
- Current flat structure works well for current scale

## Git Commit Message Template

```
fix: correct slash command specs/ directory references

Update slash commands to use correct subdirectories:
- /report now creates files in specs/research/ (was specs/reports/)
- /debug now creates files in specs/debug/ (was specs/reports/)
- /refactor now creates files in specs/research/ (was specs/reports/)
- /implement uses specs/implementation/ (was specs/summaries/)
- /plan uses specs/plans/ (no change, already correct)

Fixed all references to non-existent specs/reports/ directory.
Updated terminology for consistency.
Simplified location logic to use fixed paths.

All commands now correctly organize documents in root specs/ directory.

Refs: specs/research/101_slash_command_document_placement.md

🤖 Generated with [Claude Code](https://claude.com/claude-code)

Co-Authored-By: Claude <noreply@anthropic.com>
```

## Success Metrics

- **Path Accuracy**: 100% of commands use correct directories
- **Consistency**: 0 references to non-existent `specs/reports/`
- **User Experience**: Documents appear in expected locations
- **Maintainability**: Commands use simple, fixed paths

## Post-Implementation Actions

1. Update research report 101 with note about chosen approach
2. Test all commands to ensure proper document creation
3. Monitor for any issues or confusion
4. Consider adding this to project documentation/guides
