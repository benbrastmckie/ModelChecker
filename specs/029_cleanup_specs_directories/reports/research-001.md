# Research Report: Task #29

**Task**: cleanup_specs_directories
**Date**: 2026-03-03
**Focus**: Identify all specs/ directories in the repository besides ModelChecker/specs/ for cleanup

## Summary

Found 3 additional `specs/` directories in the repository besides the main `ModelChecker/specs/`. These directories contain historical development artifacts (plans, reports, prompts) from prior AI-assisted development that predate the current task management system. Total size is approximately 1.1MB across 57 files. Recommend deletion with no migration needed.

## Findings

### Directories Discovered

| Directory | File Count | Size | Purpose |
|-----------|------------|------|---------|
| `code/src/model_checker/theory_lib/bimodal/specs/` | 46 files | 932KB | CVC5 integration planning |
| `code/src/model_checker/theory_lib/specs/` | 10 files | 168KB | Theory refactoring work |
| `docs/specs/` | 1 file | 20KB | Documentation revision plan |

### Directory Details

#### 1. `code/src/model_checker/theory_lib/bimodal/specs/`

**Contents**:
- `cvc5/` - 33 files of SMT solver abstraction planning
  - `MASTER_PLAN.md` - CVC5 integration roadmap
  - `phase1_pilot/` - 14 stage files for bimodal CVC5 pilot
  - `phase2_abstraction/` - 9 stage files for abstraction layer
  - `phase3_integration/` - 9 stage files for integration
- `plans/` - 5 witness predicate implementation plans (001-005)
- `reports/` - 10 investigation reports including:
  - Debug analyses (countermodels, timeouts)
  - Technical investigations (witness quantification)
  - Example runs and optimization results

**Assessment**: Historical development artifacts from the CVC5 integration project. These are AI-generated planning documents from prior Claude sessions. The actual implementation would be in the source code, not these spec files.

**Preservation needed**: No. These are process artifacts, not code or configuration.

#### 2. `code/src/model_checker/theory_lib/specs/`

**Contents**:
- `plans/001_complete_theory_refactoring.md` - Theory module restructuring plan
- `prompts/` - 2 AI prompt templates
  - `analyze_theories_prompt.md`
  - `refactor_theories_prompt.md`
- `reports/` - 6 analysis reports
  - Theory-specific analyses (exclusion, imposition, logos)
  - Refactoring status and compliance reports
- `subagent-refactoring-guide.md` - Guide for parallel refactoring

**Assessment**: Historical refactoring artifacts. The prompts are interesting but outdated (reference subagent patterns not in current system). Reports capture completed work.

**Preservation needed**: No. The `subagent-refactoring-guide.md` could theoretically be preserved as documentation of refactoring patterns, but it describes an obsolete workflow.

#### 3. `docs/specs/`

**Contents**:
- `plans/documentation_revision_plan.md` - Documentation audit plan

**Assessment**: The file itself notes it was "completed in a previous revision" and points to a newer task (Task 10). This is a legacy artifact.

**Preservation needed**: No. Explicitly marked as superseded.

### Reference Analysis

References to these directories appear in:

1. **TODO.md** - References to `code/docs/specs/plans/` (paths that don't exist)
2. **specs/archive/** - Historical task references to `docs/specs/plans/`
3. **code/docs/implementation/DEVELOPMENT_WORKFLOW.md** - References `docs/specs/plans/`
4. **code/docs/development/DEBUGGING_PROTOCOLS.md** - References `docs/specs/` patterns
5. **code/docs/development/FEATURE_IMPLEMENTATION.md** - References `docs/specs/` patterns
6. **code/src/model_checker/iterate/README.md** - References `docs/specs/plans/`
7. **Internal self-references** within the bimodal/specs files themselves

**Note**: The `code/docs/` documentation references `docs/specs/` paths but this seems to be from an older convention where development artifacts lived under `docs/`. The current system uses `specs/` at the repository root.

## Recommendations

### Primary Recommendation: Delete All Three Directories

1. **`code/src/model_checker/theory_lib/bimodal/specs/`** - Delete entirely
   - Contains 46 historical planning files
   - Not referenced by active code
   - Self-contained (internal references only)

2. **`code/src/model_checker/theory_lib/specs/`** - Delete entirely
   - Contains 10 historical files including prompts
   - Prompts reference obsolete subagent patterns
   - Reports are for completed refactoring work

3. **`docs/specs/`** - Delete entirely
   - Contains 1 file explicitly marked as superseded
   - Points users to newer Task 10

### Secondary Recommendation: Update Documentation References

After deletion, update documentation that references old `docs/specs/` paths:

| File | Lines to Update |
|------|-----------------|
| `code/docs/implementation/DEVELOPMENT_WORKFLOW.md` | Lines 138, 141 |
| `code/docs/development/DEBUGGING_PROTOCOLS.md` | Lines 28-29, 137-138, 246, 251, 340 |
| `code/docs/development/FEATURE_IMPLEMENTATION.md` | Lines 58, 236, 531, 537, 553 |
| `code/src/model_checker/iterate/README.md` | Lines 56, 438 |

**Suggested update**: Change `docs/specs/` references to `specs/` (current location) or remove obsolete references.

### Items NOT to Delete

- `specs/` (main task management directory) - Active system, keep
- Any actual source code files - Only removing `specs/` subdirectories

## Risks and Mitigations

| Risk | Impact | Mitigation |
|------|--------|------------|
| Loss of historical context | Low | These are planning docs, not code; git history preserves them |
| Broken documentation links | Medium | Update `code/docs/` references in same PR |
| User confusion | Low | Document what was removed in commit message |

## References

- Main specs directory: `specs/README.md`
- Current task management system: `.claude/CLAUDE.md`
- CLAUDE.md "Specs Directory Protocol" section

## Next Steps

1. Create implementation plan with two phases:
   - Phase 1: Delete the three specs directories
   - Phase 2: Update documentation references (optional, can be separate task)
2. Consider whether documentation updates warrant their own task or can be bundled
