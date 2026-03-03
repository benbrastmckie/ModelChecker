# Implementation Plan: Task #29

- **Task**: 29 - cleanup_specs_directories
- **Version**: 002
- **Status**: [NOT STARTED]
- **Effort**: 45 minutes
- **Dependencies**: None
- **Research Inputs**: specs/029_cleanup_specs_directories/reports/research-001.md
- **Artifacts**: plans/implementation-002.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: general
- **Lean Intent**: false

## Revision Notes

**v002**: Simplified plan - removed audit trail documentation per user feedback. Git history provides sufficient record of changes.

## Overview

Remove obsolete `specs/` directories containing historical AI-generated planning artifacts that are no longer needed. Three directories totaling approximately 1.1MB will be deleted, and four documentation files with stale references will be updated.

### Research Integration

Research report identified:
- 3 specs/ directories to delete (total: 57 files, ~1.1MB)
- All contain superseded planning documents, no executable code
- 4 documentation files reference deleted paths and need updates

## Goals & Non-Goals

**Goals**:
- Delete all specs/ directories except ModelChecker/specs/
- Update documentation references to removed directories

**Non-Goals**:
- Migrate any content (research confirmed nothing requires preservation)
- Modify any Python code or configuration files
- Change the primary specs/ directory structure
- Create additional audit documentation (git history is sufficient)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Accidental deletion of wrong directory | H | L | Explicit path verification before deletion |
| Broken documentation links | M | M | Update all identified references |

## Implementation Phases

### Phase 1: Delete Specs Directories [NOT STARTED]

**Goal**: Remove the three identified specs/ directories

**Tasks**:
- [ ] Delete `code/src/model_checker/theory_lib/bimodal/specs/` (46 files, 932KB)
- [ ] Delete `code/src/model_checker/theory_lib/specs/` (10 files, 168KB)
- [ ] Delete `docs/specs/` (1 file, 20KB)

**Timing**: 10 minutes

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/specs/` - DELETE
- `code/src/model_checker/theory_lib/specs/` - DELETE
- `docs/specs/` - DELETE

**Verification**:
- Directories no longer exist

---

### Phase 2: Update Documentation References [NOT STARTED]

**Goal**: Remove or update stale references to deleted directories

**Tasks**:
- [ ] Update `code/docs/implementation/DEVELOPMENT_WORKFLOW.md` (lines 138, 141)
- [ ] Update `code/docs/development/DEBUGGING_PROTOCOLS.md` (lines 28-29, 137-138, 246, 251, 340)
- [ ] Update `code/docs/development/FEATURE_IMPLEMENTATION.md` (lines 58, 236, 531, 537, 553)
- [ ] Update `code/src/model_checker/iterate/README.md` (lines 56, 438)

**Timing**: 30 minutes

**Files to modify**:
- `code/docs/implementation/DEVELOPMENT_WORKFLOW.md` - Edit references
- `code/docs/development/DEBUGGING_PROTOCOLS.md` - Edit references
- `code/docs/development/FEATURE_IMPLEMENTATION.md` - Edit references
- `code/src/model_checker/iterate/README.md` - Edit references

**Verification**:
- No broken references to deleted directories
- `grep -r "theory_lib/bimodal/specs\|theory_lib/specs\|docs/specs" .` returns no relevant hits

## Testing & Validation

- [ ] All three target directories deleted
- [ ] No grep hits for deleted directory paths
- [ ] ModelChecker/specs/ directory intact

## Artifacts & Outputs

- plans/implementation-002.md (this file)

## Rollback/Contingency

Git provides rollback capability - all deleted content recoverable from history.
