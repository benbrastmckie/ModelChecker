# Implementation Plan: Task #29

- **Task**: 29 - cleanup_specs_directories
- **Status**: [NOT STARTED]
- **Effort**: 1 hour
- **Dependencies**: None
- **Research Inputs**: specs/029_cleanup_specs_directories/reports/research-001.md
- **Artifacts**: plans/implementation-001.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: general
- **Lean Intent**: false

## Overview

Remove obsolete `specs/` directories containing historical AI-generated planning artifacts that are no longer needed. Three directories totaling approximately 1.1MB will be deleted, and four documentation files with stale references will be updated. Research confirmed no code, configuration, or critical content requires preservation.

### Research Integration

Research report identified:
- 3 specs/ directories to delete (total: 57 files, ~1.1MB)
- All contain superseded planning documents, no executable code
- 4 documentation files reference deleted paths and need updates

## Goals & Non-Goals

**Goals**:
- Delete all specs/ directories except ModelChecker/specs/
- Update documentation references to removed directories
- Document what was removed for audit trail

**Non-Goals**:
- Migrate any content (research confirmed nothing requires preservation)
- Modify any Python code or configuration files
- Change the primary specs/ directory structure

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Accidental deletion of wrong directory | H | L | Explicit path verification before deletion |
| Broken documentation links | M | M | Update all identified references |
| Missing reference in undiscovered file | L | L | Grep verification after deletion |

## Implementation Phases

### Phase 1: Delete Specs Directories [NOT STARTED]

**Goal**: Remove the three identified specs/ directories

**Tasks**:
- [ ] Verify directory paths exist and match research findings
- [ ] Delete `code/src/model_checker/theory_lib/bimodal/specs/` (46 files, 932KB)
- [ ] Delete `code/src/model_checker/theory_lib/specs/` (10 files, 168KB)
- [ ] Delete `docs/specs/` (1 file, 20KB)
- [ ] Verify deletions succeeded

**Timing**: 15 minutes

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/specs/` - DELETE
- `code/src/model_checker/theory_lib/specs/` - DELETE
- `docs/specs/` - DELETE

**Verification**:
- Directories no longer exist
- No errors during deletion

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
- No broken references in documentation
- Documentation still makes sense after edits

---

### Phase 3: Verification and Documentation [NOT STARTED]

**Goal**: Confirm cleanup is complete and document changes

**Tasks**:
- [ ] Search for any remaining references to deleted directories
- [ ] Verify ModelChecker/specs/ is intact and functional
- [ ] Create implementation summary documenting what was removed

**Timing**: 15 minutes

**Files to modify**:
- `specs/029_cleanup_specs_directories/summaries/implementation-summary-20260303.md` - CREATE

**Verification**:
- `grep -r "theory_lib/bimodal/specs" .` returns no results
- `grep -r "theory_lib/specs" .` returns no results (except legitimate code paths)
- `grep -r "docs/specs" .` returns no results
- Primary specs/ directory intact

## Testing & Validation

- [ ] All three target directories deleted
- [ ] No grep hits for deleted directory paths in documentation
- [ ] ModelChecker/specs/ directory and state.json intact
- [ ] Documentation files read correctly after edits
- [ ] No broken internal documentation links

## Artifacts & Outputs

- plans/implementation-001.md (this file)
- summaries/implementation-summary-20260303.md (to be created)

## Rollback/Contingency

Git provides rollback capability:
```bash
# If needed, restore deleted directories from git history
git checkout HEAD~1 -- code/src/model_checker/theory_lib/bimodal/specs/
git checkout HEAD~1 -- code/src/model_checker/theory_lib/specs/
git checkout HEAD~1 -- docs/specs/
```

All content is versioned; no permanent data loss risk.
