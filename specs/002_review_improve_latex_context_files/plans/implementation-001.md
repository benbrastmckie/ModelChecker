# Implementation Plan: Task #2

- **Task**: 2 - Review and improve LaTeX context files for sn-article template
- **Status**: [IMPLEMENTING]
- **Effort**: 3 hours
- **Dependencies**: Task 1 (provides foundation for understanding project LaTeX setup)
- **Research Inputs**: specs/002_review_improve_latex_context_files/reports/research-001.md
- **Artifacts**: plans/implementation-001.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: meta
- **Lean Intent**: false

## Overview

Transform the existing LaTeX context files from describing a Logos/subfile-based project to accurately documenting the sn-article template used by this project (Springer Nature Journal Article Template v3.1 for Journal of Automated Reasoning). The current context files reference the wrong project structure and the latex-implementation-agent has mismatched path references. This plan addresses both content accuracy and structural alignment.

### Research Integration

Key findings from research-001.md integrated:
- 8 existing files describe wrong project (Logos with subfiles vs sn-article single-file)
- Agent path references use wrong subdirectory names (style/ vs standards/, structure/ vs patterns/)
- Missing sn-article-specific documentation for Springer requirements
- `notation-conventions.md` and `subfile-template.md` are not applicable to this project

## Goals & Non-Goals

**Goals**:
- Update all LaTeX context files to accurately describe the sn-article template
- Create new `sn-article-requirements.md` documenting Springer-specific requirements
- Remove or archive inapplicable files (subfile-template, notation-conventions)
- Fix path references in latex-implementation-agent.md
- Ensure context loading patterns match actual directory structure

**Non-Goals**:
- Creating new LaTeX document content
- Modifying the actual latex/paper.tex file
- Adding support for subfile-based projects
- Changing the project's build system

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Breaking existing agent functionality | High | Low | Agent paths are already broken; fixing them improves functionality |
| Loss of useful generic content | Medium | Low | Preserve generic LaTeX patterns (semantic linefeeds, cross-references) in updated files |
| Over-specialization for sn-article | Medium | Medium | Keep sn-article specifics in dedicated file; retain generic patterns in other files |

## Implementation Phases

### Phase 1: Remove/Archive Inapplicable Files [COMPLETED]

**Goal**: Clean up files that do not apply to the sn-article single-file project format

**Tasks**:
- [ ] Remove `.claude/context/project/latex/templates/subfile-template.md` (subfiles not allowed by Springer)
- [ ] Remove `.claude/context/project/latex/standards/notation-conventions.md` (logos-specific macros not used)
- [ ] Remove empty `templates/` directory after subfile-template.md removal
- [ ] Verify no other files reference the removed files

**Timing**: 15 minutes

**Files to modify**:
- `templates/subfile-template.md` - DELETE
- `standards/notation-conventions.md` - DELETE

**Verification**:
- No orphaned references to removed files
- Directory structure is clean

---

### Phase 2: Create sn-article Requirements Document [COMPLETED]

**Goal**: Create comprehensive documentation of Springer Nature sn-article template requirements

**Tasks**:
- [ ] Create `.claude/context/project/latex/standards/sn-article-requirements.md`
- [ ] Document Journal of Automated Reasoning submission requirements
- [ ] Document sn-jnl.cls document class options (referee, lineno, etc.)
- [ ] Document single-file format requirements (no \input or subfiles)
- [ ] Document required Declarations section structure
- [ ] Document code/data availability statement requirements
- [ ] Document figure handling requirements

**Timing**: 45 minutes

**Files to modify**:
- `standards/sn-article-requirements.md` - CREATE (NEW)

**Verification**:
- File contains all critical Springer requirements from latex/README.md
- File is self-contained and follows context file conventions
- File can be loaded by agents via @-reference

---

### Phase 3: Update Existing Context Files [COMPLETED]

**Goal**: Revise existing context files to accurately describe sn-article project

**Tasks**:
- [ ] Update `README.md` with sn-article project overview and correct loading strategy
- [ ] Update `standards/document-structure.md` to describe single-file sn-jnl structure
- [ ] Update `patterns/theorem-environments.md` to document sn-jnl theorem styles (thmstyleone, thmstyletwo, thmstylethree)
- [ ] Update `tools/compilation-guide.md` to include latexmk configuration from project
- [ ] Update `standards/latex-style-guide.md` to reference sn-article conventions (minimal changes)
- [ ] Update `patterns/cross-references.md` to ensure compatibility (minimal changes)

**Timing**: 1.5 hours

**Files to modify**:
- `.claude/context/project/latex/README.md` - Major revision
- `.claude/context/project/latex/standards/document-structure.md` - Major revision
- `.claude/context/project/latex/patterns/theorem-environments.md` - Major revision
- `.claude/context/project/latex/tools/compilation-guide.md` - Moderate revision
- `.claude/context/project/latex/standards/latex-style-guide.md` - Minor revision
- `.claude/context/project/latex/patterns/cross-references.md` - Minor revision

**Verification**:
- No references to Logos project or subfiles
- All sn-jnl specific features documented
- Files remain concise yet complete

---

### Phase 4: Fix Agent Path References [NOT STARTED]

**Goal**: Update latex-implementation-agent.md to reference correct context paths

**Tasks**:
- [ ] Update context loading section with correct subdirectory names (standards/ not style/, patterns/ not structure/, tools/ not build/)
- [ ] Add reference to new sn-article-requirements.md
- [ ] Remove references to deleted files (notation-conventions, subfile-template)
- [ ] Verify all @-references resolve to existing files
- [ ] Update any task-type to context mapping tables

**Timing**: 30 minutes

**Files to modify**:
- `.claude/agents/latex-implementation-agent.md` - Path corrections

**Verification**:
- All @-references in agent file point to existing context files
- Agent context loading table is accurate
- Agent can successfully load all referenced context

---

## Testing & Validation

- [ ] Verify all removed files are gone and no orphaned references exist
- [ ] Verify new sn-article-requirements.md loads correctly via @-reference
- [ ] Verify updated README.md accurately reflects directory structure
- [ ] Verify latex-implementation-agent.md path references are all valid
- [ ] Verify theorem-environments.md documents sn-jnl styles correctly
- [ ] Verify compilation-guide.md includes latexmk configuration

## Artifacts & Outputs

- `specs/002_review_improve_latex_context_files/plans/implementation-001.md` (this file)
- `specs/002_review_improve_latex_context_files/summaries/implementation-summary-YYYYMMDD.md` (after completion)
- Updated files in `.claude/context/project/latex/`
- Updated `.claude/agents/latex-implementation-agent.md`

## Rollback/Contingency

If implementation causes issues:
1. Git revert to pre-implementation state
2. Context files are non-critical for basic operation (agents use "if exists" pattern)
3. Individual files can be restored from git history
4. No production code is affected by these meta changes
