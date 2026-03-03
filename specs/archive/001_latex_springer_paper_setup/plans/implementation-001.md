# Implementation Plan: Task #1

- **Task**: 1 - latex_springer_paper_setup
- **Status**: [COMPLETED]
- **Effort**: 1.5 hours
- **Dependencies**: None
- **Research Inputs**: specs/001_latex_springer_paper_setup/reports/research-001.md
- **Artifacts**: plans/implementation-001.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: latex
- **Lean Intent**: false

## Overview

This plan sets up a LaTeX paper directory at ModelChecker/latex/ using the Springer Nature template (v3.1, December 2024) for Journal of Automated Reasoning submission. The implementation copies the exact template files, organizes supporting assets, and creates documentation explaining journal requirements. Unlike the Logos project, this uses a single consolidated .tex document per Springer's explicit requirement (no subfiles).

### Research Integration

- Springer Nature requires single .tex documents (no \input or subfiles)
- The sn-mathphys-num reference style is appropriate for automated reasoning journals
- Template v3.1 (December 2024) is current
- Code/data availability statements are mandatory per Springer Nature policy
- Supporting files (cls, bst) must accompany the main document

## Goals & Non-Goals

**Goals**:
- Create ModelChecker/latex/ directory with proper structure
- Copy Springer Nature template files exactly as provided
- Organize supporting files in latex/assets/ directory
- Create comprehensive README.md documenting contents and requirements
- Ensure the paper compiles successfully with pdflatex

**Non-Goals**:
- Writing actual paper content (separate task)
- Creating custom notation package (may be added later)
- Depositing code on Zenodo (pre-submission task)
- Adapting the Logos notation.sty file

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Template compilation fails on system | M | L | Test pdflatex compilation during setup |
| Missing TeX dependencies | M | L | Document required TeX Live packages |
| File organization differs from journal expectations | L | L | Follow template structure exactly |

## Implementation Phases

### Phase 1: Create Directory Structure [COMPLETED]

**Goal**: Establish the ModelChecker/latex/ directory with proper subdirectories

**Tasks**:
- [ ] Create ModelChecker/latex/ directory
- [ ] Create latex/assets/ subdirectory for supporting files
- [ ] Create latex/figures/ subdirectory for paper figures (initially empty)
- [ ] Create latex/bibliography/ subdirectory for references

**Timing**: 10 minutes

**Files to create**:
- `latex/` - Main paper directory
- `latex/assets/` - Template class and supporting files
- `latex/figures/` - Figure files for the paper
- `latex/bibliography/` - Bibliography files

**Verification**:
- All directories exist
- Directory structure matches research recommendations

---

### Phase 2: Copy Template Files [COMPLETED]

**Goal**: Copy the Springer Nature template files to the correct locations

**Tasks**:
- [ ] Copy sn-jnl.cls to latex/assets/
- [ ] Copy sn-mathphys-num.bst to latex/assets/ (primary style for JAR)
- [ ] Copy sn-bibliography.bib to latex/bibliography/ as references.bib
- [ ] Copy sn-article.tex to latex/ as paper.tex
- [ ] Copy user-manual.pdf to latex/assets/ for reference
- [ ] Optionally copy additional .bst files to latex/assets/ for flexibility

**Timing**: 15 minutes

**Files to create/copy**:
- `latex/assets/sn-jnl.cls` - Springer Nature document class
- `latex/assets/sn-mathphys-num.bst` - Bibliography style (primary)
- `latex/assets/user-manual.pdf` - Template documentation
- `latex/bibliography/references.bib` - Bibliography database (from sample)
- `latex/paper.tex` - Main document (from sn-article.tex)

**Verification**:
- All files copied successfully
- File sizes match originals

---

### Phase 3: Configure Main Document [COMPLETED]

**Goal**: Update paper.tex to use the correct asset paths and initial configuration

**Tasks**:
- [ ] Update document class path to reference assets/ directory
- [ ] Update bibliography path to reference bibliography/ directory
- [ ] Update graphicspath to include figures/ directory
- [ ] Remove sample content sections (keep structure as reference comments)
- [ ] Update title and author placeholders
- [ ] Ensure all required Declarations subsections are present

**Timing**: 30 minutes

**Files to modify**:
- `latex/paper.tex` - Configure paths and clean up sample content

**Verification**:
- Document compiles with pdflatex
- No missing file errors
- Declarations section structure is complete

---

### Phase 4: Create README Documentation [COMPLETED]

**Goal**: Create comprehensive README.md documenting directory contents and journal requirements

**Tasks**:
- [ ] Document directory structure
- [ ] Document purpose of each file
- [ ] Document Journal of Automated Reasoning requirements
- [ ] Document Springer Nature code/data availability policies
- [ ] Document build instructions (pdflatex + bibtex workflow)
- [ ] Document TeX Live package dependencies
- [ ] Document submission checklist

**Timing**: 25 minutes

**Files to create**:
- `latex/README.md` - Comprehensive documentation

**README Structure**:
1. Overview
2. Directory Structure
3. File Descriptions
4. Journal Requirements (JAR-specific)
5. Springer Nature Policies (code/data availability)
6. Build Instructions
7. Submission Checklist

**Verification**:
- README accurately describes all files
- Build instructions work as documented
- Journal requirements clearly stated

---

### Phase 5: Create Build Configuration and Test [COMPLETED]

**Goal**: Create latexmkrc for consistent builds and verify compilation

**Tasks**:
- [ ] Create latexmkrc with pdflatex configuration
- [ ] Test full build (pdflatex + bibtex + pdflatex + pdflatex)
- [ ] Verify PDF output is generated
- [ ] Verify no errors or warnings (beyond template defaults)

**Timing**: 20 minutes

**Files to create**:
- `latex/latexmkrc` - Build configuration

**Verification**:
- `latexmk paper.tex` completes successfully
- PDF is generated in latex/ directory
- Build log shows no errors

---

## Testing & Validation

- [ ] All directories created correctly
- [ ] All template files copied to correct locations
- [ ] paper.tex compiles successfully with pdflatex
- [ ] bibtex processes references.bib without errors
- [ ] README.md is accurate and complete
- [ ] latexmk builds the document end-to-end

## Artifacts & Outputs

- `ModelChecker/latex/` - Complete paper directory
- `ModelChecker/latex/paper.tex` - Main document (template-based)
- `ModelChecker/latex/assets/` - Supporting template files
- `ModelChecker/latex/bibliography/references.bib` - Bibliography database
- `ModelChecker/latex/figures/` - Figure directory (initially empty)
- `ModelChecker/latex/README.md` - Documentation
- `ModelChecker/latex/latexmkrc` - Build configuration

## Rollback/Contingency

If implementation fails:
1. Remove ModelChecker/latex/ directory entirely
2. Original template files remain untouched at /home/benjamin/Downloads/v13/sn-article-template/
3. No dependencies on existing ModelChecker code

Alternative approach if path issues arise:
- Place all files directly in latex/ without subdirectories
- Adjust paths in paper.tex accordingly
