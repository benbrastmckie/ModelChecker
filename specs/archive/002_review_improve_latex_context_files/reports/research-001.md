# Research Report: Task #2

**Task**: 2 - review_improve_latex_context_files
**Started**: 2026-02-18T12:00:00Z
**Completed**: 2026-02-18T12:30:00Z
**Effort**: Medium
**Dependencies**: Task 1 (provides foundation for understanding project LaTeX setup)
**Sources/Inputs**: Codebase exploration, comparison with neovim/typst context
**Artifacts**: specs/002_review_improve_latex_context_files/reports/research-001.md
**Standards**: report-format.md, subagent-return.md

## Executive Summary

- The existing LaTeX context files (8 files) are well-structured but describe a **different project** (Logos documentation with subfiles) rather than the **sn-article template** used by this project
- The `latex-implementation-agent.md` references context paths that **do not match** the actual context directory structure
- Comparison with neovim/typst contexts reveals a missing **sn-article-specifics.md** or similar file for project-specific requirements
- The `latex/README.md` contains excellent project-specific documentation that should inform context updates
- Recommended: Create sn-article focused context file, update agent path references, revise existing files to be template-agnostic

## Context & Scope

### What Was Researched

1. All 8 existing LaTeX context files in `.claude/context/project/latex/`
2. The `latex-implementation-agent.md` for context loading patterns
3. The `skill-latex-implementation/SKILL.md` for context references
4. The `.claude/rules/latex.md` auto-loaded rules file
5. Comparison domains: neovim (16 files), typst (8 files)
6. Project-specific files: `latex/README.md`, `latex/paper.tex`, `latex/latexmkrc`

### Key Constraints

- Context files should be loaded lazily via @-references
- Context must be accurate for the **sn-article** template (Springer Nature Journal Article Template v3.1)
- Single .tex file requirement (no subfiles) per Springer journal submission requirements
- Files should be clear, complete, yet concise

## Findings

### 1. Current LaTeX Context File Inventory

| File | Lines | Purpose | Issue |
|------|-------|---------|-------|
| `README.md` | 47 | Overview & loading guide | References Logos, not sn-article |
| `standards/document-structure.md` | 184 | Main doc & subfile org | Describes subfile structure (not applicable) |
| `standards/latex-style-guide.md` | 225 | Formatting conventions | Generic, good semantic linefeeds section |
| `standards/notation-conventions.md` | 175 | logos-notation.sty macros | Logos-specific, not needed for sn-article |
| `patterns/cross-references.md` | 209 | Labels, refs, citations | Good general patterns |
| `patterns/theorem-environments.md` | 216 | amsthm environments | Good, but sn-jnl defines its own |
| `templates/subfile-template.md` | 165 | Subfile boilerplate | Not applicable (single file required) |
| `tools/compilation-guide.md` | 210 | Build process | Generic pdflatex/bibtex, missing latexmk config |

**Total**: 8 files, ~1,431 lines

### 2. Mismatch Between Agent and Context Directory

The `latex-implementation-agent.md` references paths that **do not exist**:

```markdown
# From latex-implementation-agent.md (lines 68-74):
- `@.claude/context/project/latex/style/latex-style-guide.md` - Formatting conventions (if exists)
- `@.claude/context/project/latex/style/notation-conventions.md` - Symbol definitions (if exists)
- `@.claude/context/project/latex/structure/document-structure.md` - Chapter/section patterns (if exists)
- `@.claude/context/project/latex/structure/theorem-environments.md` - Theorem/lemma formatting (if exists)
- `@.claude/context/project/latex/structure/cross-references.md` - Label/ref patterns (if exists)
- `@.claude/context/project/latex/structure/subfile-template.md` - Modular document structure (if exists)
- `@.claude/context/project/latex/build/compilation-guide.md` - Build process (if exists)
```

**Actual structure**:
```
project/latex/
├── README.md
├── standards/          # (not "style/")
│   ├── document-structure.md
│   ├── latex-style-guide.md
│   └── notation-conventions.md
├── patterns/           # (not "structure/")
│   ├── cross-references.md
│   └── theorem-environments.md
├── templates/          # (not "structure/")
│   └── subfile-template.md
└── tools/              # (not "build/")
    └── compilation-guide.md
```

### 3. Comparison with Neovim and Typst Contexts

**Neovim Context (16 files)** - Exemplary pattern:
- `README.md` with clear Loading Strategy section and task-type mapping
- Distinct `domain/`, `patterns/`, `standards/`, `tools/`, `templates/` directories
- Agent context loading table: "Task Type | Required Context"
- Each file is self-contained with practical examples

**Typst Context (8 files)** - Good pattern:
- `README.md` with project-specific paths (Theories/Bimodal/typst/)
- Clear "Differences from LaTeX" comparison table
- Loading Strategy with numbered steps

**LaTeX Context Gap**: Missing project-specific README.md content that describes:
- The actual project structure (`latex/paper.tex` single-file)
- The sn-jnl.cls document class requirements
- The sn-mathphys-num.bst bibliography style
- Springer Nature submission requirements

### 4. Project-Specific Requirements (from latex/README.md)

The project's `latex/README.md` (198 lines) contains critical information missing from context:

**Template Details**:
- Springer Nature Journal Article Template v3.1 (December 2024)
- Document class: `sn-jnl.cls`
- Reference style: `sn-mathphys-num` (Math and Physical Sciences, Numbered)
- Target: Journal of Automated Reasoning

**Critical Requirements**:
- **Single .tex file**: No `\input` or subfiles allowed
- **Figures**: Must be separate files, not embedded
- **Declarations section**: REQUIRED (funding, conflicts, ethics, data/code availability)
- **Code availability statement**: REQUIRED for computational papers

**Theorem Styles** (different from amsthm):
- `thmstyleone`: theorem, proposition, lemma, corollary (bold head, italic text)
- `thmstyletwo`: example, remark (roman head, italic text)
- `thmstylethree`: definition (bold head, roman text)

**Build Configuration** (from `latexmkrc`):
```perl
$pdf_mode = 1;
$pdflatex = 'pdflatex -interaction=nonstopmode -synctex=1 %O %S';
$bibtex_use = 2;
```

### 5. Gap Analysis

| Aspect | Current State | Required State |
|--------|---------------|----------------|
| README.md | References Logos project | Should reference sn-article/JAR paper |
| Document structure | Describes subfiles | Should describe single-file format |
| Theorem environments | Generic amsthm | Should document sn-jnl styles |
| Notation conventions | logos-notation.sty | Not applicable (remove or generalize) |
| Compilation guide | Generic pdflatex | Should include latexmk with project config |
| Subfile template | Exists | Should be removed (not applicable) |
| Journal requirements | Missing | Should document Springer requirements |
| Agent path references | Wrong subdirectories | Should match actual structure |

## Decisions

### Recommended Approach

1. **Update `README.md`** to describe the sn-article setup for JAR paper
2. **Remove or rename** `notation-conventions.md` (logos-specific content not needed)
3. **Remove or archive** `subfile-template.md` (subfiles not allowed)
4. **Update `document-structure.md`** to describe single-file format with sn-jnl sections
5. **Update `theorem-environments.md`** to document sn-jnl theorem styles
6. **Update `compilation-guide.md`** to include latexmk configuration from project
7. **Create new `sn-article-requirements.md`** documenting Springer-specific requirements
8. **Fix agent path references** in `latex-implementation-agent.md`

### Files to Create

1. **`standards/sn-article-requirements.md`** (NEW):
   - Journal of Automated Reasoning submission requirements
   - Declarations section requirements (code/data availability)
   - Single-file format requirements
   - Document class options (referee, lineno, etc.)

### Files to Significantly Revise

1. **`README.md`**: Project-specific content with loading strategy
2. **`standards/document-structure.md`**: Single-file sn-jnl structure
3. **`patterns/theorem-environments.md`**: sn-jnl theorem styles
4. **`tools/compilation-guide.md`**: latexmk configuration

### Files to Remove/Archive

1. **`templates/subfile-template.md`**: Not applicable
2. **`standards/notation-conventions.md`**: logos-specific, not needed

### Agent File Updates

Update `latex-implementation-agent.md` to:
1. Fix path references to match actual structure
2. Add sn-article-requirements.md to required context
3. Remove references to notation-conventions (optional)

## Risks & Mitigations

### Risk 1: Breaking Existing Functionality
**Mitigation**: The existing context files are currently mis-referenced by the agent anyway. Updating both together ensures consistency.

### Risk 2: Over-Specialization for sn-article
**Mitigation**: Keep generic LaTeX patterns (semantic linefeeds, cross-references) in style-guide.md. Put sn-article specifics in dedicated file.

### Risk 3: Loss of Useful Content
**Mitigation**: The logos-notation.sty and subfile content may be useful for other projects. Consider:
- Moving to an archive directory
- Or keeping as optional context for projects that use subfiles

## Appendix

### A. Search Queries Used

1. `Glob: .claude/context/project/latex/**/*` - Found 8 files
2. `Glob: .claude/context/project/neovim/**/*` - Found 16 files for comparison
3. `Glob: .claude/context/project/typst/**/*` - Found 8 files for comparison
4. `Glob: latex/**/*` - Found project LaTeX files

### B. Key Files Examined

**Context Files (all 8)**:
- `.claude/context/project/latex/README.md`
- `.claude/context/project/latex/standards/*.md` (3 files)
- `.claude/context/project/latex/patterns/*.md` (2 files)
- `.claude/context/project/latex/templates/subfile-template.md`
- `.claude/context/project/latex/tools/compilation-guide.md`

**Agent/Skill Files**:
- `.claude/agents/latex-implementation-agent.md`
- `.claude/skills/skill-latex-implementation/SKILL.md`
- `.claude/rules/latex.md`

**Project Files**:
- `latex/README.md` - Critical source of truth
- `latex/paper.tex` - Actual template usage
- `latex/latexmkrc` - Build configuration

### C. Comparison Context READMEs

**Neovim README Pattern**:
- Directory structure tree
- Loading Strategy with conditionals
- Configuration Assumptions section
- Agent Context Loading table (Task Type | Required Context)

**Typst README Pattern**:
- Created/Purpose metadata
- Overview with Key Characteristics
- Project Usage with actual paths
- Loading Strategy numbered steps
- Differences from LaTeX table

### D. Springer sn-jnl.cls Features (from paper.tex)

Document class options:
```latex
\documentclass[pdflatex,sn-mathphys-num]{sn-jnl}
% Options: referee (double spacing), lineno (line numbers)
```

Theorem styles defined by class:
```latex
\theoremstyle{thmstyleone}  % theorem, proposition, lemma, corollary
\theoremstyle{thmstyletwo}  % example, remark
\theoremstyle{thmstylethree} % definition
```

Required back matter:
```latex
\section*{Declarations}
\subsection*{Funding}
\subsection*{Conflict of interest}
\subsection*{Ethics approval}
\subsection*{Consent to participate}
\subsection*{Consent for publication}
\subsection*{Data availability}
\subsection*{Code availability}  % REQUIRED for computational papers
\subsection*{Author contribution}
```
