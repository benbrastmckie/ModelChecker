# Research Report: Task #1

**Task**: 1 - latex_springer_paper_setup
**Started**: 2026-02-18T00:00:00Z
**Completed**: 2026-02-18T00:30:00Z
**Effort**: Medium
**Dependencies**: None
**Sources/Inputs**:
- Template files at /home/benjamin/Downloads/v13/sn-article-template/
- Springer Nature LaTeX documentation
- Journal of Automated Reasoning submission guidelines
- Reference project at /home/benjamin/Projects/Logos/Theory/latex/
**Artifacts**:
- specs/001_latex_springer_paper_setup/reports/research-001.md (this report)
**Standards**: report-format.md

## Executive Summary

- Springer Nature provides a comprehensive LaTeX template (sn-jnl.cls v3.1, December 2024) suitable for Journal of Automated Reasoning submissions
- The template requires a single .tex document with figures attached separately (no \input or subfiles approach)
- Key requirements include: Math/Physics numbered reference style (sn-mathphys-num), code availability statements, data availability statements, and declarations section
- The recommended directory structure for ModelChecker/latex/ should mirror the template with customizations for mathematical notation

## Context & Scope

This research investigates requirements for setting up a LaTeX paper directory in the ModelChecker project for submission to the Journal of Automated Reasoning (Springer Nature). The task explicitly requires NOT using subfiles (unlike the Logos project) and instead creating a single consolidated paper.

### Research Questions
1. What files from the Springer template are required?
2. What are the Journal of Automated Reasoning specific requirements?
3. How should the directory be structured?
4. What notation customizations are needed?

## Findings

### 1. Springer Nature Template Files (v3.1, December 2024)

**Location**: `/home/benjamin/Downloads/v13/sn-article-template/`

**Required Files**:
| File | Purpose |
|------|---------|
| `sn-jnl.cls` | Document class (55,857 bytes) |
| `sn-mathphys-num.bst` | Bibliography style for Math/Physics (numbered) |
| `sn-bibliography.bib` | Sample bibliography file |
| `sn-article.tex` | Template document |

**Optional Files**:
| File | Purpose |
|------|---------|
| `fig.eps` / `empty.eps` | Sample figures (not needed) |
| `user-manual.pdf` | Reference documentation |
| Other `.bst` files | Alternative bibliography styles |

### 2. Template Structure Requirements

**Critical Warning from Template**:
```latex
%% Please do not use \input{...} to include other tex files.
%% Submit your LaTeX manuscript as one .tex document.
%%
%% All additional figures and files should be attached
%% separately and not embedded in the \TeX\ document itself.
```

**Document Class Configuration**:
```latex
\documentclass[pdflatex,sn-mathphys-num]{sn-jnl}
```

Options available:
- `referee` - Double line spacing for review
- `lineno` - Line numbers in margin
- Reference styles: `sn-basic`, `sn-mathphys-num` (recommended), `sn-mathphys-ay`, `sn-nature`, `sn-apa`, `sn-chicago`, `sn-vancouver-num/ay`

**Standard Packages Loaded by Template**:
- `graphicx`, `multirow`, `amsmath`, `amssymb`, `amsfonts`
- `amsthm`, `mathrsfs`, `appendix`, `xcolor`, `textcomp`
- `manyfoot`, `booktabs`, `algorithm`, `algorithmicx`
- `algpseudocode`, `listings`

### 3. Required Document Sections

**Front Matter**:
- Title with optional short title
- Authors with affiliations (structured format: `\fnm{}`, `\sur{}`, `\email{}`)
- Abstract (unstructured preferred, ~200 words)
- Keywords

**Body Structure**:
- Introduction (no subheadings)
- Results/Methods/Discussion sections as appropriate
- Equations, Tables, Figures
- Algorithms/Code listings (if applicable)

**Back Matter**:
- Supplementary information (if applicable)
- Acknowledgements (brief)
- Declarations section (REQUIRED):
  - Funding
  - Conflict of interest/Competing interests
  - Ethics approval and consent to participate
  - Consent for publication
  - Data availability
  - Materials availability
  - Code availability
  - Author contribution
- Appendices
- References

### 4. Theorem Environments

The template provides three predefined styles:

```latex
\theoremstyle{thmstyleone}   % Bold head, italic text (numbered)
\newtheorem{theorem}{Theorem}
\newtheorem{proposition}[theorem]{Proposition}

\theoremstyle{thmstyletwo}   % Roman head, italic text (numbered)
\newtheorem{example}{Example}
\newtheorem{remark}{Remark}

\theoremstyle{thmstylethree} % Bold head, roman text (numbered)
\newtheorem{definition}{Definition}
```

### 5. Journal of Automated Reasoning Specific Requirements

**Scope**: Original research in automated reasoning, including:
- Theorem proving
- Model checking
- Logic programming
- Formal verification
- SMT solving

**Key Policies**:
- ORCID ID recommended at submission
- Authorship changes not permitted after acceptance
- Interests disclosure required (within last 3 years)
- Systems and formalizations should be made available online

**Code Availability Requirements** (Springer Nature Policy):
- Code Availability Statement required in all original research articles
- Code must be deposited in repository with permanent identifier
- Recommended repositories: **Code Ocean**, **Zenodo**
- GitHub links alone are insufficient (no permanent identifier)
- Citation in reference list required

**Data Availability Requirements**:
- Data Availability Statement mandatory
- Data should be deposited in publicly accessible repositories
- May include data in manuscript or supplementary files if no repository available

### 6. Reference Style

For Journal of Automated Reasoning, use **sn-mathphys-num** (Math and Physical Sciences Numbered):

```latex
\documentclass[pdflatex,sn-mathphys-num]{sn-jnl}
```

Bibliography entry examples:
```bibtex
@article{bib1,
  author  = "Author, A. and Author, B.",
  title   = "Article Title",
  journal = "J. Automated Reasoning",
  volume  = "68",
  pages   = "1--25",
  year    = "2024",
  doi     = "10.1007/..."
}
```

### 7. Figure Requirements

- Use PDF/JPG/PNG for pdflatex compilation
- EPS for standard latex compilation
- Each image from single input file
- Avoid subfigures
- Use `\begin{figure*}...\end{figure*}` for full-width figures in double-column

### 8. Notation Customization Needs

Based on `/home/benjamin/Projects/Logos/Theory/latex/assets/logos-notation.sty`, the following notation packages may need adaptation:

**Essential for ModelChecker Paper**:
- Modal operators: `\Box`, `\Diamond`
- Counterfactual operators: `\boxright`, `\diamondright`, `\circleright`
- State space notation: `\sqcup`, `\sqsubseteq`
- Verification relations: `\Vdash`, `\dashV`
- Bilateral proposition notation

**Package Dependencies to Include**:
```latex
\usepackage{stmaryrd}   % for \llbracket, \rrbracket
\usepackage{mathabx}    % for \square, \sqbullet symbols
\usepackage{mathtools}  % for \coloneqq
```

**Note**: Some packages may conflict with sn-jnl.cls. Test compatibility before final submission.

## Recommendations

### Recommended Directory Structure

```
ModelChecker/latex/
├── paper.tex                    # Single main document
├── sn-jnl.cls                   # Springer Nature class file
├── bst/
│   └── sn-mathphys-num.bst     # Bibliography style
├── bibliography/
│   └── references.bib          # Bibliography entries
├── figures/                     # Separate figure files
│   ├── figure1.pdf
│   └── ...
├── notation.sty                 # Custom notation (adapted from logos-notation.sty)
├── latexmkrc                    # Build configuration
└── README.md                    # Build instructions
```

### Implementation Steps

1. **Create Directory Structure**
   - Create `ModelChecker/latex/` directory
   - Copy required template files (sn-jnl.cls, bst files)

2. **Create Main Document**
   - Start from sn-article.tex template
   - Configure for sn-mathphys-num reference style
   - Add ModelChecker-specific notation preamble

3. **Adapt Notation Package**
   - Create simplified notation.sty from logos-notation.sty
   - Test compatibility with sn-jnl.cls
   - Include only notation needed for ModelChecker paper

4. **Set Up Bibliography**
   - Create references.bib with project-relevant citations
   - Ensure DOI fields populated where available

5. **Configure Build System**
   - Create latexmkrc for consistent builds
   - Test pdflatex compilation

6. **Prepare Code/Data Availability**
   - Deposit ModelChecker code on Zenodo or Code Ocean
   - Obtain DOI for citation
   - Prepare availability statements

### Key Differences from Logos Project

| Aspect | Logos Project | ModelChecker Paper |
|--------|---------------|-------------------|
| Document structure | subfiles package | Single .tex file |
| Document class | article (11pt) | sn-jnl (Springer) |
| Bibliography style | Custom bib_style.bst | sn-mathphys-num.bst |
| Notation | logos-notation.sty | Adapted subset |
| References | cleveref customization | natbib (built into sn-jnl) |

## Decisions

1. **Reference Style**: Use `sn-mathphys-num` (numbered, Math/Physics) as appropriate for automated reasoning journal
2. **No Subfiles**: Follow Springer requirement for single .tex document
3. **Code Repository**: Recommend Zenodo for permanent DOI assignment
4. **Notation Adaptation**: Create minimal notation.sty with only required symbols, testing compatibility with sn-jnl.cls

## Risks & Mitigations

| Risk | Likelihood | Impact | Mitigation |
|------|------------|--------|------------|
| Package conflicts with sn-jnl.cls | Medium | High | Test notation packages early; use conditional loading |
| Missing DOI for code | Low | Medium | Create Zenodo archive before submission |
| Notation inconsistency | Low | Low | Document all custom commands clearly |
| Large document compilation issues | Low | Medium | Use latexmk with proper configuration |

## Appendix

### A. Search Queries Used
- "Journal of Automated Reasoning Springer submission guidelines 2025 2026"
- "Springer Nature LaTeX template sn-jnl manuscript preparation submission"
- "Journal of Automated Reasoning article length word limit page limit requirements"
- "Springer Nature automated reasoning submission code availability data repository Zenodo"

### B. Key Documentation References
- [Springer Nature LaTeX Template (Overleaf)](https://www.overleaf.com/latex/templates/springer-nature-latex-template/myxmhdsbzkyd)
- [Springer Nature LaTeX Author Support](https://www.springernature.com/gp/authors/campaigns/latex-author-support)
- [Journal of Automated Reasoning Submission Guidelines](https://link.springer.com/journal/10817/submission-guidelines)
- [Springer Nature Code Policy](https://www.springernature.com/gp/open-science/code-policy)
- [Springer Nature Research Data Policy](https://www.springernature.com/gp/authors/research-data-policy)

### C. Template Version Information
- Template Version: 3.1 (December 2024)
- sn-jnl.cls: 55,857 bytes
- Compiler Requirements: TexLive 2018+ (varies by submission system)
