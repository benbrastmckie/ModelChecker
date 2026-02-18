# Springer Nature sn-article Template Requirements

## Overview

This document specifies the requirements for using the Springer Nature Journal Article Template (sn-jnl.cls v3.1) for submissions to the **Journal of Automated Reasoning** (JAR).

## Template Information

| Field | Value |
|-------|-------|
| Template | Springer Nature Journal Article Template v3.1 |
| Document Class | sn-jnl.cls |
| Reference Style | sn-mathphys-num (Math and Physical Sciences, Numbered) |
| Target Journal | Journal of Automated Reasoning |

## Document Class Options

### Basic Usage

```latex
\documentclass[pdflatex,sn-mathphys-num]{sn-jnl}
```

### Available Options

| Option | Effect | Use Case |
|--------|--------|----------|
| `pdflatex` | Use pdflatex engine | Standard compilation |
| `sn-mathphys-num` | Numbered citations | Required for JAR |
| `referee` | Double line spacing | Review copy |
| `lineno` | Line numbers in margin | Review copy |

### Review Copy Configuration

```latex
% Double spacing for review:
\documentclass[referee,pdflatex,sn-mathphys-num]{sn-jnl}

% Line numbers for review:
\documentclass[lineno,pdflatex,sn-mathphys-num]{sn-jnl}

% Both options combined:
\documentclass[referee,lineno,pdflatex,sn-mathphys-num]{sn-jnl}
```

## Single-File Requirement

**CRITICAL**: Springer Nature requires submission as a single .tex file.

### Prohibited Patterns

```latex
% NOT ALLOWED - no external includes:
\input{section.tex}
\include{chapter.tex}
\subfile{content.tex}

% NOT ALLOWED - no subfiles package:
\usepackage{subfiles}
```

### Required Pattern

All content must be inline in the main `paper.tex` file:

```latex
\documentclass[pdflatex,sn-mathphys-num]{sn-jnl}

% All packages declared here
\usepackage{graphicx}
\usepackage{amsmath,amssymb,amsfonts}
% ... etc

\begin{document}
% All content inline
\section{Introduction}
Content here...

\section{Next Section}
More content...

\end{document}
```

## Required Sections

### Front Matter

```latex
\title[Short Title]{Full Title}

\author*[1]{\fnm{First} \sur{Last}}\email{email@example.com}

\affil*[1]{\orgdiv{Department}, \orgname{University},
  \orgaddress{\city{City}, \state{State}, \country{Country}}}

\abstract{Abstract text here.}

\keywords{keyword1, keyword2, keyword3}

\maketitle
```

### Declarations Section (REQUIRED)

The Declarations section must appear before the bibliography and include all applicable subsections, even if "Not applicable":

```latex
\section*{Declarations}

\subsection*{Funding}
% Grant numbers and funding sources, or "Not applicable"

\subsection*{Conflict of interest}
% Disclose conflicts, or "The authors have no conflicts of interest to declare"

\subsection*{Ethics approval}
% For human/animal research, or "Not applicable"

\subsection*{Consent to participate}
% For human subjects, or "Not applicable"

\subsection*{Consent for publication}
% For identifiable information, or "Not applicable"

\subsection*{Data availability}
% Where data can be accessed, DOIs preferred

\subsection*{Code availability}
% REQUIRED: Repository URL with DOI (Zenodo recommended)
% Example: "The ModelChecker software (version X.Y.Z) is available at
% https://doi.org/10.5281/zenodo.XXXXXXX under the MIT License."

\subsection*{Author contribution}
% CRediT-style or prose description
```

### Back Matter

```latex
\backmatter

% Optional supplementary information
%%\bmhead{Supplementary information}

% Optional acknowledgements
%%\bmhead{Acknowledgements}

% Required: Declarations section (see above)

% Optional: Appendices
%%\begin{appendices}
%%\section{Appendix Title}
%%\end{appendices}

% Required: Bibliography
\bibliography{bibliography/references}
```

## Code and Data Availability

### Code Availability (REQUIRED for Computational Papers)

Springer Nature requires:

1. **Repository**: Deposit code on a persistent repository (Zenodo preferred, GitHub with DOI)
2. **License**: Specify the license
3. **Version**: Reference the specific version used in the paper

**Example Statement**:
```latex
\subsection*{Code availability}
The ModelChecker software (version 1.2.3) is available at
\url{https://doi.org/10.5281/zenodo.XXXXXXX} under the MIT License.
Source code is also available at \url{https://github.com/user/repo}.
```

### Data Availability

- Describe where data can be accessed
- Use persistent identifiers (DOIs)
- State "Not applicable" if no datasets were generated

## Figure Requirements

### Format

- Figures must be separate files (not embedded in .tex)
- Supported formats: PDF, PNG, JPG (for pdflatex)
- Use `\graphicspath{{figures/}}` for organization

### Inclusion Pattern

```latex
\graphicspath{{figures/}}

\begin{figure}
\centering
\includegraphics[width=0.8\textwidth]{figure-name}
\caption{Figure caption here.}
\label{fig:figure-name}
\end{figure}
```

## Theorem Environments

The sn-jnl.cls provides three predefined theorem styles:

| Style | Environments | Format |
|-------|--------------|--------|
| `thmstyleone` | theorem, proposition, lemma, corollary | Bold head, italic text |
| `thmstyletwo` | example, remark | Roman head, italic text |
| `thmstylethree` | definition | Bold head, roman text |

### Definition Pattern

```latex
\theoremstyle{thmstyleone}
\newtheorem{theorem}{Theorem}
\newtheorem{proposition}[theorem]{Proposition}
\newtheorem{lemma}[theorem]{Lemma}
\newtheorem{corollary}[theorem]{Corollary}

\theoremstyle{thmstyletwo}
\newtheorem{example}{Example}
\newtheorem{remark}{Remark}

\theoremstyle{thmstylethree}
\newtheorem{definition}{Definition}
```

## Submission Checklist

Before submission, verify:

- [ ] Single .tex file (no `\input` or subfile commands)
- [ ] All figures as separate files (PDF/PNG/JPG)
- [ ] Bibliography compiles without errors
- [ ] All cross-references resolve
- [ ] Declarations section complete with all subsections
- [ ] Code availability statement with DOI/URL
- [ ] Author information correct (use `\fnm{}` and `\sur{}` macros)
- [ ] Abstract within word limit
- [ ] Keywords appropriate for JAR

### Files to Submit

1. `paper.tex` - Main manuscript (single file)
2. `paper.pdf` - Compiled PDF
3. `references.bib` - Bibliography file
4. `sn-jnl.cls` - Document class
5. `sn-mathphys-num.bst` - Bibliography style
6. All figure files from `figures/` directory

## References

- [Journal of Automated Reasoning](https://www.springer.com/journal/10817)
- [Springer Nature Author Guidelines](https://www.springer.com/gp/authors-editors)
- Template User Manual: `latex/assets/user-manual.pdf`
