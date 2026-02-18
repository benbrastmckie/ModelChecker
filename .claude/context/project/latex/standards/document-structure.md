# Document Structure Standards

## Overview

This document describes the structure of the ModelChecker paper using the Springer Nature sn-jnl.cls template. The key constraint is that Springer requires submission as a **single .tex file** with no external includes.

## Single-File Structure

### paper.tex Layout

```latex
%Version 3.1 December 2024
% Springer Nature Journal Article Template

%%=======================================================%%
%% Document class options                                %%
%%=======================================================%%
\documentclass[pdflatex,sn-mathphys-num]{sn-jnl}

%%=======================================================%%
%% Path configuration                                    %%
%%=======================================================%%
\graphicspath{{figures/}}

%%=======================================================%%
%% Packages                                              %%
%%=======================================================%%
\usepackage{graphicx}
\usepackage{multirow}
\usepackage{amsmath,amssymb,amsfonts}
\usepackage{amsthm}
\usepackage{mathrsfs}
\usepackage[title]{appendix}
\usepackage{xcolor}
\usepackage{textcomp}
\usepackage{manyfoot}
\usepackage{booktabs}
\usepackage{algorithm}
\usepackage{algorithmicx}
\usepackage{algpseudocode}
\usepackage{listings}

%%=======================================================%%
%% Project-specific packages                             %%
%%=======================================================%%
%% Add any additional packages here

%%=======================================================%%
%% Theorem environments                                  %%
%%=======================================================%%
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

\raggedbottom

\begin{document}

%%=======================================================%%
%% Title and Authors                                     %%
%%=======================================================%%
\title[Short Title]{Full Title}
\author*[1]{\fnm{First} \sur{Last}}\email{email@example.com}
\affil*[1]{\orgdiv{Department}, \orgname{University},
  \orgaddress{\city{City}, \state{State}, \country{Country}}}

%%=======================================================%%
%% Abstract and Keywords                                 %%
%%=======================================================%%
\abstract{Abstract text here.}
\keywords{keyword1, keyword2, keyword3}
\maketitle

%%=======================================================%%
%% Main Content                                          %%
%%=======================================================%%
\section{Introduction}\label{sec:intro}
\section{Background}\label{sec:background}
\section{Main Content}\label{sec:main}
\section{Implementation}\label{sec:implementation}
\section{Evaluation}\label{sec:evaluation}
\section{Conclusion}\label{sec:conclusion}

%%=======================================================%%
%% Back Matter                                           %%
%%=======================================================%%
\backmatter

\section*{Declarations}
\subsection*{Funding}
\subsection*{Conflict of interest}
\subsection*{Ethics approval}
\subsection*{Consent to participate}
\subsection*{Consent for publication}
\subsection*{Data availability}
\subsection*{Code availability}
\subsection*{Author contribution}

%%\begin{appendices}
%%\section{Appendix Title}\label{sec:appendix}
%%\end{appendices}

\bibliography{bibliography/references}

\end{document}
```

## Section Hierarchy

```
\section{Major Division}           % Level 1
  \subsection{Sub-topic}           % Level 2
    \subsubsection{Detail}         % Level 3
      \paragraph{Fine point}       % Level 4 (rare)
```

## Content Organization

### Section Content Flow

1. **Introduction paragraph**: Brief overview of section purpose
2. **Definitions**: Formal definitions using `definition` environment
3. **Theorems/Lemmas**: Formal results with proofs
4. **Remarks**: Clarifying notes using `remark` environment
5. **Examples**: Illustrative cases (when helpful)

### Subsection Guidelines

- Each subsection should be self-contained
- Start with context for the concept
- Provide formal definitions before theorems that use them
- Use semantic linefeeds (one sentence per line)

## Front Matter

### Title Page Elements

```latex
\title[Short Title for Header]{Full Paper Title}

\author*[1]{\fnm{First} \sur{Last}}\email{author@example.com}

\affil*[1]{\orgdiv{Department}, \orgname{University},
  \orgaddress{\city{City}, \state{State}, \country{Country}}}
```

**Note**: Use `*` for corresponding author. Use `\fnm{}` for first name and `\sur{}` for surname.

### Abstract and Keywords

```latex
\abstract{
Abstract text goes here.
The abstract serves as a general introduction and brief summary of main results.
Check JAR guidelines for length limits.
}

\keywords{model checking, modal logic, counterfactual logic, SMT solver, Z3}
```

## Back Matter

### Declarations Section

Required subsections (include all, even if "Not applicable"):

1. **Funding** - Grant numbers and funding sources
2. **Conflict of interest** - Any competing interests
3. **Ethics approval** - For human/animal research
4. **Consent to participate** - For human subjects
5. **Consent for publication** - For identifiable information
6. **Data availability** - Where data can be accessed
7. **Code availability** - Repository URL with DOI (REQUIRED)
8. **Author contribution** - CRediT-style or prose description

### Appendices

```latex
\begin{appendices}
\section{Proofs}\label{app:proofs}
Appendix content here.
\end{appendices}
```

### Bibliography

```latex
\bibliography{bibliography/references}
```

- BibTeX format in `bibliography/references.bib`
- Cite using `\cite{key}`
- Style: sn-mathphys-num (numbered citations)

## Cross-References

### Internal References

```latex
\label{def:model}              % Label definitions
\label{thm:soundness}          % Label theorems
\label{eq:semantics}           % Label equations
\label{sec:intro}              % Label sections

\ref{def:model}                % Reference by number
See Section~\ref{sec:intro}    % With name
Equation~(\ref{eq:semantics})  % Parenthetical
```

### Label Conventions

| Prefix | Element Type | Example |
|--------|-------------|---------|
| `def:` | Definition | `\label{def:model}` |
| `thm:` | Theorem | `\label{thm:soundness}` |
| `lem:` | Lemma | `\label{lem:auxiliary}` |
| `prop:` | Proposition | `\label{prop:main}` |
| `sec:` | Section | `\label{sec:intro}` |
| `eq:` | Equation | `\label{eq:semantics}` |
| `fig:` | Figure | `\label{fig:diagram}` |
| `tab:` | Table | `\label{tab:results}` |

## Prohibited Patterns

### No External Includes

Springer requires a single .tex file. Do NOT use:

```latex
% PROHIBITED:
\input{section.tex}
\include{chapter.tex}
\subfile{content.tex}
\usepackage{subfiles}
```

All content must be inline in paper.tex.

## Compilation

### Quick Build

```bash
cd latex
latexmk -pdf paper.tex
```

### Manual Build (with bibliography)

```bash
cd latex
pdflatex paper.tex
bibtex paper
pdflatex paper.tex
pdflatex paper.tex
```

### Clean Up

```bash
latexmk -c          # Clean auxiliary files, keep PDF
latexmk -C          # Clean everything including PDF
```
