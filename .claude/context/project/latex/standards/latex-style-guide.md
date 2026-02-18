# LaTeX Style Guide

## Document Class

### Main Document

```latex
\documentclass[pdflatex,sn-mathphys-num]{sn-jnl}
```

The sn-jnl.cls document class is used for Springer Nature journal submissions. See `sn-article-requirements.md` for complete configuration options.

## Required Packages

### Core Packages (included in paper.tex)

```latex
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
```

### Packages Loaded by sn-jnl.cls

These are automatically available:
- `natbib` - Citation management
- `hyperref` - Hyperlinks and PDF metadata

## Formatting Rules

### Line Length

- Source lines: 100 characters maximum
- Break long equations using `align` environment

### Indentation

- Use 2 spaces for LaTeX source indentation
- Align `&` in multi-line equations

### Spacing

- One blank line between paragraphs
- Two blank lines before `\section`
- One blank line before `\subsection`

### Comments

```latex
% Single-line comment for brief notes

% ============================================================
% Section comments for major divisions
% ============================================================
```

## Source File Formatting

### Semantic Linefeeds

Use **one sentence per line** in LaTeX source files. This convention, also called "semantic linefeeds," was documented by Brian Kernighan in 1974 and remains a best practice for technical writing.

**Rationale**:
1. **Version control**: Git diffs show only changed sentences, not entire paragraphs
2. **Editor efficiency**: Text editors manipulate lines easily; sentences become natural units
3. **Review clarity**: Pull request reviews can comment on specific sentences
4. **No output impact**: LaTeX ignores single line breaks in compiled output

**Rules**:
1. Each sentence starts on a new line
2. A period (or other sentence-ending punctuation) is always followed by a line break
3. Long sentences may break at natural clause boundaries (after commas, semicolons, or conjunctions)
4. Do not use automatic line wrapping/reflow
5. Preserve protected spaces before citations: `text~\cite{foo}`

### Pass Example

```latex
Modal logic extends classical logic with operators for necessity and possibility.
The box operator $\Box$ expresses metaphysical necessity,
while the diamond operator $\Diamond$ expresses possibility.

These operators satisfy the duality $\Diamond \varphi \leftrightarrow \neg\Box\neg\varphi$.
```

### Fail Example

```latex
% Bad: Multiple sentences on one line, hard to diff
Modal logic extends classical logic with operators for necessity and possibility. The box operator $\Box$ expresses metaphysical necessity, while the diamond operator $\Diamond$ expresses possibility. These operators satisfy the duality $\Diamond \varphi \leftrightarrow \neg\Box\neg\varphi$.
```

### Long Sentence Guidelines

Break long sentences at natural clause boundaries:

```latex
% Good: Breaks at clause boundary (after comma)
The canonical model construction proceeds by first extending the consistent set
to a maximal consistent set,
then defining the accessibility relation via modal witnesses.

% Good: Break at conjunction
A frame is reflexive if every world accesses itself,
and transitive if accessibility composes.
```

## Theorem and Definition Naming

### Named Theorem Formatting

When referencing theorems by name, use consistent formatting:

| Context | Format | Example |
|---------|--------|---------|
| Prose reference | *Italics* | the *Soundness Theorem* states... |
| Environment name | Normal (in brackets) | `\begin{theorem}[Soundness]` |

### Pass Example

```latex
The \emph{Soundness Theorem} establishes that provable formulas are valid.

\begin{theorem}[Soundness]\label{thm:soundness}
If $\Gamma \vdash \varphi$ then $\Gamma \models \varphi$.
\end{theorem}
```

### Fail Example

```latex
% Bad: Inconsistent formatting
The Soundness Theorem establishes that provable formulas are valid.
\begin{theorem}[\emph{Soundness}]  % Wrong: italics inside bracket
```

### Definition Ordering

Definitions must appear before their first use in prose. When introducing new concepts, place the formal definition environment before explanatory text that references the defined term.

**Rationale**: Readers should encounter the formal definition before informal explanations that assume familiarity with it.

### Pass Example

```latex
\begin{definition}[Model]\label{def:model}
A \emph{model} is a structure $\mathcal{M} = \langle W, R, V \rangle$...
\end{definition}

A model captures the semantic structure needed for evaluation.
The accessibility relation $R$ determines which worlds are reachable.
```

### Fail Example

```latex
% Bad: Using term before defining it
A model captures the semantic structure needed for evaluation.
The accessibility relation $R$ determines which worlds are reachable.

\begin{definition}[Model]  % Definition comes too late
```

## File Organization

### Single-File Structure

Springer Nature requires a single .tex file. All content must be inline:

```
latex/
├── paper.tex              # Main document (all content inline)
├── latexmkrc              # Build configuration
├── sn-jnl.cls             # Document class
├── sn-mathphys-num.bst    # Bibliography style
├── bibliography/
│   └── references.bib     # Reference database
├── figures/               # Figure files
└── assets/                # Template backup files
```

## Code Quality

### Pass Example

```latex
\begin{definition}[Frame]
A \emph{frame} is a structure $\mathcal{F} = \langle W, R \rangle$ where:
\begin{itemize}
  \item $W$ is a nonempty set of \emph{worlds}
  \item $R \subseteq W \times W$ is an \emph{accessibility relation}
\end{itemize}
\end{definition}
```

### Fail Example

```latex
% Bad: No environment, poor formatting
A frame is F = <W, R> where W is worlds and R is accessibility.
```

## Validation Checklist

- [ ] One sentence per line (semantic linefeeds)
- [ ] All packages imported in preamble
- [ ] Theorem environments use sn-jnl styles (thmstyleone, thmstyletwo, thmstylethree)
- [ ] Environments properly opened and closed
- [ ] Cross-references resolve without warnings
- [ ] No overfull hboxes in compiled output
- [ ] Named theorems use italics in prose, normal text in environment brackets
- [ ] Definitions appear before first use in prose
- [ ] Single .tex file (no `\input` or `\include` commands)
