# Implementation Plan: Task #37

- **Task**: 37 - Add formal definitions, complexity analysis, and experimental setup
- **Status**: [NOT STARTED]
- **Effort**: 2.5 hours
- **Dependencies**: None
- **Research Inputs**: specs/037_add_formal_definitions_and_complexity/reports/01_formal-definitions-research.md
- **Artifacts**: plans/01_formal-content-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: latex
- **Lean Intent**: false

## Overview

This plan addresses three critical gaps in `latex/paper.tex` that JAR reviewers will expect: formal definition of hyperintensionality, complexity analysis of the model checking algorithm, and experimental setup for benchmark reproducibility.
The research report provides ready-to-insert LaTeX snippets with literature citations.
Implementation follows priority order from the research: experimental setup (highest risk of desk rejection), hyperintensionality definition, complexity analysis.

### Research Integration

- Report: `reports/01_formal-definitions-research.md` (integrated v1, 2024-03-24)
- Key findings: Ladner 1977 and Knudstorp 2023 provide complexity citations; Fine 2017 provides hyperintensionality definition; experimental setup template requires user input for hardware specs

## Goals & Non-Goals

**Goals**:
- Add formal Definition environment for "hyperintensional operator"
- Add complexity analysis subsection with PSPACE/decidability citations
- Add experimental setup paragraph with hardware/software specifications
- Add required bibliography entries (ladner1977, knudstorp2023)
- Follow semantic linefeeds convention (one sentence per line)

**Non-Goals**:
- Rewriting existing sections
- Adding new theorems or proofs beyond the definition
- Changing document structure or section order
- Adding content beyond the three identified gaps

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Experimental setup placeholders not filled | H | M | Add clear [INSERT: ...] markers, note in commit |
| Definition conflicts with existing notation | M | L | Check macro definitions (lines 74-156) before inserting |
| Bibliography entries cause compilation errors | M | L | Validate BibTeX syntax, test compilation |
| Line number drift from future edits | L | M | Use descriptive anchors (after subsection X), not exact lines |

## Implementation Phases

### Phase 1: Add Experimental Setup Paragraph [COMPLETED]

**Goal**: Add experimental setup paragraph at the start of Section 7 (Results) before subsection 7.1, addressing the highest-priority gap that could cause desk rejection.

**Tasks**:
- [ ] Read current Section 7 structure (lines 1044-1100 of paper.tex)
- [ ] Insert experimental setup paragraph after line 1045 (after `\section{Implementation Results and Empirical Validation}`)
- [ ] Use research report template (Appendix A.1) with [INSERT: ...] placeholders
- [ ] Follow semantic linefeeds: one sentence per line

**Timing**: 30 minutes

**Files to modify**:
- `latex/paper.tex` - Insert ~15 lines after line 1045

**LaTeX Content**:
```latex
\paragraph{Experimental Setup.}
All experiments were conducted on the following configuration:
\begin{itemize}
    \item \textbf{Hardware}: [INSERT: CPU model, e.g., Intel Core i7-12700K @ 3.6GHz], [INSERT: RAM, e.g., 32GB DDR4-3200], [INSERT: OS, e.g., Ubuntu 22.04 LTS]
    \item \textbf{Software}: Python [INSERT: version, e.g., 3.11.4], Z3 [INSERT: version, e.g., 4.12.2], \modelchecker{} version [INSERT: version or commit hash]
    \item \textbf{Methodology}: Each example was executed [INSERT: number] times; reported times are [INSERT: mean/median] wall-clock time in seconds.
    Standard deviation is reported where applicable.
    \item \textbf{Timeout}: Default timeout of 60 seconds per example; examples exceeding this threshold are marked as timeouts.
    \item \textbf{Reproducibility}: All experiments are reproducible via \texttt{make benchmark} in the repository; random seed fixed at [INSERT: seed value] for deterministic model iteration.
\end{itemize}
```

**Verification**:
- Paragraph appears at start of Section 7, before subsection 7.1
- [INSERT: ...] placeholders are clearly marked
- Document compiles without errors

---

### Phase 2: Add Hyperintensionality Definition [NOT STARTED]

**Goal**: Add formal Definition 1 and accompanying Remark in Section 6, after the philosophical background introduces "what makes them true or false" (line 911).

**Tasks**:
- [ ] Read Section 6.1 context (lines 909-926 of paper.tex)
- [ ] Insert Definition environment after line 911 (after "what makes them true or false.")
- [ ] Insert Remark environment listing hyperintensional operators
- [ ] Verify macro usage: `\nec`, `\propident`, `\ground`, `\relimpl`, `\theorylogos`

**Timing**: 45 minutes

**Files to modify**:
- `latex/paper.tex` - Insert ~25 lines after line 911

**LaTeX Content**:
```latex
\begin{definition}[Hyperintensional Operator]\label{def:hyperintensional}
An operator $\mathcal{O}$ is \emph{hyperintensional} if there exist formulas $A$ and $B$ such that:
\begin{enumerate}
    \item $A$ and $B$ are necessarily equivalent: $\nec(A \leftrightarrow B)$, yet
    \item $\mathcal{O}(A)$ and $\mathcal{O}(B)$ may differ in truth-value.
\end{enumerate}
Equivalently, substitution of necessary equivalents within the scope of $\mathcal{O}$ does not preserve truth.
\end{definition}

\begin{remark}[Hyperintensional Operators in \theorylogos{}]\label{rem:hyperintensional-operators}
The following \theorylogos{} operators are hyperintensional:
\begin{itemize}
    \item \textbf{Conjunction} ($\land$): $A \land B$ and $B \land A$ are necessarily equivalent but may have distinct verifiers, hence $\lneg((A \land B) \propident (B \land A))$ is satisfiable.
    \item \textbf{Propositional identity} ($\propident$): $A \propident B$ requires identical verifiers \emph{and} falsifiers, not merely necessary equivalence.
    \item \textbf{Ground} ($\ground$): $A \ground B$ requires every verifier of $B$ to contain a verifier of $A$ as a part.
    \item \textbf{Relevant implication} ($\relimpl$): Requires subject-matter overlap beyond material truth.
\end{itemize}
These distinctions arise from bilateral evaluation: propositions are characterized by their exact verifiers and falsifiers, not merely their truth-values across possible worlds.
\end{remark}
```

**Verification**:
- Definition numbered as Definition 1 (first in document)
- Cross-references (`\ref{def:hyperintensional}`, `\ref{rem:hyperintensional-operators}`) resolve
- Macros render correctly in compiled PDF

---

### Phase 3: Add Complexity Analysis Section [NOT STARTED]

**Goal**: Add complexity classification subsection in Section 2 after subsection 2.5 (Computational Complexity), before Section 3.

**Tasks**:
- [ ] Read Section 2.5 end context (lines 509-518 of paper.tex)
- [ ] Insert new subsection 2.6 "Complexity Classification" after line 514 (before Section 3 separator)
- [ ] Add Proposition for modal fragment complexity with Ladner citation
- [ ] Add table for constraint scaling by primitive arity
- [ ] Add Z3 encoding complexity paragraph

**Timing**: 45 minutes

**Files to modify**:
- `latex/paper.tex` - Insert ~45 lines after line 514

**LaTeX Content**:
```latex
\subsection{Complexity Classification}\label{sec:complexity-classification}

\subsubsection{Decision Problem Complexity}

The satisfiability problem for the modal fragment of \theorylogos{} inherits classical complexity bounds.

\begin{proposition}[Modal Fragment Complexity]
For the modal operators $\nec$ and $\poss$ over S4 frames:
\begin{enumerate}
    \item The satisfiability problem is PSPACE-complete~\cite{ladner1977}.
    \item The finite model property holds.
\end{enumerate}
\end{proposition}

The hyperintensional operators (ground, essence, propositional identity) operate over a finite state lattice, preserving decidability.
Recent work establishes that truthmaker logics on semilattices are decidable with the finite model property~\cite{knudstorp2023}.

\subsubsection{Z3 Encoding Complexity}

The constraint count and quantifier depth grow with parameters $N$ (state space bits) and $K$ (atomic proposition count):

\begin{table}[htbp]
\centering
\caption{Constraint Scaling by Primitive Arity}
\label{tab:constraint-scaling}
\begin{tabular}{@{}lll@{}}
\toprule
\textbf{Primitive Type} & \textbf{Arity} & \textbf{Instantiation Count} \\
\midrule
State predicates (\zpossible{}) & 1 & $O(2^N)$ \\
Evaluation (\zverify{}, \zfalsify{}) & 2 & $O(2^N \cdot K)$ \\
Accessibility (\zaccessible{}) & 2 & $O(2^{2N})$ \\
Fusion (\zfusion{}) & 3 & $O(2^{2N})$ \\
Selection (counterfactuals) & 4 & $O(2^{3N})$ \\
\bottomrule
\end{tabular}
\end{table}

The exponential growth in instantiation count with arity explains the empirical performance degradation observed in Table~\ref{tab:performance}.
Quantifier alternation depth increases with operator nesting: modal operators introduce $\forall w'[\zaccessible(w, w') \imp \ldots]$, while counterfactuals require triple alternation patterns.
```

**Verification**:
- Subsection numbered as 2.6
- Proposition uses correct theorem counter
- Table~\ref{tab:constraint-scaling} resolves correctly
- Cross-reference to Table~\ref{tab:performance} resolves

---

### Phase 4: Add Bibliography Entries [NOT STARTED]

**Goal**: Add required bibliography entries for complexity citations.

**Tasks**:
- [ ] Read current bibliography structure (latex/bibliography/references.bib)
- [ ] Add ladner1977 entry in "Modal and Counterfactual Logic" section
- [ ] Add knudstorp2023 entry in "Truthmaker Semantics" section (or create new section)
- [ ] Verify BibTeX syntax

**Timing**: 15 minutes

**Files to modify**:
- `latex/bibliography/references.bib` - Add 2 entries (~20 lines)

**BibTeX Content**:
```bibtex
@article{ladner1977,
  author       = "Ladner, Richard E.",
  title        = "The Computational Complexity of Provability in Systems of Modal Propositional Logic",
  journal      = "SIAM Journal on Computing",
  volume       = "6",
  number       = "3",
  pages        = "467--480",
  year         = "1977",
  doi          = "10.1137/0206033"
}

@article{knudstorp2023,
  author       = "Knudstorp, S{\o}ren Brinck",
  title        = "Logics of Truthmaker Semantics: Comparison, Compactness and Decidability",
  journal      = "Synthese",
  volume       = "201",
  number       = "206",
  year         = "2023",
  doi          = "10.1007/s11229-023-04401-1"
}
```

**Verification**:
- BibTeX compiles without errors
- Citations resolve in PDF
- Author names render correctly (Ladner, Knudstorp with accent)

---

### Phase 5: Verification and Compilation [NOT STARTED]

**Goal**: Verify all additions compile correctly and integrate properly.

**Tasks**:
- [ ] Run `pdflatex paper.tex` (first pass)
- [ ] Run `bibtex paper` (bibliography)
- [ ] Run `pdflatex paper.tex` (second pass)
- [ ] Run `pdflatex paper.tex` (third pass for cross-references)
- [ ] Verify no overfull hboxes or undefined references
- [ ] Review PDF output for formatting issues

**Timing**: 15 minutes

**Verification**:
- No compilation errors
- All cross-references resolve (no "??" in PDF)
- New definition, proposition, and table appear correctly
- Bibliography entries appear in references section

---

## Testing & Validation

- [ ] Document compiles without errors: `pdflatex paper.tex`
- [ ] Bibliography resolves: `bibtex paper`
- [ ] Cross-references resolve: no "??" warnings on third pass
- [ ] Definition 1 appears in Section 6.1
- [ ] Subsection 2.6 appears before Section 3
- [ ] Experimental setup paragraph appears at start of Section 7
- [ ] Citations \cite{ladner1977} and \cite{knudstorp2023} render correctly
- [ ] Table \ref{tab:constraint-scaling} renders with proper formatting
- [ ] No overfull hbox warnings

## Artifacts & Outputs

- `latex/paper.tex` - Modified with three content additions (~85 lines)
- `latex/bibliography/references.bib` - Modified with two entries (~20 lines)
- `specs/037_add_formal_definitions_and_complexity/plans/01_formal-content-plan.md` - This plan
- `specs/037_add_formal_definitions_and_complexity/summaries/01_formal-content-summary.md` - Execution summary (post-implementation)

## Rollback/Contingency

If implementation causes compilation failures:
1. Revert paper.tex to pre-implementation state: `git checkout HEAD -- latex/paper.tex`
2. Revert references.bib: `git checkout HEAD -- latex/bibliography/references.bib`
3. Diagnose specific LaTeX error from compilation log
4. Apply fixes incrementally, testing compilation after each change

If content placement is incorrect:
1. Move content to correct location based on section labels
2. Adjust cross-references if needed
3. Re-verify compilation
