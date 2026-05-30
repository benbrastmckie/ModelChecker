# Research Report: Formal Definitions, Complexity Analysis, and Experimental Setup

**Task**: 37
**Date**: 2024-03-24
**Focus**: Add missing technical content for JAR submission

---

## Executive Summary

This report addresses three critical gaps in `latex/paper.tex` that JAR reviewers will expect:

1. **Formal definition of hyperintensionality** - The term is used throughout but never formally defined
2. **Complexity analysis** - No formal complexity bounds for the decision problem or Z3 encoding
3. **Experimental setup** - Tables present timing data with no hardware/software specifications

---

## 1. Formal Definition of Hyperintensionality

### 1.1 Source Material

From the Typst manual (`Theory/typst/manual/chapters/02-constitutive.typ`), the key characterization is:

> The semantics is _hyperintensional_, distinguishing propositions that agree in truth-value across all possibilities while differing in subject-matter.

The manual further clarifies (lines 339-342):

> It is characteristic of hyperintensional semantics to consider impossible states in addition to possible states. [...] This allows the semantics to distinguish propositions that agree in truth-value across all possible worlds but differ in their subject-matter or content.

### 1.2 Standard Definition from Literature

The Stanford Encyclopedia of Philosophy and standard literature define hyperintensionality as:

**Definition**: An operator O is *hyperintensional* if and only if there exist formulas A and B such that:
1. A and B are logically/necessarily equivalent (true in exactly the same possible worlds), yet
2. O(A) and O(B) may differ in truth-value

Equivalently: O is hyperintensional iff substitution of necessary equivalents fails to preserve truth.

### 1.3 Hyperintensional Operators in Logos

From the paper and manual, the following operators are hyperintensional:

| Operator | Symbol | Why Hyperintensional |
|----------|--------|---------------------|
| Conjunction | A AND B | Different verifiers than B AND A |
| Propositional Identity | A === B | Requires same verifiers AND falsifiers |
| Ground | A GROUND B | Requires verifier containment |
| Essence | A ESSENCE B | Requires necessary grounding |
| Relevant Implication | A R-> B | Requires subject-matter overlap |

**Key Example**: Conjunction commutativity fails: A AND B !== B AND A because while they have the same truth-value in all worlds, they may have different exact verifiers.

### 1.4 Recommended LaTeX Content

**Placement**: Add as Definition 1 in Section 6 (Case Study: Logos Theory), after line 911 (after "what makes them true or false").

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
    \item \textbf{Conjunction} ($\land$): $A \land B$ and $B \land A$ are necessarily equivalent but may have distinct verifiers, hence $\lnot((A \land B) \propident (B \land A))$ is satisfiable.
    \item \textbf{Propositional identity} ($\propident$): $A \propident B$ requires identical verifiers \emph{and} falsifiers, not merely necessary equivalence.
    \item \textbf{Ground} ($\ground$): $A \ground B$ requires every verifier of $B$ to contain a verifier of $A$ as a part.
    \item \textbf{Relevant implication} ($\relimpl$): Requires subject-matter overlap beyond material truth.
\end{itemize}
These distinctions arise from bilateral evaluation: propositions are characterized by their exact verifiers and falsifiers, not merely their truth-values across possible worlds.
\end{remark}
```

---

## 2. Complexity Analysis

### 2.1 Known Complexity Results for Modal Logic

From the web search and literature:

| Logic | Satisfiability Complexity | Source |
|-------|--------------------------|--------|
| K, T, B, S4 | PSPACE-complete | Ladner 1977 |
| S5 | NP-complete | Ladner 1977 |
| Multi-modal with common knowledge | EXPTIME-complete | Halpern & Moses |
| Bimodal K x K | EXPTIME-hard | Various |

**Key reference**: Ladner, R. E. (1977). "The Computational Complexity of Provability in Systems of Modal Propositional Logic." SIAM Journal on Computing, 6(3), 467-480.

### 2.2 Truthmaker Semantics Complexity

From Knudstorp (2023), "Logics of Truthmaker Semantics: Comparison, Compactness and Decidability" (Synthese):

- Truthmaker consequence on semilattices is **decidable**
- The logic has the **finite model property**
- Standard translations into first-order logic exist

The propositional fragment of HYPE (Leitgeb's hyperintensional logic) is also decidable with the finite model property.

### 2.3 Z3 Encoding Complexity Analysis

For the ModelChecker's Z3 encoding:

**State Space**: With N bits, there are 2^N possible states.

**Constraint Scaling**:
- Unary predicates (e.g., `possible`): O(2^N) instantiations
- Binary predicates (e.g., `verify`, `accessible`): O(2^N * K) where K = number of atomic propositions
- Ternary predicates (e.g., `fusion`): O(2^(2N)) instantiations

**Quantifier Structure**:
- Frame constraints use universal quantification over states: ForAll s[...]
- Modal operators nest quantifiers: ForAll w[ForAll w'[R(w,w') -> ...]]
- Counterfactuals require triple nesting with selection functions

**Empirical Complexity** (from paper Table 4):
| N | States | Avg Time | Timeout Rate |
|---|--------|----------|--------------|
| 3 | 8 | 0.3s | 0% |
| 4 | 16 | 1.8s | 2% |
| 5 | 32 | 8.5s | 12% |
| 6 | 64 | 45.2s | 35% |
| 7 | 128 | 180+s | 68% |

The exponential growth in solving time suggests the encoding complexity is at least EXPTIME in the state space size.

### 2.4 Recommended LaTeX Content

**Placement**: Add as new subsection 2.6 after existing Section 2.5 (line ~518), or integrate into Section 2.5 "Computational Complexity".

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

**Bibliography additions** (add to references.bib):

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

---

## 3. Experimental Setup

### 3.1 Current Gap

Tables 4 (tab:performance), 6 (tab:optimization), and 7 (tab:inference-comparison) present timing data with no specification of:
- Hardware configuration
- Software versions
- Statistical methodology
- Timeout configuration

This is explicitly noted as a potential desk rejection criterion.

### 3.2 Recommended Experimental Setup Paragraph

**Placement**: Add at the start of Section 7 (Results), before subsection 7.1 (line 1046).

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

### 3.3 Additional Recommendations

1. **Report standard deviation** for timing tables (Table 4)
2. **Clarify "average across 50 examples"** - which 50 examples? Random sample? Representative selection?
3. **Add confidence intervals** for timeout rates
4. **Specify warm-up runs** if any (JIT compilation effects)

---

## 4. Implementation Recommendations

### 4.1 Priority Order

1. **Experimental Setup** (HIGHEST) - Most likely to cause desk rejection
2. **Formal Hyperintensionality Definition** (HIGH) - Core concept left undefined
3. **Complexity Analysis** (MEDIUM) - Enhances rigor but less critical

### 4.2 File Modifications

| File | Lines | Change |
|------|-------|--------|
| `latex/paper.tex` | ~1046 | Add experimental setup paragraph |
| `latex/paper.tex` | ~911-925 | Add Definition 1 (hyperintensional) |
| `latex/paper.tex` | ~518 | Add complexity subsection 2.6 |
| `latex/bibliography/references.bib` | EOF | Add ladner1977, knudstorp2023 |

### 4.3 Placeholders Requiring User Input

The experimental setup paragraph contains `[INSERT: ...]` placeholders that require actual system information:
- CPU model and speed
- RAM amount and type
- Operating system version
- Python version
- Z3 version
- Number of trials
- Mean vs median choice
- Random seed value

---

## 5. Sources

### Academic References
- Ladner, R. E. (1977). "The Computational Complexity of Provability in Systems of Modal Propositional Logic." SIAM Journal on Computing, 6(3), 467-480.
- Knudstorp, S. B. (2023). "Logics of Truthmaker Semantics: Comparison, Compactness and Decidability." Synthese, 201(206).
- Fine, K. (2017). "Truthmaker Semantics." In A Companion to the Philosophy of Language (2nd ed.).
- Stanford Encyclopedia of Philosophy: "Hyperintensionality"

### Web Resources
- [Logics of Truthmaker Semantics (Springer)](https://link.springer.com/article/10.1007/s11229-023-04401-1)
- [Characterizing the NP-PSPACE Gap in Modal Logic (IJCAI 2007)](https://www.ijcai.org/Proceedings/07/Papers/371.pdf)
- [Z3: An Efficient SMT Solver (Springer)](https://link.springer.com/chapter/10.1007/978-3-540-78800-3_24)
- [HYPE: A System of Hyperintensional Logic (JPhL)](https://link.springer.com/article/10.1007/s10992-018-9467-0)

### Project Sources
- `/home/benjamin/Projects/Logos/Theory/typst/manual/chapters/02-constitutive.typ` (lines 10, 339-342)
- `/home/benjamin/Projects/Logos/Theory/typst/manual/chapters/01-introduction.typ` (lines 22, 37)
- `/home/benjamin/Projects/Logos/ModelChecker/latex/paper.tex` (current state)

---

## Appendix: Complete LaTeX Snippets

### A.1 Experimental Setup (Ready to Insert)

```latex
\paragraph{Experimental Setup.}
All experiments were conducted on the following configuration:
\begin{itemize}
    \item \textbf{Hardware}: [CPU], [RAM], [OS]
    \item \textbf{Software}: Python [version], Z3 [version], \modelchecker{} [version]
    \item \textbf{Methodology}: Each example was executed [N] times; reported times are [mean/median] wall-clock time in seconds with standard deviation where applicable.
    \item \textbf{Timeout}: Default timeout of 60 seconds per example.
    \item \textbf{Reproducibility}: All experiments are reproducible via \texttt{make benchmark}; random seed [value] ensures deterministic iteration.
\end{itemize}
```

### A.2 Hyperintensionality Definition (Ready to Insert)

```latex
\begin{definition}[Hyperintensional Operator]\label{def:hyperintensional}
An operator $\mathcal{O}$ is \emph{hyperintensional} if there exist formulas $A$ and $B$ such that $\nec(A \leftrightarrow B)$ holds (necessary equivalence) yet $\mathcal{O}(A)$ and $\mathcal{O}(B)$ may differ in truth-value.
\end{definition}

\begin{example}[Hyperintensional Conjunction]
In \theorylogos{}, conjunction is hyperintensional: $A \land B$ and $B \land A$ are necessarily equivalent but may have distinct exact verifiers, so $(A \land B) \propident (B \land A)$ fails.
\end{example}
```

### A.3 Bibliography Entries (Ready to Insert)

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
