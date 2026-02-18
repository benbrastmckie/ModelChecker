# Cross-Reference Patterns

## Label Conventions

### Label Prefixes

| Prefix | Element Type | Example |
|--------|-------------|---------|
| `def:` | Definition | `\label{def:model}` |
| `thm:` | Theorem | `\label{thm:soundness}` |
| `lem:` | Lemma | `\label{lem:extension}` |
| `prop:` | Proposition | `\label{prop:monotonicity}` |
| `cor:` | Corollary | `\label{cor:completeness}` |
| `eq:` | Equation | `\label{eq:semantics}` |
| `sec:` | Section | `\label{sec:intro}` |
| `tab:` | Table | `\label{tab:results}` |
| `fig:` | Figure | `\label{fig:diagram}` |
| `alg:` | Algorithm | `\label{alg:check}` |

### Label Naming

- Use lowercase
- Hyphenate multi-word names
- Be descriptive but concise

```latex
\label{def:model}                % Good
\label{def:m}                    % Too abbreviated
\label{def:The_Kripke_Model}     % Wrong style
```

## Reference Commands

### Standard References

```latex
% Basic reference (number only)
\ref{def:model}                 % Output: "1"

% With tilde to prevent line break
Definition~\ref{def:model}      % Output: "Definition 1"
Theorem~\ref{thm:soundness}     % Output: "Theorem 2"
Section~\ref{sec:intro}         % Output: "Section 1"
```

### Multiple References

```latex
% Manual listing
Definitions~\ref{def:model} and~\ref{def:frame}

% Range
Sections~\ref{sec:intro}--\ref{sec:conclusion}
```

### Equation References

```latex
% Standard
Equation~(\ref{eq:semantics})   % Output: "Equation (3)"

% Using eqref (auto-parentheses)
\eqref{eq:semantics}            % Output: "(3)"
```

### Page References

```latex
\pageref{def:model}             % Output: "12"
% Use sparingly - prefer section/definition references
```

## Bibliography References

### Citation Commands

```latex
\cite{author2024}               % Standard citation: [1]
\cite[p.~42]{author2024}        % With page: [1, p. 42]
\cite{author2024,other2023}     % Multiple: [1, 2]
```

### Citation Placement

```latex
% At end of sentence (after period looks wrong with numbered citations)
Modal logic was introduced by Lewis~\cite{lewis1918}.

% Mid-sentence
Following Lewis~\cite{lewis1918}, we define...
```

### Protected Space Before Citation

Always use `~` before `\cite` to prevent line breaks:

```latex
% Good
The semantics was developed by Fine~\cite{fine2017}.

% Bad (may break poorly)
The semantics was developed by Fine \cite{fine2017}.
```

## BibTeX Entry Pattern

```bibtex
@article{author2024title,
  author = {Last, First and Other, Second},
  title = {Paper Title},
  journal = {Journal of Automated Reasoning},
  year = {2024},
  volume = {68},
  number = {2},
  pages = {123--145},
  doi = {10.1007/example}
}

@book{author2023book,
  author = {Last, First},
  title = {Book Title},
  publisher = {Springer},
  year = {2023},
  address = {Berlin}
}

@inproceedings{author2024conf,
  author = {Last, First},
  title = {Conference Paper Title},
  booktitle = {Proceedings of Conference},
  year = {2024},
  pages = {1--15},
  publisher = {ACM}
}
```

## Figure and Table References

### Figure Reference

```latex
\begin{figure}
\centering
\includegraphics[width=0.8\textwidth]{diagram}
\caption{System architecture showing the main components.}
\label{fig:architecture}
\end{figure}

% Reference
As shown in Figure~\ref{fig:architecture}, the system consists of...
```

### Table Reference

```latex
\begin{table}
\centering
\caption{Experimental results comparing approaches.}
\label{tab:results}
\begin{tabular}{lcc}
\toprule
Method & Accuracy & Time \\
\midrule
Ours & 95\% & 1.2s \\
Baseline & 82\% & 3.4s \\
\bottomrule
\end{tabular}
\end{table}

% Reference
Table~\ref{tab:results} presents the results...
```

## Algorithm References

```latex
\begin{algorithm}
\caption{Model Checking}\label{alg:check}
\begin{algorithmic}[1]
\Procedure{Check}{$M, \varphi$}
  \State \textbf{return} $M \models \varphi$
\EndProcedure
\end{algorithmic}
\end{algorithm}

% Reference
Algorithm~\ref{alg:check} describes the procedure...
```

## Best Practices

### Do

- Label all definitions, theorems, and important equations
- Use descriptive label names (`def:model` not `def:1`)
- Use `~` before `\ref` and `\cite` to prevent line breaks
- Include page numbers for books in citations

### Don't

- Over-label (skip trivial remarks)
- Use hard-coded numbers ("see Definition 3")
- Use labels that might change meaning
- Forget to run pdflatex twice to resolve references

## Complete Example

```latex
\section{Semantics}\label{sec:semantics}

\begin{definition}[Model]\label{def:model}
A \emph{model} is a tuple $\mathcal{M} = \langle W, R, V \rangle$ where
$W$ is a set of worlds,
$R \subseteq W \times W$ is an accessibility relation,
and $V$ assigns truth values.
\end{definition}

The model structure (Definition~\ref{def:model}) enables evaluation of modal formulas.
This approach follows the tradition established by Kripke~\cite{kripke1963}.

\begin{theorem}[Soundness]\label{thm:soundness}
If $\Gamma \vdash \varphi$ then $\Gamma \models \varphi$.
\end{theorem}

Theorem~\ref{thm:soundness} is proven by induction on derivations.
See Section~\ref{sec:proofs} for the complete proof.
```
