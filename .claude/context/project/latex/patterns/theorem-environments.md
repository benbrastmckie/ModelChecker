# Theorem Environment Patterns

## Overview

The Springer Nature sn-jnl.cls document class provides three predefined theorem styles. This document describes their usage for the ModelChecker paper.

## sn-jnl Theorem Styles

### Style Overview

| Style | Environments | Head Format | Body Format |
|-------|--------------|-------------|-------------|
| `thmstyleone` | theorem, proposition, lemma, corollary | Bold | Italic |
| `thmstyletwo` | example, remark | Roman | Italic |
| `thmstylethree` | definition | Bold | Roman |

### Environment Definitions

```latex
% In preamble of paper.tex

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

**Note**: Theorem, proposition, lemma, and corollary share a counter (`[theorem]`).
Example, remark, and definition have separate counters.

## Definition Environment

### Basic Definition

```latex
\begin{definition}[Model]\label{def:model}
A \emph{model} is a tuple $\mathcal{M} = \langle W, R, V \rangle$ where:
\begin{itemize}
  \item $W$ is a nonempty set of worlds
  \item $R \subseteq W \times W$ is an accessibility relation
  \item $V : \mathrm{Prop} \to \mathcal{P}(W)$ is a valuation function
\end{itemize}
\end{definition}
```

### Definition with Subsequent Remark

```latex
\begin{definition}[Semantic Entailment]\label{def:entailment}
We write $\Gamma \models \varphi$ if for every model $\mathcal{M}$ and world $w$,
if $\mathcal{M}, w \models \psi$ for all $\psi \in \Gamma$,
then $\mathcal{M}, w \models \varphi$.
\end{definition}

\begin{remark}
This definition extends to sets of formulas on the right:
$\Gamma \models \Delta$ means $\Gamma \models \varphi$ for all $\varphi \in \Delta$.
\end{remark}
```

## Theorem Environment

### Theorem Statement

```latex
\begin{theorem}[Soundness]\label{thm:soundness}
If $\Gamma \vdash \varphi$ then $\Gamma \models \varphi$.
\end{theorem}

\begin{proof}
By induction on the length of derivations.
The base case holds by definition of the valuation.
For the inductive step, we verify each inference rule preserves validity.
\end{proof}
```

### Theorem with Multiple Parts

```latex
\begin{theorem}[Model Properties]\label{thm:model-properties}
Let $\mathcal{M}$ be a model. Then:
\begin{enumerate}
  \item $\mathcal{M} \models \varphi \lor \neg\varphi$ for all $\varphi$
  \item $\mathcal{M} \models \neg(\varphi \land \neg\varphi)$ for all $\varphi$
  \item If $\mathcal{M} \models \varphi \to \psi$ and $\mathcal{M} \models \varphi$,
        then $\mathcal{M} \models \psi$
\end{enumerate}
\end{theorem}
```

## Lemma and Proposition

### Lemma (Auxiliary Result)

```latex
\begin{lemma}[Extension]\label{lem:extension}
Every consistent set of formulas can be extended to a maximal consistent set.
\end{lemma}

\begin{proof}
By Zorn's lemma applied to the set of consistent extensions ordered by inclusion.
\end{proof}
```

### Proposition (Important but Non-Central)

```latex
\begin{proposition}[Monotonicity]\label{prop:monotonicity}
If $\Gamma \subseteq \Delta$ and $\Gamma \vdash \varphi$, then $\Delta \vdash \varphi$.
\end{proposition}
```

### Corollary (Direct Consequence)

```latex
\begin{corollary}\label{cor:completeness}
If $\Gamma \models \varphi$ then $\Gamma \vdash \varphi$.
\end{corollary}

\begin{proof}
Immediate from Theorem~\ref{thm:completeness} and Lemma~\ref{lem:extension}.
\end{proof}
```

## Example and Remark

### Example

```latex
\begin{example}[Modal Validity]
The formula $\Box p \to p$ is valid in all reflexive frames.
Consider $\mathcal{M} = \langle W, R, V \rangle$ where $R$ is reflexive.
For any $w \in W$: if $\mathcal{M}, w \models \Box p$,
then $\mathcal{M}, w \models p$ since $wRw$.
\end{example}
```

### Remark

```latex
\begin{remark}
The converse of Theorem~\ref{thm:soundness} requires additional axioms.
See Section~\ref{sec:completeness} for the completeness proof.
\end{remark}
```

## Proof Environment

### Standard Proof

```latex
\begin{proof}
Let $\varphi$ be arbitrary.
We proceed by structural induction on $\varphi$.
\textbf{Base case}: When $\varphi$ is atomic, the result holds by definition.
\textbf{Inductive step}: Assume the result holds for subformulas.
Case analysis on the main connective completes the proof.
\end{proof}
```

### Proof with Named Steps

```latex
\begin{proof}
We establish three claims.

\textbf{Claim 1}: Every model satisfies the axiom K.
\emph{Proof}: Direct verification using the semantics of $\Box$.

\textbf{Claim 2}: Modus ponens preserves validity.
\emph{Proof}: If $\models \varphi$ and $\models \varphi \to \psi$, then $\models \psi$.

\textbf{Claim 3}: Necessitation preserves validity.
\emph{Proof}: If $\models \varphi$, then $\models \Box\varphi$.

The theorem follows from these three claims.
\end{proof}
```

## Environment Usage Guidelines

| Environment | Use When |
|-------------|----------|
| `definition` | Introducing formal concepts |
| `theorem` | Stating main results |
| `lemma` | Auxiliary results for proofs |
| `proposition` | Important but supporting results |
| `corollary` | Immediate consequences of theorems |
| `remark` | Clarifications and observations |
| `example` | Concrete illustrations |

## Cross-Reference Pattern

```latex
\begin{definition}[Frame]\label{def:frame}
A \emph{frame} is a pair $\mathcal{F} = \langle W, R \rangle$.
\end{definition}

% Later in the document:
By Definition~\ref{def:frame}, frames consist of...

\begin{theorem}[Frame Correspondence]\label{thm:correspondence}
A formula is valid in all reflexive frames iff...
\end{theorem}

% Later:
Theorem~\ref{thm:correspondence} establishes the link between...
```

## Label Conventions

| Prefix | Element Type | Example |
|--------|-------------|---------|
| `def:` | Definition | `\label{def:model}` |
| `thm:` | Theorem | `\label{thm:soundness}` |
| `lem:` | Lemma | `\label{lem:extension}` |
| `prop:` | Proposition | `\label{prop:monotonicity}` |
| `cor:` | Corollary | `\label{cor:completeness}` |

## Formatting Notes

### Mathematical Content

- Use `$...$` for inline math: "the formula $\varphi$"
- Use `\[...\]` or `equation` for displayed math
- Use `align` environment for multi-line equations

### Semantic Linefeeds

Apply one sentence per line in theorem statements:

```latex
\begin{theorem}[Completeness]\label{thm:completeness}
The system is complete with respect to the class of all frames.
That is, if $\models \varphi$ then $\vdash \varphi$.
\end{theorem}
```
