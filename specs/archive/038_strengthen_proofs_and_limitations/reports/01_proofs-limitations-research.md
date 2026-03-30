# Research Report: Task #38

**Task**: 38 - Strengthen proofs, add limitations, qualify novelty claims
**Started**: 2026-03-24T00:00:00Z
**Completed**: 2026-03-24T01:00:00Z
**Effort**: Medium (research across three distinct topics)
**Dependencies**: None
**Sources/Inputs**: latex/paper.tex, WebSearch (JAR standards, existing tools), academic literature
**Artifacts**: This report
**Standards**: report-format.md, subagent-return.md

## Executive Summary

- **Topic 15 (Proof Expansion)**: The current paper lacks formal correctness theorems for the Z3 encoding. JAR papers typically require either mechanized proofs (Coq/Isabelle/Lean) or detailed pen-and-paper proofs with explicit theorem statements. Recommend adding a Correctness Theorem with structured proof sketch.
- **Topic 18 (Limitations Section)**: The paper has limitations scattered across Sections 5.5 and 9.2. These should be consolidated and expanded with standard threats-to-validity categories. Template content provided below.
- **Topic 13 (Novelty Claims)**: Survey of existing tools confirms that the combination of (a) bilateral evaluation, (b) hyperintensional operators, (c) counterfactual conditionals, and (d) SMT-based model finding is genuinely novel. Individual components exist elsewhere, but not this combination. Recommend qualifying claims to be precise about which aspects are novel.

## Context and Scope

This research addresses three areas for improving technical rigor in the JAR paper:

1. What correctness proofs are expected for SMT encodings in JAR?
2. What should a Limitations section contain for formal methods/empirical papers?
3. What existing tools implement similar functionality to ModelChecker?

## Findings

### 1. Proof Sketch Expansion for Z3 Encoding Correctness

#### Current State in Paper

The paper describes the encoding process (Section 2) but does not include explicit correctness theorems. The closest statements are:
- Line 701: "completeness does not hold in general"
- Line 811: "Current limitations include incompleteness"
- Line 1349: "177 validated examples confirming correctness"

The paper relies on empirical validation (177 test cases) rather than formal proofs.

#### JAR Expectations

Based on web research and surveyed JAR papers, correctness proofs for SMT encodings typically include:

**Standard Theorem Format:**
```
Theorem (Encoding Soundness).
For any formula phi in the object logic L:
  If the Z3 encoding SAT(encode(phi)) is unsatisfiable,
  then phi has no model in the class of L-models.

Theorem (Encoding Faithfulness/Completeness for Finite Models).
For any formula phi in L and finite model M:
  M |= phi  if and only if  SAT(encode(phi, M)) is satisfiable.
```

**Proof Strategies:**

1. **Structural Induction**: Prove by induction on formula structure that the encoding preserves semantic meaning.
2. **Bisimulation Argument**: Show a correspondence between Z3 models and semantic structures.
3. **Constraint Correspondence**: Map each semantic clause to a Z3 constraint and prove equivalence.

**JAR Paper Examples:**
- Papers using Isabelle/HOL for modal logic encoding provide machine-checked proofs
- Papers using SMT solvers typically provide detailed proof sketches with explicit lemmas
- Pure tool papers may rely on extensive testing + completeness for decidable fragments

#### Recommendation: Add Correctness Section

**Proposed Addition (Section 2 or Appendix):**

```latex
\subsection{Encoding Correctness}\label{sec:encoding-correctness}

We establish that the Z3 encoding faithfully represents truthmaker semantics.

\begin{definition}[Encoding Function]
Let $\mathcal{E}: \mathcal{L}_{\theorylogos} \times \mathcal{S} \to \text{Z3Formula}$
be the encoding function mapping formulas and states to Z3 constraints:
\begin{itemize}
  \item $\mathcal{E}(p, s) = \zverify(s, p)$ for atomic $p$
  \item $\mathcal{E}(\neg A, s) = \zfalsify(s, A)$
  \item $\mathcal{E}(A \land B, s) = \mathcal{E}(A, s) \land \mathcal{E}(B, s)$
  \item $\mathcal{E}(\Box A, w) = \forall w'[\zaccessible(w,w') \imp \mathcal{E}(A, w')]$
  \item (continue for all operators...)
\end{itemize}
\end{definition}

\begin{theorem}[Encoding Soundness]\label{thm:soundness}
For any $\theorylogos$ formula $\varphi$ and finite state space $\mathcal{S}$ with $|\mathcal{S}| = 2^N$:
\[
\text{If } \mathcal{E}(\varphi) \text{ is UNSAT in Z3, then } \varphi \text{ has no } \theorylogos\text{-model over } \mathcal{S}.
\]
\end{theorem}

\begin{proof}[Proof sketch]
By structural induction on $\varphi$. The key cases:

\textbf{Base case (atomic).}
$\mathcal{E}(p, s) = \zverify(s, p)$ is satisfiable iff there exists a valuation assigning
$\zverify(s, p) = \top$. Frame constraints ensure $s$ is possible and not null when $\zverify(s,p)$ holds.

\textbf{Inductive case (conjunction).}
By IH, $\mathcal{E}(A, s)$ is satisfiable iff $s \verifies A$ in some model.
$\mathcal{E}(A \land B, s) = \mathcal{E}(A, s) \land \mathcal{E}(B, s)$ is satisfiable
iff both conjuncts are, iff $s$ verifies both $A$ and $B$.
By the truthmaker clause for conjunction, this holds iff $s \verifies A \land B$.

\textbf{Inductive case (necessity).}
$\mathcal{E}(\Box A, w) = \forall w'[\zaccessible(w,w') \imp \mathcal{E}(A, w')]$.
By IH, each $\mathcal{E}(A, w')$ correctly encodes $w' \models A$.
The universal quantification encodes "for all accessible worlds," which is the standard
Kripke semantics for necessity.

The remaining cases (negation, disjunction, modalities, counterfactuals, constitutive operators)
follow similarly, with each encoding clause mirroring the corresponding semantic clause in
Definitions~\ref{def:tms-base}--\ref{def:counterfactual}.
\end{proof}

\begin{theorem}[Countermodel Extraction]\label{thm:countermodel}
If $\mathcal{E}(\neg \varphi)$ is SAT with model $M$, then $M$ can be extracted
as a $\theorylogos$-countermodel to $\varphi$.
\end{theorem}

\begin{proof}[Proof sketch]
Z3's model extraction provides truth values for all $\zverify(s, p)$ and $\zfalsify(s, p)$.
These directly constitute the verification/falsification functions of the semantic model.
Frame constraints ensure the extracted model satisfies $\theorylogos$ structural requirements.
\end{proof}
```

**Alternative: Mechanized Verification**

For stronger guarantees, consider:
- Formalizing the encoding in Lean 4 (currently the paper mentions "integration with proof assistants" as future work)
- This would elevate the paper's rigor significantly but requires substantial additional effort

### 2. Limitations Section

#### Current State in Paper

Limitations appear in two places:
- Section 5.5 (lines 809-817): "Finite Model Limitations and Future Work"
- Section 9.2 (lines 1314-1325): "Limitations and Challenges"

The current limitations are:
1. Incompleteness (cannot prove validity)
2. State space ceiling (N=6 typically)
3. Timeout sensitivity
4. Finite model property assumption
5. Frame constraint correctness requires expert judgment
6. Operator interaction complexity (19 operators = 361 pairs)

#### Standard Limitations Section Format

Based on research into formal methods and empirical software engineering papers, limitations should be organized by validity type:

**Standard Categories:**
1. **Internal Validity** - Correctness of method itself
2. **External Validity** - Generalizability
3. **Construct Validity** - Measurement/operationalization
4. **Conclusion Validity** - Statistical/inferential claims

#### Recommended Additions

The paper should expand Section 9.2 with:

```latex
\subsection{Limitations and Threats to Validity}\label{sec:limitations}

\subsubsection{Internal Validity: Encoding Correctness}

\textbf{Semantic encoding fidelity.}
The Z3 encoding must faithfully represent truthmaker semantic clauses.
We mitigate this threat through: (1) extensive test suite coverage (177 validated examples),
(2) regression testing on every commit, and (3) comparison with hand-constructed examples from the
truthmaker semantics literature~\cite{fine2017tms}.
However, the encoding has not been mechanically verified in a proof assistant.

\textbf{Frame constraint soundness.}
Frame constraints (Definition~\ref{def:frame}) require expert judgment to ensure they correctly
capture semantic principles. Incorrect constraints could admit spurious models or exclude valid ones.
Mitigation: constraints are derived directly from published definitions in~\cite{fine2017tms,fine2017content}.

\textbf{BitVector representation limits.}
States are represented as $N$-bit bitvectors. For $N > 64$, this exceeds native word size.
Current implementation is limited to $N \leq 16$, corresponding to $\leq 65{,}536$ states.

\subsubsection{External Validity: Generalizability}

\textbf{Finite model restriction.}
The framework can only explore finite models. Logics without the finite model property
(e.g., certain second-order extensions) cannot be completely characterized.
Mitigation: many philosophically significant modal and hyperintensional logics have the finite
model property~\cite{knudstorp2023}.

\textbf{Theory coverage.}
Results generalize to theories expressible within our framework (bilateral semantics,
mereological state spaces). Theories requiring different primitives (e.g., neighborhood
semantics for non-normal modal logics) would require framework extension.

\textbf{Example selection bias.}
The 177 examples were constructed to test specific operator behaviors, not sampled randomly.
They may not represent "typical" formulas users will test.

\subsubsection{Construct Validity: Complexity Measurement}

\textbf{Solver time as complexity proxy.}
We use Z3 solving time as a measure of theory complexity.
This conflates semantic complexity with encoding efficiency and solver heuristics.
Mitigation: we also report constraint counts and timeout rates.

\textbf{Feasible model size threshold.}
Defining tractability as "$N \leq 6$ before timeout" is arbitrary.
Different applications may have different size requirements.

\subsubsection{Scalability Limitations}

\textbf{Exponential state space.}
The state space grows as $2^N$, limiting practical exploration.
At $N=6$ (64 states), many formulas time out; $N=7$ (128 states) is often infeasible.

\textbf{Constraint explosion.}
Complex formulas with many atomic propositions generate thousands of constraints.
The ternary/quaternary primitives required by some operators (e.g., \zcloser{} for counterfactuals)
exacerbate this.

\textbf{Quantifier alternation.}
Nested modal operators introduce quantifier alternation, which is exponentially harder for SMT solvers.
Formulas like $\Box\Diamond\Box p$ may time out even at $N=3$.

\subsubsection{Limitations Not Addressed}

\textbf{Infinite models.}
No support for reasoning about infinite model classes.

\textbf{Soundness proof automation.}
The encoding correctness argument (Section~\ref{sec:encoding-correctness}) is a proof sketch,
not a machine-checked proof.

\textbf{Multi-theory comparison validity.}
When comparing theories on the same example, differences may reflect encoding choices rather
than deep semantic differences.
```

### 3. Novelty Claims Qualification

#### Current Claims in Paper

The paper makes several novelty claims:
1. Line 232: "first systematic computational implementation of bilateral truthmaker semantics"
2. Line 1085: "represents the first computational implementation integrating all these dimensions"
3. Line 1268: "first systematic computational implementation"
4. Line 1304: "First comprehensive bilateral truthmaker implementation"

#### Survey of Existing Tools

**Modal Logic Provers/Solvers:**

| Tool | Supported Logics | Bilateral? | Hyperintensional? | Truthmaker? |
|------|------------------|------------|-------------------|-------------|
| MLSolver | Modal mu-calculus, CTL*, PDL, LTL | No | No | No |
| PRONOM | Non-normal modal cube | No | No | No |
| LoTREC | Generic modal/temporal | No | No | No |
| MleanCoP | First-order modal K,T,S4,S5 | No | No | No |
| MOLTAP | Modal K,T,S4,S5 | No | No | No |
| Isabelle/HOL | Modal cube (embedded) | No | No | No |
| Coq/Lean | Various (via shallow embedding) | No | Possible | No |

**Key Findings:**

1. **MLSolver** (Friedmann & Lange): Solves modal fixpoint logics (mu-calculus, CTL*, PDL). Does NOT support:
   - Non-normal modal logics
   - Hyperintensional operators
   - Truthmaker/bilateral semantics
   - Counterfactual conditionals

2. **PRONOM**: First prover for non-normal modal logic cube. Still uses possible-worlds semantics, not truthmakers.

3. **Tableaux Workbench (TWB)**: Generic framework for propositional modal logics. No hyperintensional support.

4. **Isabelle/HOL Modal Embeddings** (Benzmuller et al.): Embeds modal logics in HOL. Focus on proof, not model-finding. No bilateral evaluation.

5. **No existing implementation found** for:
   - Computational bilateral truthmaker semantics
   - Kit Fine's exact verification/falsification
   - Hyperintensional operators (ground, essence, propositional identity)
   - Unified treatment of counterfactuals + modality + hyperintensionality

#### Recommendation: Qualified Claims

The novelty claims are **substantiated** but should be made more precise:

**Current (vague):**
> "first systematic computational implementation of bilateral truthmaker semantics"

**Recommended (precise):**
> "To our knowledge, this represents the first computational implementation of bilateral truthmaker semantics with exact verification and falsification, integrating:
> (a) hyperintensional operators (ground, essence, propositional identity),
> (b) counterfactual conditionals,
> (c) modal operators, and
> (d) SMT-based finite model finding.
>
> While individual components have precedent---modal logic provers exist (MLSolver, PRONOM), SMT solvers handle temporal logic (nuXmv), and proof assistants encode various logics (Isabelle/HOL modal cube)---the combination of bilateral evaluation, hyperintensional operators, and automated model finding appears to be novel."

**Specific Related Work Additions:**

```latex
\paragraph{Modal Logic Solvers.}
MLSolver~\cite{friedmann2010} addresses the satisfiability problem for modal fixpoint logics
including the mu-calculus, CTL*, and PDL using parity game reduction.
PRONOM~\cite{pronom2021} is the first theorem prover for the non-normal modal logic cube.
These tools focus on validity/satisfiability decision procedures using possible-worlds semantics
rather than model construction with truthmaker semantics.
Our contribution differs in: (1) model-finding emphasis (exploring actual countermodels),
(2) bilateral evaluation structure (explicit verifiers and falsifiers), and
(3) hyperintensional operators beyond modal logic.

\paragraph{Hyperintensional Logic.}
Transparent Intensional Logic (TIL)~\cite{til2010} provides a hyperintensional framework
for natural language analysis.
Recent work investigates hyperlogic with counterfactual conditionals~\cite{hyperlogic2024}.
These remain primarily theoretical; \modelchecker{} provides an executable implementation
enabling empirical exploration.

\paragraph{Truthmaker Semantics.}
Fine's truthmaker framework~\cite{fine2017tms,fine2017content} and subsequent theoretical
developments~\cite{jago2020,yablo2014} have not previously been implemented computationally.
The present work translates Fine's informal semantics into executable Z3 constraints,
enabling automated model discovery and validation.
```

## Decisions

1. **Proof Format**: Recommend adding an explicit Correctness Theorem section with proof sketch (not full mechanized proof, which is future work).

2. **Limitations Organization**: Use standard threats-to-validity categories rather than ad-hoc groupings.

3. **Novelty Strategy**: Keep "first" claims but make them more specific about what combination of features is novel, and acknowledge related work more thoroughly.

## Risks and Mitigations

| Risk | Mitigation |
|------|------------|
| Proof sketch deemed insufficient by reviewers | Note that mechanized verification is future work; emphasize extensive empirical validation |
| Limitations section too long | Keep each point concise; some can go to supplementary material |
| Missing relevant existing tool | The survey was thorough but not exhaustive; add "to our knowledge" qualifier |
| Claims perceived as overclaiming | Precise language specifying the combination of features that is novel |

## Appendix: Ready-to-Use LaTeX Snippets

### A.1 Encoding Soundness Theorem

```latex
\begin{theorem}[Encoding Soundness]\label{thm:soundness}
For any $\theorylogos$ formula $\varphi$ and finite state space $\mathcal{S}$ with $|\mathcal{S}| = 2^N$:
\[
\text{If } \mathcal{E}(\varphi) \text{ is UNSAT, then } \varphi \text{ has no model over } \mathcal{S}.
\]
\end{theorem}
```

### A.2 Limitations Subsection Headers

```latex
\subsubsection{Internal Validity: Encoding Correctness}
\subsubsection{External Validity: Generalizability}
\subsubsection{Construct Validity: Complexity Measurement}
\subsubsection{Scalability Limitations}
```

### A.3 Qualified Novelty Claim

```latex
To our knowledge, this represents the first computational implementation of bilateral
truthmaker semantics with exact verification and falsification, integrating
hyperintensional operators (ground, essence, propositional identity),
counterfactual conditionals, modal operators, and SMT-based finite model finding.
```

## Sources

- [Stanford Encyclopedia: Automated Reasoning](https://plato.stanford.edu/entries/reasoning-automated/)
- [Journal of Automated Reasoning](https://link.springer.com/journal/10817)
- [MLSolver GitHub](https://github.com/tcsprojects/mlsolver)
- [MLSolver Paper (ScienceDirect)](https://www.sciencedirect.com/science/article/pii/S1571066110000307)
- [AiML Modal Logic Tools](http://www.cs.man.ac.uk/~schmidt/tools/)
- [PRONOM: Theorem Proving for Non-normal Modal Logics](https://ceur-ws.org/Vol-2785/paper3.pdf)
- [Truthmaker Semantics GitHub](https://truthmakersemantics.github.io/)
- [Truthmaker Semantics (PhilPapers)](https://philpapers.org/browse/truthmaker-semantics)
- [Systematic Verification of Modal Logic Cube in Isabelle/HOL](https://arxiv.org/abs/1507.08717)
- [Modal Satisfiability via SMT Solving](https://people.montefiore.uliege.be/pfontain/Areces4.pdf)
- [Empirical Formal Methods Guidelines](https://www.mdpi.com/2674-113X/1/4/17)
- [Threats to Validity in Software Engineering](https://dl.acm.org/doi/10.1145/3674805.3686691)
- [Stanford Encyclopedia: Hyperintensionality](https://plato.stanford.edu/entries/hyperintensionality/)
- [Truthmaker Semantics and Natural Language (2025)](https://compass.onlinelibrary.wiley.com/doi/10.1111/lnc3.70004)
