# Research Report: Task #3

**Task**: 3 - Port paper_overview.md to LaTeX paper.tex
**Started**: 2026-02-18
**Completed**: 2026-02-18
**Effort**: Medium-High (substantial content transformation)
**Dependencies**: None
**Sources/Inputs**:
- `/home/benjamin/Projects/ModelChecker/latex/markdown/paper_overview.md` (source content)
- `/home/benjamin/Projects/ModelChecker/latex/paper.tex` (target template)
- `/home/benjamin/Projects/ModelChecker/latex/README.md` (JAR submission guidelines)
- `/home/benjamin/Projects/ModelChecker/.claude/context/project/latex/standards/latex-style-guide.md`
- [Journal of Automated Reasoning Submission Guidelines](https://link.springer.com/journal/10817/submission-guidelines)
**Artifacts**:
- `specs/003_port_paper_overview_to_latex/reports/research-001.md` (this report)
**Standards**: report-format.md

---

## Executive Summary

- Source document contains ~2400 lines of comprehensive research content covering ModelChecker framework across 10 sections
- Target uses Springer Nature sn-jnl template v3.1 with sn-mathphys-num bibliography style
- Key challenges: converting ~50+ code blocks, ~15+ tables, and extensive mathematical notation
- Bibliography requires converting ~20 references from markdown to BibTeX format
- Recommend phased implementation: sections 1-3, then 4-6, then 7-10 with bibliography

---

## Context & Scope

### Source Document Analysis

The `paper_overview.md` file is a comprehensive research paper outline with:

| Section | Subsections | Content Types | Estimated Lines |
|---------|-------------|---------------|-----------------|
| Abstract | - | Text, keywords | ~20 |
| 1. Introduction | 3 | Text, bullets | ~60 |
| 2. Programmatic Methodology | 9 | Code blocks, tables, math | ~580 |
| 3. Modularity | 4 | Code blocks, tables | ~220 |
| 4. Finite Model Exploration | 6 | Tables, code, math | ~300 |
| 5. TheoryLib Vision | 5 | Code, bullets, tables | ~380 |
| 6. Case Study: Logos | 6 | Code blocks, tables | ~400 |
| 7. Implementation Results | 5 | Tables, code examples | ~240 |
| 8. Related Work | 5 | Tables, comparisons | ~140 |
| 9. Discussion | 5 | Text, bullets | ~180 |
| 10. References | - | Citations | ~70 |

**Content Complexity**:
- ~50+ Python code blocks
- ~15+ comparison/data tables
- Extensive inline math notation
- Multiple ASCII diagrams

### Target Template

The `paper.tex` uses:
- `sn-jnl.cls` v3.1 (December 2024)
- `sn-mathphys-num` bibliography style (numbered citations)
- Single-file format (no `\input` commands per Springer requirement)

**Pre-configured features**:
- Theorem environments (thmstyleone, thmstyletwo, thmstylethree)
- Packages: booktabs, algorithm, algorithmicx, algpseudocode, listings
- Declarations section template

---

## Findings

### 1. LaTeX Semantic Linefeeds

Per project style guide, source must use one sentence per line:

```latex
% GOOD: Semantic linefeeds
Modal logic extends propositional logic with modal operators.
The necessity operator $\Box$ expresses metaphysical necessity.

% BAD: Multiple sentences per line
Modal logic extends propositional logic with modal operators. The necessity operator $\Box$ expresses metaphysical necessity.
```

**Rationale**: Clean git diffs, easier review, no output impact.

**Long sentence breaks**: At natural clause boundaries (commas, conjunctions).

### 2. Mathematical Notation Conversion

Source markdown math converts to LaTeX math:

| Markdown | LaTeX | Notes |
|----------|-------|-------|
| `$\Box$` | `$\Box$` | Direct (already LaTeX) |
| `$\Diamond$` | `$\Diamond$` | Direct |
| `→` | `$\rightarrow$` | In math mode |
| `⊑` | `$\sqsubseteq$` | Part-of relation |
| `⊔` | `$\sqcup$` | Fusion operation |
| `≡` | `$\equiv$` | Identity |
| `≤` | `$\leq$` | Ground relation |
| `∀` | `$\forall$` | Universal quantifier |
| `∃` | `$\exists$` | Existential quantifier |
| `¬` | `$\neg$` | Negation |
| `∧` | `$\land$` | Conjunction |
| `∨` | `$\lor$` | Disjunction |
| `↔` | `$\leftrightarrow$` | Biconditional |

**Mathematical content in code blocks**: Some code blocks contain mathematical notation (e.g., Z3 constraints). These should remain in `lstlisting` environments with appropriate escaping.

### 3. Code Listing Strategy

**Python code examples**: Use `lstlisting` environment with Python configuration:

```latex
\lstset{
  language=Python,
  basicstyle=\ttfamily\small,
  keywordstyle=\bfseries,
  showstringspaces=false,
  breaklines=true
}

\begin{lstlisting}[caption={Negation operator implementation}]
class Negation(OperatorDefaults):
    def extended_verify(self, state, sentence, eval_point):
        A = sentence.sentences[0]
        return self.semantics.extended_falsify(state, A, eval_point)
\end{lstlisting}
```

**Pseudocode/algorithms**: Use `algorithm` and `algpseudocode`:

```latex
\begin{algorithm}
\caption{Model Iteration}
\begin{algorithmic}[1]
\State Find first model $M_1$
\State Add blocking constraint: model $\neq M_1$
\State Solve again $\rightarrow M_2$
\While{$k$ models not found and SAT}
  \State Add blocking constraint
  \State Solve again
\EndWhile
\end{algorithmic}
\end{algorithm}
```

**Strategy recommendation**:
- Short inline examples: `lstlisting`
- Complex algorithms: `algorithm` environment
- Interface definitions: `lstlisting` with custom caption

### 4. Theorem Environments

sn-jnl provides three predefined styles:

| Style | Environments | Format | Use For |
|-------|-------------|--------|---------|
| thmstyleone | theorem, proposition, lemma, corollary | Bold head, italic text | Formal results |
| thmstyletwo | example, remark | Roman head, italic text | Examples, observations |
| thmstylethree | definition | Bold head, roman text | Definitions |

**Examples from source requiring environments**:
- Definition of "frame", "model", "verifiers/falsifiers"
- Theorem-like claims about arity complexity
- Examples of countermodels and valid/invalid inferences

### 5. Tables in Springer Format

Source has ~15+ tables requiring booktabs conversion:

```latex
% Source markdown table:
% | Setting | Effect | Typical Use |
% |---------|--------|-------------|
% | N | State space size | 3-6 |

% LaTeX booktabs:
\begin{table}[ht]
\caption{Key Semantic Settings}\label{tab:settings}
\begin{tabular}{@{}lll@{}}
\toprule
Setting & Effect & Typical Use \\
\midrule
\texttt{N} & State space size ($2^N$ states) & 3--6 \\
\texttt{contingent} & Require both verifiers and falsifiers & Force non-trivial propositions \\
\bottomrule
\end{tabular}
\end{table}
```

**Key considerations**:
- Use `@{}` to remove outer padding
- Replace markdown `|` with proper column alignment
- Use `\toprule`, `\midrule`, `\bottomrule`
- Add `\caption` and `\label` for cross-references

### 6. Figure Requirements

Source contains ASCII diagrams (e.g., architecture diagrams, state space representations).

**Options**:
1. **TikZ diagrams**: Convert ASCII to proper TikZ figures
2. **Code listings**: Keep as code/pseudo-diagrams in lstlisting
3. **External figures**: Create PDF/PNG figures

**Recommendation**: Given single-file requirement and content nature, keep most as code listings. Convert only critical architecture diagrams to TikZ if time permits.

### 7. Bibliography Setup

Source references require BibTeX entries. Current `references.bib` contains only template examples.

**References to add** (from source section 10):
1. Fine, K. (2017). *Truthmaker Semantics*. Companion to Philosophy of Language.
2. Fine, K. (2017). *A Theory of Truthmaker Content*. JPL 46(6).
3. Yablo, S. (2014). *Aboutness*. Princeton UP.
4. Lewis, D. (1973). *Counterfactuals*. Harvard UP.
5. Stalnaker, R. (1968). A Theory of Conditionals.
6. Chellas, B. (1980). *Modal Logic: An Introduction*. Cambridge UP.
7. De Moura, L. & Bjorner, N. (2008). Z3: An Efficient SMT Solver.
8. Barrett et al. (2009). Satisfiability Modulo Theories. Handbook of Satisfiability.
9. Fitting, M. (1983). *Proof Methods for Modal and Intuitionistic Logics*.
10. Benzmüller & Woltzenlogel Paleo (2014). Automating Gödel's Ontological Proof.
11. Oppenheimer & Zalta (2011). A Computationally-Discovered Simplification.
12. Clarke, Grumberg & Peled (1999). *Model Checking*. MIT Press.
13. Bertot & Castéran (2004). *Coq'Art*. Springer.
14. Nipkow, Paulson & Wenzel (2002). *Isabelle/HOL*. Springer.
15. Martin, R. (2003). *Agile Software Development*. Prentice Hall.
16. Gamma et al. (1994). *Design Patterns*. Addison-Wesley.

**Citation style**: Numbered, e.g., `\cite{fine2017truthmaker}` renders as [1].

### 8. Section Structure Mapping

Source sections map to LaTeX as follows:

| Source Section | LaTeX Section | Notes |
|----------------|---------------|-------|
| 1. Introduction | `\section{Introduction}` | Keep structure |
| 2. Programmatic Methodology | `\section{Programmatic Methodology}` | Heavy code/math |
| 3. Modularity | `\section{Modularity and Extensibility}` | Code examples |
| 4. Finite Model Exploration | `\section{Finite Model Exploration}` | Math/tables |
| 5. TheoryLib Vision | `\section{TheoryLib: Executable Semantic Theories}` | Future work |
| 6. Case Study | `\section{Case Study: Logos Theory}` | Implementation |
| 7. Implementation Results | `\section{Evaluation}` | Benchmarks/tables |
| 8. Related Work | `\section{Related Work}` | Comparisons |
| 9. Discussion | `\section{Discussion and Future Work}` | Merge 9.5 conclusion |

**Subsection limit**: sn-jnl supports `\subsection` and `\subsubsection`. Source uses deep nesting (####) which should flatten to `\subsubsection` maximum.

### 9. Length Considerations

**Source size**: ~2400 lines, ~70KB
**Typical JAR paper**: 20-40 pages (no strict limit for regular papers)
**Estimated output**: 35-50 pages with figures/tables

JAR accepts comprehensive technical papers. The source content appears appropriate for a full-length journal article without significant condensing.

**Priority if condensing needed**:
1. Keep: Sections 1, 2, 4, 6, 7, 9 (core contribution)
2. Condense: Section 3 (modularity details), Section 5 (vision)
3. Trim: Section 8 (related work can be selective)

### 10. JAR-Specific Requirements

Per latex/README.md and Springer guidelines:

**Required Declarations section**:
- Funding (or "Not applicable")
- Conflict of interest
- Ethics approval (Not applicable)
- Consent to participate (Not applicable)
- Consent for publication (Not applicable)
- Data availability
- **Code availability** (REQUIRED - must include repository URL, license, version)
- Author contribution

**Code availability statement example**:
> The ModelChecker software (version X.Y.Z) is available at https://github.com/benbrastmckie/ModelChecker under the MIT License. Archived version: https://doi.org/10.5281/zenodo.XXXXXXX

---

## Recommendations

### Content Adaptation Strategy

1. **Direct transcription** for prose sections (Introduction, Discussion)
2. **Structured conversion** for code-heavy sections (Methodology, Case Study)
3. **Table-first approach** for data sections (Results, Comparison)

### Implementation Phases

**Phase 1: Document Structure and Preamble**
- Update title, authors, affiliations
- Configure abstract and keywords
- Set up custom commands for notation

**Phase 2: Sections 1-3 (Foundation)**
- Introduction (relatively straightforward)
- Programmatic Methodology (heavy code/tables)
- Modularity (code examples)

**Phase 3: Sections 4-6 (Core Technical)**
- Finite Model Exploration (math-heavy)
- TheoryLib Vision (future work)
- Case Study: Logos (implementation details)

**Phase 4: Sections 7-10 and Back Matter**
- Implementation Results (tables, benchmarks)
- Related Work (comparison tables)
- Discussion and Conclusion
- References (complete BibTeX entries)

**Phase 5: Verification and Polish**
- Compile full document
- Fix cross-references
- Verify all citations resolve
- Check for overfull boxes
- Final read-through

### Risk Assessment

| Risk | Likelihood | Impact | Mitigation |
|------|------------|--------|------------|
| Missing packages | Low | Medium | Template includes common packages |
| Complex tables | Medium | Medium | Simplify if needed, test incrementally |
| Code listing formatting | Medium | Low | Use consistent lstset configuration |
| Bibliography errors | Medium | Medium | Test citations early, add incrementally |
| Overfull hboxes | Medium | Low | Break long lines, adjust verbatim |
| Cross-reference issues | Low | Low | Run latexmk multiple passes |

---

## Decisions

1. **Use lstlisting for all code**: Consistent approach, well-supported by template
2. **Keep section structure**: Source sections map well to typical JAR paper structure
3. **Create custom notation macros**: For frequently-used symbols (Box, Diamond, etc.)
4. **Prioritize content completeness**: JAR accepts comprehensive papers, no need to artificially condense
5. **Phase-based implementation**: Enables incremental verification and checkpointing

---

## Appendix: Notation Macro Recommendations

Add to preamble:

```latex
%%=======================================================%%
%% Custom notation macros for ModelChecker paper         %%
%%=======================================================%%
\newcommand{\nec}{\Box}           % Necessity
\newcommand{\pos}{\Diamond}       % Possibility
\newcommand{\verify}{\vdash_v}    % Verifies
\newcommand{\falsify}{\vdash_f}   % Falsifies
\newcommand{\partof}{\sqsubseteq} % Part-of relation
\newcommand{\fuse}{\sqcup}        % Fusion
\newcommand{\ground}{\leq}        % Ground relation
\newcommand{\ident}{\equiv}       % Propositional identity
\newcommand{\cfthen}{\boxright}   % Counterfactual conditional
```

---

## Search Queries Used

1. Codebase: `Glob` for `**/*.bib`, `**/*latex*.md`
2. Codebase: `Read` paper_overview.md, paper.tex, README.md, style guides
3. Web: "Journal of Automated Reasoning Springer submission guidelines paper length"
4. Web: Attempted WebFetch on JAR submission guidelines (returned 303 redirect)

## References to Documentation

- Springer Nature sn-jnl template user manual: `latex/assets/user-manual.pdf`
- Project LaTeX style guide: `.claude/context/project/latex/standards/latex-style-guide.md`
- LaTeX implementation agent: `.claude/agents/latex-implementation-agent.md`
