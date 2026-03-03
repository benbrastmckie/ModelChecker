# Research Report: Task #3 - Notation Analysis

**Task**: 3 - Port paper_overview.md to LaTeX paper.tex
**Focus**: Notation macro analysis based on logos-notation.sty
**Date**: 2026-02-18
**Session**: sess_1771445604_70c8d3

---

## Executive Summary

- logos-notation.sty provides 60+ macros covering modal, counterfactual, constitutive, and mereological notation
- Selective import recommended: use a curated subset (~25 macros) plus 15 new ModelChecker-specific macros
- stmaryrd and mathabx packages create potential conflicts with sn-jnl template (both redefine some symbols)
- Z3 function notation (e.g., `verify(s,A)`) should use monospace font, not math mode, for clarity
- Recommended approach: create modelchecker-notation.sty as a self-contained subset avoiding problematic package dependencies

---

## 1. Notation Mapping Table

Complete mapping of notation used in paper_overview.md to LaTeX commands:

### 1.1 Modal and Propositional Operators

| Source Notation | Meaning | LaTeX Command | logos-notation.sty | New Macro Needed |
|-----------------|---------|---------------|-------------------|------------------|
| `$\Box$` | Necessity | `\nec` or `\Box` | `\nec` = `\Box` | No |
| `$\Diamond$` | Possibility | `\poss` or `\Diamond` | `\poss` = `\Diamond` | No |
| `$\neg$` | Negation | `\lneg` or `\neg` | `\lneg` = `\neg` | No |
| `$\vee$` | Disjunction | `\lor` | Standard | No |
| `$\wedge$` | Conjunction | `\land` | Standard | No |
| `$\rightarrow$` | Implication | `\imp` or `\rightarrow` | `\imp` = `\to` | No |
| `$\leftrightarrow$` | Biconditional | `\leftrightarrow` | Standard | No |
| `$\top$` | Top/Verum | `\top` | Standard amsmath | No |
| `$\bot$` | Bottom/Falsum | `\bot` or `\falsum` | `\falsum` = `\bot` | No |

### 1.2 Counterfactual Operators

| Source Notation | Meaning | LaTeX Command | logos-notation.sty | New Macro Needed |
|-----------------|---------|---------------|-------------------|------------------|
| `$\Box\rightarrow$` | Would-counterfactual | `\boxright` | Defined (txfonts symbolsC) | No |
| `$\Diamond\rightarrow$` | Might-counterfactual | `\diamondright` | Defined (txfonts symbolsC) | No |
| `$\circ\rightarrow$` | Would-cause | `\circleright` | Defined (txfonts symbolsC) | No |
| `$\dot\circ\rightarrow$` | Might-cause | `\dotcircleright` | Defined (custom) | No |

### 1.3 Mereological/State Space Notation

| Source Notation | Meaning | LaTeX Command | logos-notation.sty | New Macro Needed |
|-----------------|---------|---------------|-------------------|------------------|
| `$\mathcal{S}$` | State space | `\statespace` | `\statespace` = `\mathcal{S}` | No |
| `$\square$` | Null state | `\nullstate` | `\nullstate` = `\square` | No |
| `$\sqbullet$` | Full state | `\fullstate` | `\fullstate` = `\sqbullet` | No |
| `$a \sqcup b$` | Fusion | `\fusion{a}{b}` | `\fusion{a}{b}` = `a\sqcup b` | No |
| `$\bigsqcup$` | Big fusion | `\Fusion` | `\Fusion` = `\bigsqcup` | No |
| `$\sqsubseteq$` | Parthood | `\parthood` | `\parthood` = `\sqsubseteq` | No |
| `$\sqsubset$` | Strict part | `\strictpart` | `\strictpart` = `\sqsubset` | No |

### 1.4 Verification/Falsification Notation

| Source Notation | Meaning | LaTeX Command | logos-notation.sty | New Macro Needed |
|-----------------|---------|---------------|-------------------|------------------|
| `$\Vdash$` | Verifies | `\verifies` | `\verifies` = `\Vdash` | No |
| `$\dashV$` | Falsifies | `\falsifies` | `\falsifies` = `\dashV` | No |
| `$\|A\|^+$` | Verifier set | `\verifierset{A}` | Defined | No |
| `$\|A\|^-$` | Falsifier set | `\falsifierset{A}` | Defined | No |
| `$\vDash$` | True at | `\trueat` | `\trueat` = `\vDash` | No |
| `$\Dashv$` | False at | `\falseat` | `\falseat` = `\Dashv` | No |

### 1.5 Constitutive/Grounding Notation

| Source Notation | Meaning | LaTeX Command | logos-notation.sty | New Macro Needed |
|-----------------|---------|---------------|-------------------|------------------|
| `$\leq$` | Ground relation | `\ground` | `\ground` = `\leq` | No |
| `$\sqsubseteq$` | Essence | `\essence` | `\essence` = `\sqsubseteq` | No |
| `$\equiv$` | Propositional identity | `\propident` | Not defined | **Yes** |
| R | Relevance implication | `\relimpl` | Not defined | **Yes** |

### 1.6 Model/Frame Notation

| Source Notation | Meaning | LaTeX Command | logos-notation.sty | New Macro Needed |
|-----------------|---------|---------------|-------------------|------------------|
| `$\mathcal{M}$` | Model | `\model` | `\model` = `\mathcal{M}` | No |
| `$\mathcal{F}$` | Frame | `\mframe` | `\mframe` = `\mathcal{F}` | No |
| `$\langle ... \rangle$` | Tuple | `\tuple{...}` | Defined | No |
| `$\|A\|$` | Interpretation | `\interp{A}` | `\interp{A}` = `|A|` | No |

### 1.7 Temporal Operators

| Source Notation | Meaning | LaTeX Command | logos-notation.sty | New Macro Needed |
|-----------------|---------|---------------|-------------------|------------------|
| H | Always past | `\allpast` | Defined | No |
| G | Always future | `\allfuture` | Defined | No |
| P | Sometimes past | `\somepast` | Defined | No |
| F | Sometimes future | `\somefuture` | Defined | No |
| `$\triangleleft$` | Since | `\since` | Defined | No |
| `$\triangleright$` | Until | `\until` | Defined | No |

### 1.8 Bilateral Proposition Notation

| Source Notation | Meaning | LaTeX Command | logos-notation.sty | New Macro Needed |
|-----------------|---------|---------------|-------------------|------------------|
| `$\mathbb{P}$` | Proposition space | `\props` | Defined | No |
| `$\mathsf{A}$` | Bilateral proposition | `\prop{A}` | Defined | No |
| verum symbol | Bilateral top | `\ver` | Defined (complex) | No |
| falsum symbol | Bilateral bottom | `\fal` | Defined (complex) | No |

---

## 2. Additional Macros Needed for ModelChecker Paper

### 2.1 Z3 Function Names (Code/Technical)

These appear in code listings and inline references. Use monospace font (not math mode):

| Notation | Purpose | Recommended LaTeX |
|----------|---------|-------------------|
| `verify(s,A)` | Z3 verify function | `\texttt{verify}(s,A)` or lstinline |
| `falsify(s,A)` | Z3 falsify function | `\texttt{falsify}(s,A)` |
| `accessible(w,w')` | Accessibility relation | `\texttt{accessible}(w,w')` |
| `possible(s)` | Possible state predicate | `\texttt{possible}(s)` |
| `fusion(s1,s2,s3)` | Fusion function | `\texttt{fusion}(s_1,s_2,s_3)` |
| `is_world(w)` | World predicate | `\texttt{is\_world}(w)` |
| `closer(w1,w2,w3,A)` | Closer-than relation | `\texttt{closer}(w_1,w_2,w_3,A)` |
| `excludes(s1,s2,A)` | Exclusion relation | `\texttt{excludes}(s_1,s_2,A)` |
| `witness(s,A)` | Witness relation | `\texttt{witness}(s,A)` |
| `imposes(w,A,w')` | Imposition relation | `\texttt{imposes}(w,A,w')` |
| `true_at()` | Truth at world | `\texttt{true\_at}()` |
| `extended_verify()` | Extended verify | `\texttt{extended\_verify}()` |
| `extended_falsify()` | Extended falsify | `\texttt{extended\_falsify}()` |

**Recommendation**: Create convenience macros for frequently used Z3 function names:

```latex
% Z3 function name macros
\newcommand{\zverify}{\texttt{verify}}
\newcommand{\zfalsify}{\texttt{falsify}}
\newcommand{\zaccessible}{\texttt{accessible}}
\newcommand{\zpossible}{\texttt{possible}}
\newcommand{\zfusion}{\texttt{fusion}}
\newcommand{\zisworld}{\texttt{is\_world}}
\newcommand{\zcloser}{\texttt{closer}}
\newcommand{\zexcludes}{\texttt{excludes}}
\newcommand{\zwitness}{\texttt{witness}}
\newcommand{\zimposes}{\texttt{imposes}}
\newcommand{\ztrueat}{\texttt{true\_at}}
\newcommand{\zextverify}{\texttt{extended\_verify}}
\newcommand{\zextfalsify}{\texttt{extended\_falsify}}
```

### 2.2 Theory Names

| Name | Recommended LaTeX |
|------|-------------------|
| Logos | `\textsc{Logos}` or `\textsf{Logos}` |
| Exclusion | `\textsc{Exclusion}` or `\textsf{Exclusion}` |
| Imposition | `\textsc{Imposition}` or `\textsf{Imposition}` |
| Bimodal | `\textsc{Bimodal}` or `\textsf{Bimodal}` |
| TheoryLib | `\textsc{TheoryLib}` |
| ModelChecker | `\textsc{ModelChecker}` |

**Recommendation**: Create theory name macros:

```latex
% Theory name macros
\newcommand{\theorylogos}{\textsc{Logos}}
\newcommand{\theoryexclusion}{\textsc{Exclusion}}
\newcommand{\theoryimposition}{\textsc{Imposition}}
\newcommand{\theorybimodal}{\textsc{Bimodal}}
\newcommand{\theorylib}{\textsc{TheoryLib}}
\newcommand{\modelchecker}{\textsc{ModelChecker}}
```

### 2.3 Mathematical Notation Not in logos-notation.sty

| Notation | Purpose | Recommended LaTeX | New Macro |
|----------|---------|-------------------|-----------|
| `$\equiv$` | Propositional identity | `\propident` | `\newcommand{\propident}{\equiv}` |
| R | Relevance implication | `\relimpl` | `\newcommand{\relimpl}{\mathsf{R}}` |
| N | State space size | `\stateN` | `\newcommand{\stateN}{\mathsf{N}}` |
| K | Atomic proposition count | `\atomK` | `\newcommand{\atomK}{\mathsf{K}}` |

### 2.4 Complexity Classes

| Notation | Recommended LaTeX |
|----------|-------------------|
| NP-complete | `\textsf{NP-complete}` |
| NEXPTIME | `\textsf{NEXPTIME}` |
| EXPSPACE | `\textsf{EXPSPACE}` |

---

## 3. Reusable Commands from logos-notation.sty

### 3.1 Safe to Import (No Package Conflicts)

These macros depend only on amsmath/amssymb which sn-jnl already loads:

```latex
% Modal operators
\newcommand{\nec}{\Box}
\newcommand{\poss}{\Diamond}

% Propositional
\newcommand{\imp}{\to}
\newcommand{\lneg}{\neg}
\newcommand{\falsum}{\bot}

% Model notation
\newcommand{\model}{\mathcal{M}}
\newcommand{\mframe}{\mathcal{F}}
\newcommand{\tuple}[1]{\langle #1 \rangle}
\newcommand{\define}{\coloneqq}

% Meta-variables
\newcommand{\metaphi}{\varphi}
\newcommand{\metapsi}{\psi}
\newcommand{\metachi}{\chi}

% Proof
\newcommand{\proves}{\vdash}
\newcommand{\context}{\Gamma}
```

### 3.2 Requires mathtools Package

```latex
\RequirePackage{mathtools}  % For \coloneqq
\newcommand{\define}{\coloneqq}
\newcommand{\Define}{\Coloneq}  % BNF-style ::=
```

Note: mathtools is generally compatible with sn-jnl.

### 3.3 Requires stmaryrd Package (Caution)

```latex
\RequirePackage{stmaryrd}  % For \llbracket, \rrbracket
\newcommand{\sem}[1]{\llbracket #1 \rrbracket}
\newcommand{\ext}[1]{\llbracket #1 \rrbracket}
```

**Caution**: stmaryrd may conflict with sn-jnl. Test before using.

### 3.4 Requires mathabx Package (High Conflict Risk)

```latex
\RequirePackage{mathabx}  % For \square, \sqbullet
\newcommand{\nullstate}{\square}
\newcommand{\fullstate}{\sqbullet}
```

**WARNING**: mathabx redefines many standard symbols including some from amssymb.
This is known to cause issues with Springer templates.

**Alternative**: Use Unicode symbols or define custom commands:
```latex
\newcommand{\nullstate}{\text{\tiny$\square$}}
\newcommand{\fullstate}{\blacksquare}  % From amssymb
```

### 3.5 Requires txfonts symbolsC (Counterfactuals)

```latex
\DeclareSymbolFont{symbolsC}{U}{txsyc}{m}{n}
\DeclareMathSymbol{\boxright}{\mathrel}{symbolsC}{"80}
\DeclareMathSymbol{\circleright}{\mathrel}{symbolsC}{"91}
\DeclareMathSymbol{\diamondright}{\mathrel}{symbolsC}{"84}
```

**Compatibility**: txfonts is generally compatible but may affect font rendering.
Test with sn-jnl template.

---

## 4. Compatibility Analysis: sn-jnl Template

### 4.1 Packages Already Loaded by sn-jnl or paper.tex

From paper.tex preamble:
- `amsmath`, `amssymb`, `amsfonts` - Core math packages
- `amsthm` - Theorem environments
- `mathrsfs` - Script fonts (`\mathscr`)
- `booktabs` - Professional tables
- `algorithm`, `algorithmicx`, `algpseudocode` - Algorithms
- `listings` - Code listings

### 4.2 Safe to Add

These packages are compatible with sn-jnl:
- `mathtools` - Enhanced math (extends amsmath)
- `xspace` - Smart spacing after macros
- `hyperref` - Already handled by sn-jnl internally

### 4.3 Potentially Problematic

| Package | Issue | Recommendation |
|---------|-------|----------------|
| `mathabx` | Redefines amssymb symbols | **Avoid** - use alternatives |
| `stmaryrd` | May conflict with symbols | Test carefully |
| `txfonts` | Font conflicts possible | Use symbolsC declaration only |
| `enumitem` | sn-jnl may have own list styling | Test or omit |

### 4.4 Recommended Safe Approach

Rather than importing logos-notation.sty wholesale:

1. **Create modelchecker-notation.sty** with curated subset
2. **Avoid mathabx** entirely - use alternatives
3. **Test stmaryrd** in isolation first
4. **Keep txfonts symbolsC** for counterfactual arrows (well-tested)
5. **Add new macros** for ModelChecker-specific notation

---

## 5. Recommended Preamble Section

Add this to paper.tex after the existing package imports:

```latex
%%=======================================================%%
%% Additional packages for ModelChecker paper            %%
%%=======================================================%%
\usepackage{mathtools}  % For \coloneqq and enhanced math

% Counterfactual operators (from txfonts symbolsC)
\DeclareSymbolFont{symbolsC}{U}{txsyc}{m}{n}
\SetSymbolFont{symbolsC}{bold}{U}{txsyc}{bx}{n}
\DeclareFontSubstitution{U}{txsyc}{m}{n}
\AtBeginDocument{
  \DeclareMathSymbol{\boxright}{\mathrel}{symbolsC}{"80}       % Would-counterfactual
  \DeclareMathSymbol{\circleright}{\mathrel}{symbolsC}{"91}    % Would-cause
  \DeclareMathSymbol{\diamondright}{\mathrel}{symbolsC}{"84}   % Might-counterfactual
}

%%=======================================================%%
%% Notation macros for ModelChecker paper                %%
%%=======================================================%%

% Modal operators
\newcommand{\nec}{\Box}                     % Necessity
\newcommand{\poss}{\Diamond}                % Possibility

% Propositional connectives
\newcommand{\imp}{\to}                      % Implication
\newcommand{\lneg}{\neg}                    % Negation
\newcommand{\falsum}{\bot}                  % Bottom

% State space notation
\newcommand{\statespace}{\mathcal{S}}       % State space
\newcommand{\nullstate}{\square}            % Null state (use \square from amsmath)
\newcommand{\fullstate}{\blacksquare}       % Full state (amssymb)
\newcommand{\fusion}[2]{#1 \sqcup #2}       % Fusion
\newcommand{\Fusion}{\bigsqcup}             % Big fusion
\newcommand{\parthood}{\sqsubseteq}         % Part-of relation
\newcommand{\strictpart}{\sqsubset}         % Strict part

% Verification/falsification
\newcommand{\verifies}{\Vdash}              % Verifies relation
\newcommand{\falsifies}{\dashv}             % Falsifies relation (note: \dashV may not exist)
\newcommand{\verifierset}[1]{|{#1}|^+}      % Verifier set
\newcommand{\falsifierset}[1]{|{#1}|^-}     % Falsifier set
\newcommand{\trueat}{\vDash}                % True at
\newcommand{\falseat}{\Dashv}               % False at

% Constitutive/grounding
\newcommand{\ground}{\leq}                  % Ground relation
\newcommand{\essence}{\sqsubseteq}          % Essence relation
\newcommand{\propident}{\equiv}             % Propositional identity
\newcommand{\relimpl}{\mathsf{R}}           % Relevance implication

% Model notation
\newcommand{\model}{\mathcal{M}}            % Model
\newcommand{\mframe}{\mathcal{F}}           % Frame
\newcommand{\tuple}[1]{\langle #1 \rangle}  % Tuple
\newcommand{\interp}[1]{|#1|}               % Interpretation
\newcommand{\define}{\coloneqq}             % Definition symbol

% Bilateral propositions
\newcommand{\prop}[1]{\mathsf{#1}}          % Proposition
\newcommand{\props}{\mathbb{P}}             % Proposition space

% Meta-variables
\newcommand{\metaphi}{\varphi}              % Formula meta-variable
\newcommand{\metapsi}{\psi}                 % Formula meta-variable
\newcommand{\metachi}{\chi}                 % Formula meta-variable

% Temporal operators
\newcommand{\allpast}{\mathbf{H}}           % Always past
\newcommand{\allfuture}{\mathbf{G}}         % Always future
\newcommand{\somepast}{\mathbf{P}}          % Sometimes past
\newcommand{\somefuture}{\mathbf{F}}        % Sometimes future
\newcommand{\since}{\triangleleft}          % Since
\newcommand{\until}{\triangleright}         % Until

% Settings/parameters
\newcommand{\stateN}{\mathsf{N}}            % State space size parameter
\newcommand{\atomK}{\mathsf{K}}             % Atomic proposition count

% Theory names (small caps)
\newcommand{\theorylogos}{\textsc{Logos}}
\newcommand{\theoryexclusion}{\textsc{Exclusion}}
\newcommand{\theoryimposition}{\textsc{Imposition}}
\newcommand{\theorybimodal}{\textsc{Bimodal}}
\newcommand{\theorylib}{\textsc{TheoryLib}}
\newcommand{\modelchecker}{\textsc{ModelChecker}}

% Z3 function name macros (for inline code references)
\newcommand{\zverify}{\texttt{verify}}
\newcommand{\zfalsify}{\texttt{falsify}}
\newcommand{\zaccessible}{\texttt{accessible}}
\newcommand{\zpossible}{\texttt{possible}}
\newcommand{\zfusion}{\texttt{fusion}}
\newcommand{\zisworld}{\texttt{is\_world}}
\newcommand{\zcloser}{\texttt{closer}}
\newcommand{\zexcludes}{\texttt{excludes}}
\newcommand{\zwitness}{\texttt{witness}}
\newcommand{\zimposes}{\texttt{imposes}}
\newcommand{\ztrueat}{\texttt{true\_at}}
\newcommand{\zextverify}{\texttt{extended\_verify}}
\newcommand{\zextfalsify}{\texttt{extended\_falsify}}

%%=======================================================%%
%% Listings configuration for Python code               %%
%%=======================================================%%

\lstset{
  language=Python,
  basicstyle=\ttfamily\small,
  keywordstyle=\bfseries\color{blue!70!black},
  commentstyle=\itshape\color{green!50!black},
  stringstyle=\color{red!60!black},
  showstringspaces=false,
  breaklines=true,
  breakatwhitespace=true,
  numbers=left,
  numberstyle=\tiny\color{gray},
  numbersep=5pt,
  frame=single,
  framerule=0.5pt,
  rulecolor=\color{gray!50},
  captionpos=b
}
```

---

## 6. Key Questions Answered

### Q1: Should we import logos-notation.sty wholesale or selectively?

**Answer: Selectively.**

Reasons:
1. logos-notation.sty requires `mathabx` which conflicts with sn-jnl template
2. logos-notation.sty includes enumitem list customization that may conflict
3. Many macros in logos-notation.sty are not needed for this paper
4. Custom subset allows avoiding problematic dependencies

### Q2: What additional notation macros are needed for ModelChecker-specific concepts?

**Answer: ~15 new macros needed:**

1. `\propident` - Propositional identity (`\equiv`)
2. `\relimpl` - Relevance implication (R)
3. `\stateN` - State space size parameter
4. `\atomK` - Atomic proposition count
5. `\theorylogos`, `\theoryexclusion`, `\theoryimposition`, `\theorybimodal`, `\theorylib`, `\modelchecker` - Theory names
6. `\zverify`, `\zfalsify`, `\zaccessible`, `\zpossible`, `\zfusion`, `\zisworld` - Z3 function names
7. `\zcloser`, `\zexcludes`, `\zwitness`, `\zimposes` - Additional Z3 functions

### Q3: Are there any package conflicts with sn-jnl template?

**Answer: Yes, two significant ones:**

1. **mathabx** - Redefines many amssymb symbols. **Avoid entirely.**
2. **stmaryrd** - May work but needs testing. Only needed for `\llbracket`/`\rrbracket` which are not essential.

Safe packages to add:
- mathtools (extends amsmath)
- txfonts symbolsC (just the font, not full package)

### Q4: How to handle inline code vs math for function names like `verify(s,A)`?

**Answer: Use a hybrid approach:**

1. **In prose/discussion**: Use `\zverify(s,A)` which renders as `verify(s,A)` in monospace
2. **In mathematical formulas**: Use `\texttt{verify}(s,A)` or create semantic macros
3. **In code listings**: Use `lstlisting` environment with Python syntax
4. **In algorithmic pseudocode**: Use `\textsc{Verify}` for procedure names

Example usage:
```latex
% In prose
The \zverify{} function returns true when state $s$ verifies sentence $A$.

% In math display
\[
\forall s \forall A [\zverify(s,A) \rightarrow \zpossible(s)]
\]

% In code listing
\begin{lstlisting}
def verify(state, sentence, eval_point):
    return self.semantics.verify(state, sentence)
\end{lstlisting}
```

---

## 7. Risks and Mitigations

| Risk | Likelihood | Impact | Mitigation |
|------|------------|--------|------------|
| mathabx conflicts | High | High | Use alternative symbols from amssymb |
| stmaryrd conflicts | Medium | Low | Test; fallback to `[\![` `]\!]` if needed |
| txfonts rendering | Low | Medium | Test with sn-jnl; fallback available |
| Symbol undefined | Medium | Low | Test each macro before full document |
| Overfull hboxes from macros | Low | Low | Use `\allowbreak` in long expressions |

---

## 8. Implementation Checklist

- [ ] Add mathtools package import
- [ ] Add txfonts symbolsC font declaration
- [ ] Add curated notation macros (from Section 5)
- [ ] Configure lstlisting for Python
- [ ] Test compilation with sn-jnl template
- [ ] Verify no symbol conflicts
- [ ] Test all counterfactual operators render correctly
- [ ] Verify theory name macros in text

---

## 9. References

- logos-notation.sty source: `/home/benjamin/Projects/Logos/Theory/latex/assets/logos-notation.sty`
- research-001.md: `/home/benjamin/Projects/ModelChecker/specs/003_port_paper_overview_to_latex/reports/research-001.md`
- paper.tex template: `/home/benjamin/Projects/ModelChecker/latex/paper.tex`
- paper_overview.md source: `/home/benjamin/Projects/ModelChecker/latex/markdown/paper_overview.md`

---

## Next Steps

1. Add recommended preamble section to paper.tex
2. Test compilation with sample content
3. Proceed with Section 1-3 implementation (Phase 2 of research-001.md)
