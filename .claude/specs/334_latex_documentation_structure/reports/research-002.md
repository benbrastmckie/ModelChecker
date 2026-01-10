# Research Report: LaTeX Documentation for Constitutive and Causal Layers

**Task**: 334 - Create LaTeX documentation structure for Logos system mirroring layer structure

**Started**: 2026-01-08T21:00:00Z

**Completed**: 2026-01-08T22:30:00Z

**Effort**: 1-2 days implementation (supplemental to research-001.md)

**Priority**: Medium

**Dependencies**: research-001.md (base research report)

**Sources/Inputs**:
- Documentation/Research/LAYER_EXTENSIONS.md (Overview section, lines 1-558)
- Documentation/UserGuide/ARCHITECTURE.md (Layer architecture specification)
- .opencode/specs/334_latex_documentation_structure/reports/research-001.md (base research)
- Logos/Core/Syntax/Formula.lean (Layer 0 implementation reference)

**Artifacts**:
- This supplemental research report: .opencode/specs/334_latex_documentation_structure/reports/research-002.md

**Standards**: status-markers.md, artifact-management.md, tasks.md, report.md

---

## Executive Summary

This supplemental research report builds upon research-001.md by analyzing the LAYER_EXTENSIONS.md Overview section to provide detailed guidance for documenting the Constitutive Layer (Core Layer constitutive operators) and Causal Layer (Modal Layer causal operators) in the LaTeX reference documentation. The analysis reveals that LAYER_EXTENSIONS.md provides a comprehensive semantic progression framework that should inform the LaTeX documentation structure, particularly for future layer extensions.

**Key Findings**:
1. LAYER_EXTENSIONS.md distinguishes between Core Layer (constitutive operators: ≤, ⊑, ≡) and Causal Layer (causal operator: ○→) as separate semantic frames
2. The Overview section provides clear operator definitions, semantic characterizations, and examples for both layers
3. The Constitutive Layer operators (grounding, essence, propositional identity) are timeless explanatory relations
4. The Causal Layer operator (causation) is temporal productive relation, distinct from constitutive grounding
5. Current Logos implementation (Layer 0 Core TM) does NOT include constitutive or causal operators - these are planned for future Layer 1 (Explanatory Extension)

**Critical Clarification**:
The existing research-001.md correctly focuses on Layer 0 (Core TM logic: modal + temporal operators). The Constitutive and Causal layers described in LAYER_EXTENSIONS.md are part of the planned Layer 1 (Explanatory Extension), NOT part of the current Layer 0 implementation. Therefore, LaTeX documentation for these layers should be prepared as future extension subfiles, not integrated into the current Core layer documentation.

**Recommendations**:
1. Maintain research-001.md structure for Layer 0 (Core TM) documentation
2. Create preparatory subfile templates for Layer 1 (Explanatory Extension) covering Constitutive and Causal operators
3. Extract operator definitions, semantic characterizations, and examples from LAYER_EXTENSIONS.md for future Layer 1 documentation
4. Design LaTeX macro extensions for constitutive operators (≤, ⊑, ≡) and causal operator (○→)
5. Prepare standardized sections for Layer 1 following the same structure as Layer 0

---

## Context & Scope

### Research Objectives

1. Analyze LAYER_EXTENSIONS.md Overview section for Constitutive and Causal layer content
2. Extract operator definitions, semantic characterizations, and examples
3. Identify gaps between LAYER_EXTENSIONS.md and research-001.md
4. Design LaTeX documentation structure for Constitutive and Causal layers
5. Specify content extraction rules for future Layer 1 documentation
6. Create implementation roadmap for extending LaTeX documentation to Layer 1

### Constraints

- MUST focus on Constitutive Layer (constitutive operators: ≤, ⊑, ≡, ≼) and Causal Layer (causal operator: ○→)
- MUST extract content from LAYER_EXTENSIONS.md Overview section
- MUST maintain consistency with research-001.md structure
- MUST prepare for future LaTeX document extension (not immediate implementation)
- MUST distinguish between Layer 0 (Core TM - current) and Layer 1 (Explanatory - future)
- MUST provide clear guidance for documenting timeless constitutive vs. temporal causal operators

### Out of Scope

- Implementation of Layer 1 operators in Lean (future work)
- Epistemic Layer (Layer 2) and Normative Layer (Layer 3) documentation
- Modification of existing Layer 0 documentation structure
- Creation of LaTeX content (research only, not implementation)

---

## Key Findings

### Finding 1: Semantic Progression Framework

**Source**: LAYER_EXTENSIONS.md, lines 3-49

LAYER_EXTENSIONS.md provides a **semantic progression framework** that organizes Logos layers by increasing semantic complexity:

**Semantic Frame Hierarchy**:

1. **Constitutive Layer Frame** (lines 9-10):
   - **Structure**: Complete lattice of states ordered by parthood
   - **Purpose**: Assign extensions to constants, variables, functions, predicates
   - **Operators Supported**:
     - Quantifiers: ∀, ∃
     - Extensional connectives: ¬, ∧, ∨, →, ↔
     - Constitutive operators: ≡ (propositional identity), ≤ (grounding), ⊑ (essence)
   - **Semantic Clauses**: Truth conditions reference state lattice structure

2. **Causal Layer Frame** (lines 11-12):
   - **Structure**: Extends Core frame by adding task relation between states
   - **Purpose**: Distinguish productive causal relations from timeless constitutive relations
   - **Operators Supported**:
     - Historical operators: □, ◇
     - Tense operators: P, F, H, G
     - Counterfactual conditionals: □→, ◇→
     - Causation operator: ○→
   - **Semantic Clauses**: Truth conditions reference task relation and temporal ordering

**Key Insight**: The semantic progression framework reveals that constitutive and causal operators require DIFFERENT semantic frames:
- **Constitutive operators** (≤, ⊑, ≡) require state lattice with parthood ordering
- **Causal operators** (○→) require task relation with temporal ordering

**Implication for LaTeX Documentation**:
- Constitutive Layer documentation must explain state lattice semantics
- Causal Layer documentation must explain task relation semantics
- Both layers extend the Core Layer but with different semantic machinery

### Finding 2: Constitutive Operators Specification

**Source**: LAYER_EXTENSIONS.md, lines 132-176

The Overview section provides detailed specifications for three constitutive operators:

**Grounding Operator (≤)** (lines 133-145):

**Informal Characterization**: "A is sufficient for B" or "A grounds B"

**Formal Characterizations**:
- Dual to essence: `A ≤ B := ¬A ⊑ ¬B`
- Alternative definition: `A ≤ B := (A ∨ B) ≡ B`

**State-Based Semantics**: 
- In verifier/falsifier state pairs, `A ≤ B` holds when verifiers of A contained in verifiers of B
- Every way of making A true already makes B true

**Examples**:
- `[Sam is crimson] ≤ [Sam is red]` - being crimson grounds being red
- `[Sam is a robin] ≤ [Sam is a bird]` - being a robin grounds being a bird
- `[Having 79 protons] ≤ [Being gold]` - atomic structure grounds gold identity

**Essence Operator (⊑)** (lines 146-158):

**Informal Characterization**: "A is necessary for B" or "A is essential to B"

**Formal Characterizations**:
- Dual to ground: `A ⊑ B := ¬A ≤ ¬B`
- Alternative definition: `A ⊑ B := B ≡ (A ∧ B)`

**State-Based Semantics**:
- `A ⊑ B` holds when every verifier of B contains some verifier of A as part
- No way to verify B without verifying A

**Examples**:
- `[Having 79 protons] ⊑ [Being gold]` - atomic structure essential to gold
- `[Being extended] ⊑ [Being physical]` - extension essential to physicality
- `[Being trilateral] ⊑ [Being triangular]` - three sides essential to triangle

**Propositional Identity (≡)** (lines 159-171):

**Informal Characterization**: "A just is B" - strongest constitutive equivalence

**Formal Definition**: `A ≡ B := (A ≤ B) ∧ (B ≤ A)` (mutual grounding)

**Examples**:
- `[Being a vixen] ≡ [Being a female fox]` - propositionally identical definitions
- `[Being trilateral] ≡ [Being triangular]` - having three sides just is having three angles

**Contrast with Weaker Equivalences** (lines 167-170):
- Material equivalence (`A ↔ B`): Same actual truth value (weakest)
- Necessary equivalence (`□(A ↔ B)`): Same truth value at all possible worlds (stronger)
- Propositional identity (`A ≡ B`): Same metaphysical structure (strongest)

**Relevance Operator (≼)** (lines 172-176):

**Informal Characterization**: "A is wholly relevant to B"

**Definitions**:
- Via Ground: `A ≼ B := (A ∧ B) ≤ B`
- Via Essence: `A ≼ B := (A ∨ B) ⊑ B`

**Key Insight**: All four constitutive operators (≤, ⊑, ≡, ≼) are interdefinable, forming a coherent family of timeless explanatory relations.

**Implication for LaTeX Documentation**:
- Constitutive Layer subfile must include all four operators with formal definitions
- Must explain state lattice semantics (verifiers, falsifiers, parthood)
- Must provide examples distinguishing constitutive from modal necessity
- Must explain interdefinability relationships

### Finding 3: Causal Operator Specification

**Source**: LAYER_EXTENSIONS.md, lines 252-296

The Causal Layer section provides specification for the causation operator:

**Causation Operator (○→)** (lines 257-266):

**Informal Characterization**: Represents productive causal relationships with temporal character

**Contrast with Grounding** (lines 260-264):
- **Grounding (≤)**: Constitutive and timeless
  - Example: `[Sam is crimson] ≤ [Sam is red]` - timeless constitutive grounding
- **Causation (○→)**: Productive and temporal
  - Example: `[Sam touches hot stove] ○→ [Sam feels pain]` - temporal causal production

**Relationship to Counterfactuals** (lines 254-255):
- Causal claims entail counterfactual conditional claims
- Testing counterfactuals can falsify or support causal claims
- Example: If `Pushing button causes launch sequence` is true, then `If button pushed, launch sequence initiates` is also true

**Development Status** (line 266):
- Theory developed in "Hyperintensional Causation" paper
- Implementation pending in model-checker

**Medical Treatment Planning Example** (lines 268-296):

The Overview provides a detailed example showing how causal and counterfactual operators interact in medical decision-making:

**Scenario**: Physician treats hypertension patient taking medication X

**Strategy A** (lines 272-275):
```
Prescribe(DrugA) ∧ Taking(MedicationX) □→ F(Normalize(BloodPressure)) ∧ F(Occur(LiverDamage))
```
- Would-counterfactual: Drug A would normalize blood pressure but would cause liver damage

**Strategy B** (lines 276-279):
```
Continue(MedicationX) □→ F(Persist(Hypertension)) ∧ F(Increase(CardiovascularRisk))
```
- Would-counterfactual: Continuing alone would leave hypertension untreated

**Strategy C** (lines 280-284):
```
Prescribe(DrugB) ∧ Taking(MedicationX) □→ F(Normalize(BloodPressure)) ∧ ¬F(Occur(LiverDamage))
Prescribe(DrugB) ◇→ F(Occur(Stroke))
```
- Would-counterfactual: Drug B would normalize blood pressure without liver damage
- Might-counterfactual: Drug B might cause stroke with low probability

**Analysis** (lines 286-296):
- Counterfactual operators distinguish necessary consequences (□→) from possible consequences (◇→)
- Enables nuanced risk-benefit analysis
- Proof-checker verifies deductive inferences from pharmacological knowledge
- Model-checker searches for countermodels to proposed treatment strategies

**Key Insight**: Causal operator (○→) is distinct from counterfactual operators (□→, ◇→) but related:
- Causation is productive temporal relation between events
- Counterfactuals evaluate hypothetical scenarios
- Causal claims entail counterfactual claims but not vice versa

**Implication for LaTeX Documentation**:
- Causal Layer subfile must distinguish causation from counterfactuals
- Must explain temporal character of causal relations
- Must contrast with timeless constitutive grounding
- Should include medical treatment example to illustrate operator interaction

### Finding 4: Layer Architecture Clarification

**Source**: LAYER_EXTENSIONS.md lines 41-48, ARCHITECTURE.md lines 15-22

**Critical Finding**: The LAYER_EXTENSIONS.md document uses different layer terminology than the current Logos implementation:

**LAYER_EXTENSIONS.md Terminology**:
- **Core Layer**: Predicates, functions, lambdas, quantifiers, extensional operators, constitutive operators (≤, ⊑, ≡)
- **Modal Layer**: Historical, counterfactual, tense operators
- **Causal Layer**: Causal operators (○→)
- **Epistemic Layer**: Belief, probability, epistemic modals
- **Normative Layer**: Obligation, permission, preference

**Current Logos Implementation Terminology** (ARCHITECTURE.md):
- **Layer 0 (Core TM)**: Boolean, modal (□, ◇), temporal (H, G, P, F) operators - COMPLETE
- **Layer 1 (Explanatory Extension)**: Counterfactual (□→, ◇→), constitutive (≤, ⊑, ≡), causal (○→) - PLANNED
- **Layer 2 (Epistemic Extension)**: Belief, probability, epistemic modals - PLANNED
- **Layer 3 (Normative Extension)**: Obligation, permission, preference - PLANNED

**Reconciliation**:

The LAYER_EXTENSIONS.md "Core Layer" constitutive operators and "Causal Layer" causal operator are BOTH part of the Logos implementation **Layer 1 (Explanatory Extension)**, NOT Layer 0.

**Mapping**:
- LAYER_EXTENSIONS.md "Core Layer" constitutive operators → Logos Layer 1 (Explanatory Extension)
- LAYER_EXTENSIONS.md "Modal Layer" operators → Logos Layer 0 (Core TM)
- LAYER_EXTENSIONS.md "Causal Layer" operators → Logos Layer 1 (Explanatory Extension)
- LAYER_EXTENSIONS.md "Epistemic Layer" → Logos Layer 2 (Epistemic Extension)
- LAYER_EXTENSIONS.md "Normative Layer" → Logos Layer 3 (Normative Extension)

**Implication for LaTeX Documentation**:

1. **Current Documentation** (research-001.md structure):
   - Correctly focuses on Layer 0 (Core TM): modal + temporal operators
   - Subfiles: 01-Syntax.tex, 02-Semantics.tex, 03-ProofSystem.tex, 04-Metalogic.tex, 05-Theorems.tex

2. **Future Layer 1 Documentation** (this research report):
   - Should cover BOTH constitutive operators (≤, ⊑, ≡) AND causal operator (○→)
   - Subfiles: 06-Explanatory-Syntax.tex, 07-Explanatory-Semantics.tex, etc.
   - Constitutive operators section within Layer 1 documentation
   - Causal operators section within Layer 1 documentation

3. **Semantic Frame Progression**:
   - Layer 0 semantics: Task frames (W, T, ·) with task relation
   - Layer 1 semantics: Extended task frames with state lattice (for constitutive) and selection functions (for counterfactuals/causation)

### Finding 5: Gaps in Existing Research

**Source**: Comparison of research-001.md and LAYER_EXTENSIONS.md

**Gap 1: Semantic Frame Progression Not Documented**

research-001.md focuses on extracting content from LogicNotes.tex but does not incorporate the semantic progression framework from LAYER_EXTENSIONS.md.

**Missing Content**:
- Explanation of how semantic frames build incrementally
- Compositional semantics principle (formulas combining operators from multiple layers)
- Intended model concept (instantiating semantic frames with concrete structure)
- Interaction between proof-checker and model-checker

**Recommendation**: Add "Semantic Progression" subsection to 00-Introduction.tex explaining how layers build on each other.

**Gap 2: Constitutive Operators Not Covered**

research-001.md correctly excludes constitutive operators from Layer 0 documentation (they're not in current implementation), but does not prepare for future Layer 1 documentation.

**Missing Content**:
- Constitutive operator definitions (≤, ⊑, ≡, ≼)
- State lattice semantics (verifiers, falsifiers, parthood)
- Examples distinguishing constitutive from modal necessity
- Interdefinability relationships

**Recommendation**: Create preparatory Layer 1 subfile templates with constitutive operator content extracted from LAYER_EXTENSIONS.md.

**Gap 3: Causal Operator Not Covered**

research-001.md does not address causal operator (○→) or its relationship to counterfactuals.

**Missing Content**:
- Causal operator definition and semantics
- Contrast between causation (temporal, productive) and grounding (timeless, constitutive)
- Relationship between causal claims and counterfactual claims
- Medical treatment planning example

**Recommendation**: Create preparatory Layer 1 subfile templates with causal operator content extracted from LAYER_EXTENSIONS.md.

**Gap 4: Operator Interaction Not Documented**

research-001.md focuses on individual operators but does not explain how operators from different layers interact.

**Missing Content**:
- Compositional semantics for multi-layer formulas
- Examples of formulas combining operators from multiple layers
- Operator interaction principles from LAYER_EXTENSIONS.md lines 512-534

**Recommendation**: Add "Operator Interactions" section to future Layer 1+ documentation.

**Gap 5: LaTeX Macros for Constitutive/Causal Operators Not Specified**

research-001.md Analysis 3 specifies LaTeX macros for Layer 0 operators but not for Layer 1 operators.

**Missing Macros**:
- Grounding: `\leq` or `\ground`
- Essence: `\sqsubseteq` or `\essence`
- Propositional identity: `\equiv` or `\propid`
- Relevance: `\preceq` or `\relevant`
- Causation: `\circ\to` or `\causes`

**Recommendation**: Extend logos-notation.sty with Layer 1 operator macros.

---

## Detailed Analysis

### Analysis 1: Constitutive Layer Documentation Structure

**Objective**: Design LaTeX subfile structure for Constitutive Layer operators.

**Subfile**: 06-Explanatory-Syntax.tex (Constitutive Operators Section)

**Content Structure**:

```latex
\section{Explanatory Extension: Syntax}

\subsection{Constitutive Operators}

\subsubsection{Grounding Operator}

\item[\bf Grounding ($\leq$):] "A is sufficient for B" or "A grounds B" represents constitutive explanatory relationships where A metaphysically suffices for B.

\item[\bf Formal Characterizations:]
\begin{enumerate}
  \item Dual to essence: $\metaA \leq \metaB := \neg\metaA \sqsubseteq \neg\metaB$
  \item Alternative definition: $\metaA \leq \metaB := (\metaA \vee \metaB) \equiv \metaB$
\end{enumerate}

\item[\bf State-Based Semantics:] In verifier/falsifier state pairs, $\metaA \leq \metaB$ holds when verifiers of $\metaA$ are contained in verifiers of $\metaB$. Every way of making $\metaA$ true already makes $\metaB$ true.

\item[\bf Examples:]
\begin{enumerate}
  \item $[\text{Sam is crimson}] \leq [\text{Sam is red}]$ - being crimson grounds being red
  \item $[\text{Sam is a robin}] \leq [\text{Sam is a bird}]$ - being a robin grounds being a bird
  \item $[\text{Having 79 protons}] \leq [\text{Being gold}]$ - atomic structure grounds gold identity
\end{enumerate}

\subsubsection{Essence Operator}

\item[\bf Essence ($\sqsubseteq$):] "A is necessary for B" or "A is essential to B" represents constitutive necessity where A is metaphysically necessary for B.

\item[\bf Formal Characterizations:]
\begin{enumerate}
  \item Dual to ground: $\metaA \sqsubseteq \metaB := \neg\metaA \leq \neg\metaB$
  \item Alternative definition: $\metaA \sqsubseteq \metaB := \metaB \equiv (\metaA \wedge \metaB)$
\end{enumerate}

\item[\bf State-Based Semantics:] $\metaA \sqsubseteq \metaB$ holds when every verifier of $\metaB$ contains some verifier of $\metaA$ as part. No way to verify $\metaB$ without verifying $\metaA$.

\item[\bf Examples:]
\begin{enumerate}
  \item $[\text{Having 79 protons}] \sqsubseteq [\text{Being gold}]$ - atomic structure essential to gold
  \item $[\text{Being extended}] \sqsubseteq [\text{Being physical}]$ - extension essential to physicality
  \item $[\text{Being trilateral}] \sqsubseteq [\text{Being triangular}]$ - three sides essential to triangle
\end{enumerate}

\subsubsection{Propositional Identity}

\item[\bf Propositional Identity ($\equiv$):] "A just is B" - strongest constitutive equivalence where A and B mutually ground each other.

\item[\bf Formal Definition:] $\metaA \equiv \metaB := (\metaA \leq \metaB) \wedge (\metaB \leq \metaA)$ (mutual grounding)

\item[\bf Examples:]
\begin{enumerate}
  \item $[\text{Being a vixen}] \equiv [\text{Being a female fox}]$ - propositionally identical definitions
  \item $[\text{Being trilateral}] \equiv [\text{Being triangular}]$ - having three sides just is having three angles
\end{enumerate}

\item[\bf Contrast with Weaker Equivalences:]
\begin{enumerate}
  \item Material equivalence ($\metaA \leftrightarrow \metaB$): Same actual truth value (weakest)
  \item Necessary equivalence ($\Box(\metaA \leftrightarrow \metaB)$): Same truth value at all possible worlds (stronger)
  \item Propositional identity ($\metaA \equiv \metaB$): Same metaphysical structure (strongest)
\end{enumerate}

\subsubsection{Relevance Operator}

\item[\bf Relevance ($\preceq$):] "A is wholly relevant to B" - interdefinable with ground and essence.

\item[\bf Definitions:]
\begin{enumerate}
  \item Via Ground: $\metaA \preceq \metaB := (\metaA \wedge \metaB) \leq \metaB$
  \item Via Essence: $\metaA \preceq \metaB := (\metaA \vee \metaB) \sqsubseteq \metaB$
\end{enumerate}

\subsection{Extensions from Layer 0}

The Explanatory Extension adds four constitutive operators to the Layer 0 (Core TM) language:
\begin{itemize}
  \item $\leq$ (grounding): Constitutive sufficiency
  \item $\sqsubseteq$ (essence): Constitutive necessity
  \item $\equiv$ (propositional identity): Mutual grounding
  \item $\preceq$ (relevance): Wholly relevant to
\end{itemize}

These operators are timeless explanatory relations, contrasting with the temporal modal and tense operators of Layer 0.
```

**Content Sources**:
- Operator definitions: LAYER_EXTENSIONS.md lines 133-176
- Examples: LAYER_EXTENSIONS.md lines 141-145, 154-158, 164-166
- Formal characterizations: LAYER_EXTENSIONS.md lines 136-138, 149-151, 161

**Lean Cross-References** (when implemented):
- `\leansrc{Logos.Explanatory.Syntax}{ground}`
- `\leansrc{Logos.Explanatory.Syntax}{essence}`
- `\leansrc{Logos.Explanatory.Syntax}{propid}`
- `\leansrc{Logos.Explanatory.Syntax}{relevant}`

### Analysis 2: Causal Layer Documentation Structure

**Objective**: Design LaTeX subfile structure for Causal Layer operator.

**Subfile**: 06-Explanatory-Syntax.tex (Causal Operators Section)

**Content Structure**:

```latex
\subsection{Causal Operators}

\subsubsection{Causation Operator}

\item[\bf Causation ($\circ\to$):] Represents productive causal relationships with temporal character.

\item[\bf Contrast with Grounding:] Grounding ($\leq$) is constitutive and timeless, while causation ($\circ\to$) is productive and temporal.

\item[\bf Examples:]
\begin{enumerate}
  \item $[\text{Sam touches hot stove}] \circ\to [\text{Sam feels pain}]$ - temporal causal production
  \item Contrast: $[\text{Sam is crimson}] \leq [\text{Sam is red}]$ - timeless constitutive grounding
\end{enumerate}

\item[\bf Relationship to Counterfactuals:] Causal claims entail counterfactual conditional claims. Testing counterfactual conditionals may be used to falsify or support causal claims.

\item[\bf Example:] If $[\text{Pushing button}] \circ\to [\text{Launch sequence initiates}]$ is true at time $x$ in history $h$, then $[\text{Button pushed}] \boxright F[\text{Launch sequence initiates}]$ is also true at $x$ in $h$.

\item[\bf Development Status:] Theory developed in "Hyperintensional Causation" paper, implementation pending in model-checker.\leansrc{Logos.Explanatory.Syntax}{causes}

\subsubsection{Medical Treatment Planning Example}

\item[\bf Scenario:] Physician treats hypertension patient currently taking medication X. Three treatment strategies available with different risk profiles requiring counterfactual analysis.

\item[\bf Strategy A (add Drug A):]
\begin{align*}
&\text{Prescribe}(\text{DrugA}) \wedge \text{Taking}(\text{MedicationX}) \\
&\quad \boxright F(\text{Normalize}(\text{BloodPressure})) \wedge F(\text{Occur}(\text{LiverDamage}))
\end{align*}
Drug A would normalize blood pressure but would cause liver damage due to interaction with medication X (would-counterfactual: certain bad outcome).

\item[\bf Strategy B (continue medication X alone):]
\begin{align*}
&\text{Continue}(\text{MedicationX}) \\
&\quad \boxright F(\text{Persist}(\text{Hypertension})) \wedge F(\text{Increase}(\text{CardiovascularRisk}))
\end{align*}
Continuing alone would leave hypertension untreated, increasing cardiovascular risk (would-counterfactual: certain continued problem).

\item[\bf Strategy C (add Drug B):]
\begin{align*}
&\text{Prescribe}(\text{DrugB}) \wedge \text{Taking}(\text{MedicationX}) \\
&\quad \boxright F(\text{Normalize}(\text{BloodPressure})) \wedge \neg F(\text{Occur}(\text{LiverDamage})) \\
&\text{Prescribe}(\text{DrugB}) \diamondright F(\text{Occur}(\text{Stroke}))
\end{align*}
Drug B would normalize blood pressure without liver interaction but might cause stroke with low probability (might-counterfactual: possible but uncertain bad outcome).

\item[\bf Analysis:] The system weighs expected outcomes:
\begin{itemize}
  \item Certain liver damage (Strategy A)
  \item Certain continued cardiovascular risk (Strategy B)
  \item Uncertain stroke risk (Strategy C)
\end{itemize}

Counterfactual operators distinguish necessary consequences ($\boxright$ would) from possible consequences ($\diamondright$ might), enabling nuanced risk-benefit analysis. The proof-checker verifies deductive inferences from pharmacological knowledge while model-checker searches for countermodels to proposed treatment strategies.

\subsection{Extensions from Layer 0}

The Explanatory Extension adds causal operator to the Layer 0 (Core TM) language:
\begin{itemize}
  \item $\circ\to$ (causation): Temporal productive causal relation
\end{itemize}

This operator is temporal and productive, contrasting with:
\begin{itemize}
  \item Timeless constitutive grounding ($\leq$)
  \item Counterfactual conditionals ($\boxright$, $\diamondright$) which evaluate hypothetical scenarios
\end{itemize}
```

**Content Sources**:
- Causation definition: LAYER_EXTENSIONS.md lines 257-266
- Medical example: LAYER_EXTENSIONS.md lines 268-296
- Contrast with grounding: LAYER_EXTENSIONS.md lines 260-264
- Relationship to counterfactuals: LAYER_EXTENSIONS.md lines 254-255

**Lean Cross-References** (when implemented):
- `\leansrc{Logos.Explanatory.Syntax}{causes}`
- `\leansrc{Logos.Explanatory.Semantics}{causal_relation}`

### Analysis 3: Semantic Frame Documentation

**Objective**: Design LaTeX subfile structure for Constitutive and Causal layer semantics.

**Subfile**: 07-Explanatory-Semantics.tex

**Content Structure**:

```latex
\section{Explanatory Extension: Semantics}

\subsection{State Lattice Semantics (Constitutive Operators)}

\item[\bf State Lattice:] A \textbf{state lattice} is a complete lattice $\langle S, \sqsubseteq \rangle$ where $S$ is a set of states and $\sqsubseteq$ is a parthood ordering.

\item[\bf Verifiers and Falsifiers:] For each formula $\metaA$:
\begin{enumerate}
  \item $V(\metaA) \subseteq S$ is the set of \textbf{verifiers} of $\metaA$ (states that make $\metaA$ true)
  \item $F(\metaA) \subseteq S$ is the set of \textbf{falsifiers} of $\metaA$ (states that make $\metaA$ false)
\end{enumerate}

\item[\bf Grounding Semantics:] $\metaA \leq \metaB$ holds iff $V(\metaA) \subseteq V(\metaB)$.

Every verifier of $\metaA$ is a verifier of $\metaB$. Every way of making $\metaA$ true already makes $\metaB$ true.

\item[\bf Essence Semantics:] $\metaA \sqsubseteq \metaB$ holds iff for every $s \in V(\metaB)$, there exists $t \in V(\metaA)$ such that $t \sqsubseteq s$.

Every verifier of $\metaB$ contains some verifier of $\metaA$ as part.

\item[\bf Propositional Identity Semantics:] $\metaA \equiv \metaB$ holds iff $V(\metaA) = V(\metaB)$ and $F(\metaA) = F(\metaB)$.

$\metaA$ and $\metaB$ have the same verifiers and falsifiers.

\subsection{Task Relation Semantics (Causal Operators)}

\item[\bf Extended Task Frame:] An \textbf{extended task frame} is a tuple $\langle W, T, \cdot, S, \sqsubseteq \rangle$ where:
\begin{enumerate}
  \item $\langle W, T, \cdot \rangle$ is a task frame (from Layer 0)
  \item $\langle S, \sqsubseteq \rangle$ is a state lattice
  \item Each world state $w \in W$ is associated with a state $s \in S$
\end{enumerate}

\item[\bf Causal Relation:] A \textbf{causal relation} $\circ\to$ relates events at earlier times to events at later times within a world history.

\item[\bf Causation Semantics:] $\taskmodel, \worldhist, x \models \metaA \circ\to \metaB$ iff:
\begin{enumerate}
  \item There exists $y < x$ such that $\taskmodel, \worldhist, y \models \metaA$
  \item For all histories $\worldhist'$ minimally different from $\worldhist$ at $y$, if $\taskmodel, \worldhist', y \models \metaA$ then $\taskmodel, \worldhist', x \models \metaB$
\end{enumerate}

The causal relation holds when the antecedent event at an earlier time produces the consequent event at a later time across minimally different histories.

\subsection{Extensions from Layer 0}

The Explanatory Extension extends Layer 0 task frame semantics with:
\begin{itemize}
  \item State lattice $\langle S, \sqsubseteq \rangle$ for constitutive operators
  \item Verifier/falsifier sets for each formula
  \item Causal relation for temporal productive causation
  \item Selection functions for counterfactual conditionals (not detailed here)
\end{itemize}

\subsection{Compositional Semantics}

Formulas combining operators from multiple layers are evaluated in the most complex frame needed:
\begin{itemize}
  \item Layer 0 operators (modal, temporal) use task frame structure
  \item Layer 1 constitutive operators use state lattice structure
  \item Layer 1 causal operators use task relation with temporal ordering
\end{itemize}

\item[\bf Example:] $\Box(\metaA \leq \metaB)$ - "It is necessary that A grounds B"
\begin{enumerate}
  \item Evaluate $\metaA \leq \metaB$ using state lattice semantics
  \item Evaluate $\Box(\cdot)$ using task frame accessibility relation
\end{enumerate}
```

**Content Sources**:
- State lattice semantics: LAYER_EXTENSIONS.md lines 139-140, 152-153
- Compositional semantics: LAYER_EXTENSIONS.md lines 17-18
- Causal semantics: Inferred from LAYER_EXTENSIONS.md lines 254-266

**Lean Cross-References** (when implemented):
- `\leansrc{Logos.Explanatory.Semantics}{StateLattice}`
- `\leansrc{Logos.Explanatory.Semantics}{verifiers}`
- `\leansrc{Logos.Explanatory.Semantics}{falsifiers}`
- `\leansrc{Logos.Explanatory.Semantics}{causal_relation}`

### Analysis 4: LaTeX Macro Extensions for Layer 1

**Objective**: Specify LaTeX macros for constitutive and causal operators.

**File**: logos-notation.sty (Layer 1 Extensions)

**Macro Definitions**:

```latex
% ============================================================================
% Layer 1 (Explanatory Extension) Operators
% ============================================================================

% Constitutive Operators
\newcommand{\ground}{\leq}                          % Grounding (≤)
\newcommand{\essence}{\sqsubseteq}                  % Essence (⊑)
\newcommand{\propid}{\equiv}                        % Propositional identity (≡)
\newcommand{\relevant}{\preceq}                     % Relevance (≼)

% Causal Operators
\newcommand{\causes}{\circ\to}                      % Causation (○→)

% Counterfactual Operators
\newcommand{\boxright}{\Box\to}                     % Would-counterfactual (□→)
\newcommand{\diamondright}{\Diamond\to}             % Might-counterfactual (◇→)

% State Lattice Notation
\newcommand{\statelattice}{\mathcal{S}}             % State lattice S
\newcommand{\parthood}{\sqsubseteq}                 % Parthood ordering
\newcommand{\verifiers}[1]{V(#1)}                   % Verifiers of formula
\newcommand{\falsifiers}[1]{F(#1)}                  % Falsifiers of formula

% Extended Task Frame Notation
\newcommand{\extendedframe}{\mathcal{F}^+}          % Extended task frame
\newcommand{\extendedmodel}{\mathcal{M}^+}          % Extended task model

% Semantic Notation for Layer 1
\newcommand{\groundmodels}{\models_{\ground}}       % Grounding consequence
\newcommand{\causalmodels}{\models_{\causes}}       % Causal consequence

% Proof System Notation for Layer 1
\newcommand{\groundproves}{\vdash_{\ground}}        % Grounding derivability
\newcommand{\causalproves}{\vdash_{\causes}}        % Causal derivability
```

**Usage Examples**:

```latex
% Grounding
$[\text{Sam is crimson}] \ground [\text{Sam is red}]$

% Essence
$[\text{Having 79 protons}] \essence [\text{Being gold}]$

% Propositional identity
$[\text{Being a vixen}] \propid [\text{Being a female fox}]$

% Causation
$[\text{Touching hot stove}] \causes [\text{Feeling pain}]$

% Counterfactual
$[\text{Button pushed}] \boxright F[\text{Launch initiates}]$

% State lattice semantics
$\verifiers{\metaA} \subseteq \verifiers{\metaB}$

% Extended task frame
$\extendedframe = \langle W, T, \cdot, \statelattice, \parthood \rangle$
```

**Compatibility Check**:
- Verify no conflicts with existing notation.sty macros
- Test rendering in compiled PDF
- Ensure consistent spacing and alignment

---

## Decisions

### Decision 1: Layer 1 Documentation as Future Extension

**Decision**: Prepare Layer 1 (Explanatory Extension) documentation as future extension subfiles, not integrated into current Layer 0 documentation.

**Rationale**:
1. **Implementation Status**: Layer 1 operators (constitutive, causal, counterfactual) are NOT implemented in current Logos codebase
2. **Clarity**: Separating Layer 0 (current) from Layer 1 (future) avoids confusion
3. **Modularity**: Subfile architecture supports easy addition when Layer 1 implemented
4. **Consistency**: Follows same structure as research-001.md for Layer 0

**Implementation**:
- Create preparatory subfile templates: 06-Explanatory-Syntax.tex, 07-Explanatory-Semantics.tex, etc.
- Comment out in main document until Layer 1 implemented
- Include content extracted from LAYER_EXTENSIONS.md
- Add Lean cross-references as placeholders (when implemented)

### Decision 2: Combine Constitutive and Causal in Single Layer

**Decision**: Document constitutive operators (≤, ⊑, ≡) and causal operator (○→) together in Layer 1 (Explanatory Extension) subfiles.

**Rationale**:
1. **Logos Architecture**: Both are part of Layer 1 (Explanatory Extension) per ARCHITECTURE.md
2. **Semantic Relationship**: Both extend Layer 0 semantics (state lattice + task relation)
3. **Conceptual Coherence**: Both provide explanatory resources (constitutive vs. causal)
4. **Contrast**: Documenting together highlights timeless vs. temporal distinction

**Structure**:
- 06-Explanatory-Syntax.tex: Sections for constitutive operators AND causal operator
- 07-Explanatory-Semantics.tex: State lattice semantics AND causal relation semantics
- 08-Explanatory-ProofSystem.tex: Axioms for both operator families
- 09-Explanatory-Metalogic.tex: Soundness/completeness for Layer 1
- 10-Explanatory-Theorems.tex: Key theorems involving both operator types

### Decision 3: Include Medical Treatment Example

**Decision**: Include the medical treatment planning example from LAYER_EXTENSIONS.md in Layer 1 documentation.

**Rationale**:
1. **Pedagogical Value**: Concrete example illustrates operator interaction
2. **Minimal Explanation**: Example is concise (fits minimal explanation policy)
3. **Operator Interaction**: Shows how causal and counterfactual operators work together
4. **Risk-Benefit Analysis**: Demonstrates practical application for AI planning

**Placement**: 06-Explanatory-Syntax.tex, subsection "Medical Treatment Planning Example" under Causal Operators section

**Content**: Extract verbatim from LAYER_EXTENSIONS.md lines 268-296

### Decision 4: State Lattice Semantics Explanation

**Decision**: Include detailed explanation of state lattice semantics (verifiers, falsifiers, parthood) in Layer 1 documentation.

**Rationale**:
1. **Semantic Foundation**: State lattice is essential for constitutive operators
2. **Novel Concept**: Not covered in Layer 0 documentation (task frames are different)
3. **Formal Precision**: Verifier/falsifier semantics provides formal grounding for informal characterizations
4. **Minimal but Sufficient**: Can be explained concisely (1-2 pages)

**Placement**: 07-Explanatory-Semantics.tex, subsection "State Lattice Semantics (Constitutive Operators)"

**Content**: Extract from LAYER_EXTENSIONS.md lines 139-140, 152-153 and expand with formal definitions

### Decision 5: Interdefinability Relationships

**Decision**: Document interdefinability relationships between constitutive operators (≤, ⊑, ≡, ≼).

**Rationale**:
1. **Formal Precision**: Shows operators form coherent family
2. **Theoretical Insight**: Reveals deep connections between operators
3. **Proof Strategy**: Enables proving theorems about one operator via another
4. **Minimal Explanation**: Can be stated concisely as formal definitions

**Placement**: 06-Explanatory-Syntax.tex, subsection "Interdefinability" after individual operator definitions

**Content**:
```latex
\subsection{Interdefinability of Constitutive Operators}

The four constitutive operators are interdefinable:

\begin{enumerate}
  \item $\metaA \leq \metaB := \neg\metaA \sqsubseteq \neg\metaB$ (ground via essence)
  \item $\metaA \sqsubseteq \metaB := \neg\metaA \leq \neg\metaB$ (essence via ground)
  \item $\metaA \equiv \metaB := (\metaA \leq \metaB) \wedge (\metaB \leq \metaA)$ (propid via ground)
  \item $\metaA \preceq \metaB := (\metaA \wedge \metaB) \leq \metaB$ (relevance via ground)
  \item $\metaA \preceq \metaB := (\metaA \vee \metaB) \sqsubseteq \metaB$ (relevance via essence)
\end{enumerate}

These interdefinability relationships show that the constitutive operators form a coherent family of timeless explanatory relations.
```

---

## Recommendations

### Recommendation 1: Layer 1 Subfile Templates

**Recommendation**: Create preparatory subfile templates for Layer 1 (Explanatory Extension) with content extracted from LAYER_EXTENSIONS.md.

**Subfiles to Create**:

1. **06-Explanatory-Syntax.tex**:
   - Constitutive operators section (≤, ⊑, ≡, ≼)
   - Causal operator section (○→)
   - Counterfactual operators section (□→, ◇→)
   - Interdefinability relationships
   - Extensions from Layer 0

2. **07-Explanatory-Semantics.tex**:
   - State lattice semantics (verifiers, falsifiers, parthood)
   - Grounding, essence, propositional identity semantics
   - Extended task frame definition
   - Causal relation semantics
   - Selection functions for counterfactuals
   - Compositional semantics for multi-layer formulas

3. **08-Explanatory-ProofSystem.tex**:
   - Constitutive axioms (when developed)
   - Causal axioms (when developed)
   - Counterfactual axioms (when developed)
   - Inference rules for Layer 1
   - Extensions from Layer 0

4. **09-Explanatory-Metalogic.tex**:
   - Soundness for Layer 1 (when proven)
   - Completeness for Layer 1 (when proven)
   - Decidability (when established)
   - Characterization results

5. **10-Explanatory-Theorems.tex**:
   - Key theorems involving constitutive operators
   - Key theorems involving causal operators
   - Operator interaction theorems
   - Derived results

**Content Sources**:
- LAYER_EXTENSIONS.md lines 51-296 (Core Layer, Modal Layer, Causal Layer sections)
- Future Lean implementation in Logos/Explanatory/

**Timeline**: Create templates when Layer 1 implementation begins (3-6 months post Core MVP per Explanatory/README.md)

### Recommendation 2: Semantic Progression Introduction

**Recommendation**: Add "Semantic Progression" subsection to 00-Introduction.tex explaining how Logos layers build incrementally.

**Content**:

```latex
\subsection{Semantic Progression}

The Logos system is organized into a series of expressive layers, each corresponding to a semantic frame of increasing complexity. A \textbf{semantic frame} defines the primitive semantic structure needed to interpret logical formulas by specifying what kinds of elements exist in the semantic domain and how truth conditions are evaluated.

\subsubsection{Layer 0: Core TM Logic}

The Core Layer (documented in this reference) provides:
\begin{itemize}
  \item \textbf{Task Frame}: $\langle W, T, \cdot \rangle$ with world states, time group, and task relation
  \item \textbf{Operators}: Modal ($\Box$, $\Diamond$), temporal ($H$, $G$, $P$, $F$), propositional ($\neg$, $\wedge$, $\vee$, $\to$)
  \item \textbf{Semantics}: Truth evaluation at world history and time
\end{itemize}

\subsubsection{Layer 1: Explanatory Extension (Future)}

The Explanatory Extension will add:
\begin{itemize}
  \item \textbf{State Lattice}: $\langle S, \sqsubseteq \rangle$ for constitutive operators
  \item \textbf{Operators}: Grounding ($\leq$), essence ($\sqsubseteq$), propositional identity ($\equiv$), causation ($\circ\to$), counterfactuals ($\boxright$, $\diamondright$)
  \item \textbf{Semantics}: Verifier/falsifier sets, causal relations, selection functions
\end{itemize}

\subsubsection{Compositional Semantics}

Formulas combining operators from multiple layers are evaluated in the most complex frame needed, which contains all the semantic machinery required for each operator. For example, $\Box(\metaA \leq \metaB)$ ("It is necessary that A grounds B") combines modal necessity (Layer 0) with grounding (Layer 1), requiring an extended task frame with state lattice.
```

**Placement**: 00-Introduction.tex, after "Layer Architecture" subsection

**Source**: LAYER_EXTENSIONS.md lines 3-25

### Recommendation 3: Operator Contrast Tables

**Recommendation**: Include comparison tables contrasting related operators to highlight distinctions.

**Table 1: Constitutive vs. Modal Necessity**

```latex
\begin{table}[h]
\centering
\begin{tabular}{|l|l|l|}
\hline
\textbf{Operator} & \textbf{Type} & \textbf{Example} \\
\hline
Material equivalence ($\leftrightarrow$) & Extensional & Same truth value \\
Necessary equivalence ($\Box(\cdot \leftrightarrow \cdot)$) & Modal & Same truth value at all worlds \\
Propositional identity ($\equiv$) & Constitutive & Same metaphysical structure \\
\hline
\end{tabular}
\caption{Hierarchy of equivalence relations from weakest to strongest}
\end{table}
```

**Table 2: Constitutive vs. Causal Relations**

```latex
\begin{table}[h]
\centering
\begin{tabular}{|l|l|l|}
\hline
\textbf{Operator} & \textbf{Character} & \textbf{Example} \\
\hline
Grounding ($\leq$) & Timeless, constitutive & Being crimson grounds being red \\
Causation ($\circ\to$) & Temporal, productive & Touching stove causes pain \\
\hline
\end{tabular}
\caption{Contrast between constitutive and causal explanatory relations}
\end{table}
```

**Placement**: 06-Explanatory-Syntax.tex, after operator definitions

**Source**: LAYER_EXTENSIONS.md lines 167-170, 260-264

### Recommendation 4: Update Main Document Structure

**Recommendation**: Update LogosReference.tex to include commented-out Layer 1 subfiles for future activation.

**Updated Structure**:

```latex
\begin{document}
\maketitle
\tableofcontents

% ============================================================================
% Layer 0: Core TM Logic (Current Implementation)
% ============================================================================

\subfile{subfiles/00-Introduction}
\subfile{subfiles/01-Syntax}
\subfile{subfiles/02-Semantics}
\subfile{subfiles/03-ProofSystem}
\subfile{subfiles/04-Metalogic}
\subfile{subfiles/05-Theorems}

% ============================================================================
% Layer 1: Explanatory Extension (Future Implementation)
% ============================================================================

% Uncomment when Layer 1 implemented in Lean:
% \subfile{subfiles/06-Explanatory-Syntax}
% \subfile{subfiles/07-Explanatory-Semantics}
% \subfile{subfiles/08-Explanatory-ProofSystem}
% \subfile{subfiles/09-Explanatory-Metalogic}
% \subfile{subfiles/10-Explanatory-Theorems}

% ============================================================================
% Layer 2: Epistemic Extension (Future Implementation)
% ============================================================================

% Uncomment when Layer 2 implemented in Lean:
% \subfile{subfiles/11-Epistemic-Syntax}
% \subfile{subfiles/12-Epistemic-Semantics}
% \subfile{subfiles/13-Epistemic-ProofSystem}
% \subfile{subfiles/14-Epistemic-Metalogic}
% \subfile{subfiles/15-Epistemic-Theorems}

% ============================================================================
% Layer 3: Normative Extension (Future Implementation)
% ============================================================================

% Uncomment when Layer 3 implemented in Lean:
% \subfile{subfiles/16-Normative-Syntax}
% \subfile{subfiles/17-Normative-Semantics}
% \subfile{subfiles/18-Normative-ProofSystem}
% \subfile{subfiles/19-Normative-Metalogic}
% \subfile{subfiles/20-Normative-Theorems}

\bibliographystyle{assets/bib_style}
\bibliography{bibliography/LogosReferences}
\end{document}
```

**Rationale**:
- Clear separation between current and future layers
- Easy activation when layers implemented
- Maintains consistent structure across all layers

### Recommendation 5: Bibliography Entries

**Recommendation**: Add bibliography entries for key references on constitutive and causal operators.

**Bibliography Entries** (LogosReferences.bib):

```bibtex
@article{fine2012guide,
  title={Guide to Ground},
  author={Fine, Kit},
  journal={Metaphysical Grounding: Understanding the Structure of Reality},
  pages={37--80},
  year={2012},
  publisher={Cambridge University Press}
}

@article{rosen2010metaphysical,
  title={Metaphysical Dependence: Grounding and Reduction},
  author={Rosen, Gideon},
  journal={Modality: Metaphysics, Logic, and Epistemology},
  pages={109--136},
  year={2010},
  publisher={Oxford University Press}
}

@article{schaffer2009spacetime,
  title={Spacetime the One Substance},
  author={Schaffer, Jonathan},
  journal={Philosophical Studies},
  volume={145},
  number={1},
  pages={131--148},
  year={2009},
  publisher={Springer}
}

@article{woodward2003making,
  title={Making Things Happen: A Theory of Causal Explanation},
  author={Woodward, James},
  year={2003},
  publisher={Oxford University Press}
}

@article{pearl2009causality,
  title={Causality: Models, Reasoning and Inference},
  author={Pearl, Judea},
  year={2009},
  edition={2nd},
  publisher={Cambridge University Press}
}

@unpublished{brastmckie2024hyperintensional,
  title={Hyperintensional Causation},
  author={Brast-McKie, Benjamin},
  note={Manuscript in preparation},
  year={2024}
}
```

**Placement**: bibliography/LogosReferences.bib

**Usage**: Cite in Layer 1 subfiles when discussing constitutive and causal operators

---

## Risks & Mitigations

### Risk 1: Layer Terminology Confusion

**Risk**: Confusion between LAYER_EXTENSIONS.md terminology (Core/Modal/Causal layers) and Logos implementation terminology (Layer 0/1/2/3).

**Likelihood**: Medium

**Impact**: Medium (documentation inconsistency)

**Mitigation**:
1. **Clarification Note**: Add note to 00-Introduction.tex explaining terminology difference
2. **Consistent Usage**: Use Logos implementation terminology (Layer 0/1/2/3) throughout LaTeX documentation
3. **Cross-Reference**: Include footnote referencing LAYER_EXTENSIONS.md terminology mapping
4. **Glossary Entry**: Add glossary entry explaining layer terminology

**Clarification Note** (for 00-Introduction.tex):

```latex
\subsection{Note on Layer Terminology}

This reference uses the Logos implementation layer terminology:
\begin{itemize}
  \item \textbf{Layer 0 (Core TM)}: Modal and temporal operators (current implementation)
  \item \textbf{Layer 1 (Explanatory Extension)}: Constitutive, causal, counterfactual operators (future)
  \item \textbf{Layer 2 (Epistemic Extension)}: Belief, probability, epistemic modal operators (future)
  \item \textbf{Layer 3 (Normative Extension)}: Obligation, permission, preference operators (future)
\end{itemize}

Note: The research document LAYER\_EXTENSIONS.md uses different terminology ("Core Layer" for constitutive operators, "Modal Layer" for modal/temporal operators, "Causal Layer" for causal operators). In this reference, constitutive and causal operators are both part of Layer 1 (Explanatory Extension).
```

### Risk 2: Premature Layer 1 Documentation

**Risk**: Creating detailed Layer 1 documentation before implementation may become outdated if design changes.

**Likelihood**: Medium

**Impact**: Low (templates can be updated)

**Mitigation**:
1. **Template Approach**: Create templates with placeholders, not final content
2. **Version Control**: Track changes to LAYER_EXTENSIONS.md and update templates accordingly
3. **Lean Cross-References**: Use placeholders for Lean cross-references (when implemented)
4. **Review Cycle**: Review and update templates when Layer 1 implementation begins

**Template Placeholder Example**:

```latex
\item[\bf Grounding Axioms:] [TO BE DETERMINED - pending Layer 1 implementation]

% Placeholder axioms based on LAYER_EXTENSIONS.md:
% - Reflexivity: A ≤ A
% - Transitivity: (A ≤ B) ∧ (B ≤ C) → (A ≤ C)
% - Antisymmetry: (A ≤ B) ∧ (B ≤ A) → (A ≡ B)

\leansrc{Logos.Explanatory.ProofSystem}{ground_axioms} % Placeholder
```

### Risk 3: State Lattice Semantics Complexity

**Risk**: State lattice semantics (verifiers, falsifiers, parthood) may be too complex for "minimal explanation" policy.

**Likelihood**: Low

**Impact**: Medium (documentation becomes too verbose)

**Mitigation**:
1. **Formal Definitions Only**: Provide formal definitions without extended explanations
2. **Examples**: Use 1-2 examples to illustrate verifier/falsifier semantics
3. **Cross-Reference**: Reference external papers (Fine 2012, Rosen 2010) for detailed explanations
4. **Length Limit**: Limit state lattice section to 2 pages maximum

**Concise State Lattice Section** (example):

```latex
\subsection{State Lattice Semantics}

\item[\bf State Lattice:] $\langle S, \sqsubseteq \rangle$ where $S$ is a set of states and $\sqsubseteq$ is a parthood ordering.

\item[\bf Verifiers:] $V(\metaA) = \{s \in S : s \text{ makes } \metaA \text{ true}\}$

\item[\bf Falsifiers:] $F(\metaA) = \{s \in S : s \text{ makes } \metaA \text{ false}\}$

\item[\bf Grounding Semantics:] $\metaA \leq \metaB$ iff $V(\metaA) \subseteq V(\metaB)$

\item[\bf Example:] $[\text{crimson}] \leq [\text{red}]$ because every state that makes "crimson" true also makes "red" true.

For detailed exposition, see Fine (2012) and Rosen (2010).
```

---

## Appendix: Content Extraction from LAYER_EXTENSIONS.md

### Constitutive Operators Content

**Grounding (≤)** - Lines 133-145:
- Informal: "A is sufficient for B" or "A grounds B"
- Formal: `A ≤ B := ¬A ⊑ ¬B` or `A ≤ B := (A ∨ B) ≡ B`
- Semantics: Verifiers of A contained in verifiers of B
- Examples: crimson→red, robin→bird, 79 protons→gold

**Essence (⊑)** - Lines 146-158:
- Informal: "A is necessary for B" or "A is essential to B"
- Formal: `A ⊑ B := ¬A ≤ ¬B` or `A ⊑ B := B ≡ (A ∧ B)`
- Semantics: Every verifier of B contains verifier of A as part
- Examples: 79 protons⊑gold, extended⊑physical, trilateral⊑triangular

**Propositional Identity (≡)** - Lines 159-171:
- Informal: "A just is B"
- Formal: `A ≡ B := (A ≤ B) ∧ (B ≤ A)`
- Examples: vixen≡female fox, trilateral≡triangular
- Contrast: Material (↔), necessary (□(↔)), propositional (≡)

**Relevance (≼)** - Lines 172-176:
- Informal: "A is wholly relevant to B"
- Formal: `A ≼ B := (A ∧ B) ≤ B` or `A ≼ B := (A ∨ B) ⊑ B`

### Causal Operator Content

**Causation (○→)** - Lines 257-266:
- Informal: Productive causal relationships with temporal character
- Contrast: Grounding (timeless, constitutive) vs. Causation (temporal, productive)
- Examples: touching stove→pain (causal) vs. crimson→red (grounding)
- Status: Theory developed, implementation pending

**Medical Treatment Example** - Lines 268-296:
- Scenario: Hypertension treatment with 3 strategies
- Strategy A: DrugA + MedX → normalize BP + liver damage (certain)
- Strategy B: MedX alone → persist hypertension + cardiovascular risk (certain)
- Strategy C: DrugB + MedX → normalize BP (certain) + stroke (possible)
- Analysis: Counterfactuals distinguish necessary (□→) from possible (◇→) consequences

### Semantic Progression Content

**Framework** - Lines 3-25:
- Semantic frames define primitive structure for truth evaluation
- Layers build systematically with increasing complexity
- Compositional semantics: Multi-layer formulas use most complex frame
- Intended models instantiate frames with concrete structure

**Constitutive Layer Frame** - Lines 9-10:
- Complete lattice of states ordered by parthood
- Supports quantifiers, extensional connectives, constitutive operators

**Causal Layer Frame** - Lines 11-12:
- Extends Core frame with task relation between states
- Supports historical, tense, counterfactual, causation operators

---

**End of Supplemental Research Report**
