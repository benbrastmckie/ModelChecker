# Research Report: LaTeX Documentation Structure for Logos Layers

**Task**: 334 - Create a copy of /home/benjamin/Projects/Philosophy/Teaching/LogicNotes/ in /home/benjamin/Projects/ProofChecker/Documentation/LaTeX/ with a cleaned up structure that mirrors the Logos layers

**Started**: 2026-01-08T19:30:00Z

**Completed**: 2026-01-08T20:15:00Z

**Effort**: 2-3 days implementation

**Priority**: Medium

**Dependencies**: None

**Sources/Inputs**:
- Source LaTeX: /home/benjamin/Projects/Philosophy/Teaching/LogicNotes/LogicNotes.tex (1452 lines)
- Source assets: /home/benjamin/Projects/Philosophy/Teaching/LogicNotes/assets/ (5 style files)
- Logos codebase: /home/benjamin/Projects/ProofChecker/Logos/
- Architecture documentation: Documentation/UserGuide/ARCHITECTURE.md
- Implementation status: Documentation/ProjectInfo/IMPLEMENTATION_STATUS.md

**Artifacts**:
- This research report: .opencode/specs/334_latex_documentation_structure/reports/research-001.md

**Standards**: status-markers.md, artifact-management.md, tasks.md, report.md

---

## Executive Summary

This research analyzes the source LaTeX structure from LogicNotes.tex and maps it to the Logos layer architecture to design a cleaned-up LaTeX reference documentation. The source document is a comprehensive 1452-line logic course covering propositional logic through bimodal logic with problem sets. The target documentation will reorganize this content into layer-specific subfiles mirroring the Logos Core layer structure, excluding problem sets, and focusing on definitions and metalogical properties without proofs.

**Key Findings**:
1. Source structure contains 6 major logic systems with clear section boundaries
2. Logos implements a 5-layer architecture (Layer 0 Core + 3 future extensions + Examples)
3. Direct mapping exists between source sections and Logos Core components
4. LaTeX formatting standards are well-established with 5 custom style files
5. Bimodal TM logic is the primary focus, with modal and temporal logic as prerequisites

**Recommendations**:
1. Create main document LogosReference.tex with subfile architecture
2. Generate 5 subfiles for Core layer components (Syntax, Semantics, ProofSystem, Metalogic, Theorems)
3. Preserve formatting.sty, notation.sty, and proof_styles.sty from source
4. Exclude all problem sets and proofs, focusing on definitions only
5. Add standardized sections per layer as specified in requirements

---

## Context & Scope

### Research Objectives

1. Analyze source LaTeX document structure and content organization
2. Map source sections to Logos layer architecture
3. Identify formatting standards and style dependencies
4. Design target directory structure and subfile organization
5. Specify content extraction and transformation rules
6. Create implementation roadmap for documentation generation

### Constraints

- MUST exclude all problem sets from source
- MUST exclude proofs, keeping only definitions and theorem statements
- MUST maintain source formatting standards
- MUST create subfile for each Logos layer component
- MUST include standardized sections: Syntax extensions, Semantic frames/models, Proof system extensions, Metalogical properties
- MUST be readable without Lean code knowledge
- MUST compile as valid LaTeX document

### Out of Scope

- Implementation of LaTeX generation (research only)
- Modification of Lean source code
- Creation of new mathematical content
- Translation to other formats (HTML, PDF generation)

---

## Key Findings

### Finding 1: Source Document Structure

**Source**: /home/benjamin/Projects/Philosophy/Teaching/LogicNotes/LogicNotes.tex

The source document follows a progressive logic curriculum structure:

**Section Breakdown** (by line numbers):
1. Lines 27-69: Propositional Logic - Syntax and Semantics (13 definitions)
2. Lines 70-115: Problem Set - Metalinguistic Abbreviation [EXCLUDE]
3. Lines 117-270: Propositional Logic - Fitch System (natural deduction rules) [EXCLUDE - not in Logos]
4. Lines 271-322: Problem Set - Regimentation and Deduction [EXCLUDE]
5. Lines 323-360: Propositional Logic - Hilbert System (axioms K, S, MP rule)
6. Lines 361-403: Problem Sets - Derived Metarules and Axiomatic Proofs [EXCLUDE]
7. Lines 404-427: Modal Logic - Motivation (informal introduction)
8. Lines 428-470: Modal Logic - Syntax (language ML, operators, abbreviations)
9. Lines 449-470: Problem Set - Syntax [EXCLUDE]
10. Lines 471-557: Modal Logic - Axiomatic Systems (K, D, T, B, S4, S5 systems)
11. Lines 517-557: Problem Set - Axiomatic Proofs [EXCLUDE]
12. Lines 558-607: Modal Logic - Frames (Kripke semantics, frame constraints)
13. Lines 587-607: Problem Set - Frames [EXCLUDE]
14. Lines 608-688: Modal Logic - Logical Consequence (validity, soundness, completeness)
15. Lines 633-688: Problem Set - Logical Consequence [EXCLUDE]
16. Lines 689-778: Modal Logic - Metalogic (soundness, completeness, characterization theorems)
17. Lines 722-778: Problem Set - Metalogic [EXCLUDE]
18. Lines 779-848: Tense Logic - Syntax (operators Past, Future, abbreviations)
19. Lines 827-848: Problem Set - Syntax [EXCLUDE]
20. Lines 849-906: Tense Logic - Frames (temporal frames, frame constraints)
21. Lines 886-906: Problem Set - Frames [EXCLUDE]
22. Lines 907-964: Tense Logic - Logical Consequence (validity over temporal frames)
23. Lines 965-1026: Tense Logic - Axiomatic System (TK, T4, TA, TL axioms)
24. Lines 992-1026: Problem Sets - Tense Proofs [EXCLUDE]
25. Lines 1027-1098: Problem Set - Characterization [EXCLUDE]
26. Lines 1099-1123: Bimodal Logic - Tense and Modality (motivation, perpetuity intuitions)
27. Lines 1124-1176: Bimodal Logic - Syntax (language BL, combined operators)
28. Lines 1141-1176: Problem Set - Syntax [EXCLUDE]
29. Lines 1177-1237: Bimodal Logic - Semantics (task frames, world histories, truth conditions)
30. Lines 1215-1237: Problem Set - Semantics [EXCLUDE]
31. Lines 1238-1287: Bimodal Logic - Axiomatic System (TM system, perpetuity principles P1-P6)
32. Lines 1264-1287: Problem Set - Derivations [EXCLUDE]
33. Lines 1288-1309: Bimodal Logic - Metatheory [COMMENTED OUT - incomplete]
34. Lines 1310-1344: Problem Set - Metatheory [COMMENTED OUT - incomplete]
35. Lines 1345-1436: Bimodal Logic - Extensions (extended language, open futures/pasts)
36. Lines 1397-1436: Problem Set - Extensions [EXCLUDE]

**Content Statistics**:
- Total lines: 1452
- Problem set lines: ~400 (27% of document)
- Core content lines: ~1050 (73% of document)
- Sections: 38 total (19 content + 19 problem sets)

**Key Observations**:
1. Clear hierarchical structure: System → Component (Syntax/Semantics/Proof/Meta)
2. Problem sets immediately follow each content section
3. Consistent formatting: enumerate environments with leftmargin=1.2in
4. Abbreviations defined systematically with ≔ notation
5. Bimodal TM logic (lines 1099-1436) is the culmination, building on modal and temporal

### Finding 2: Logos Layer Architecture

**Source**: Logos/README.md, Documentation/UserGuide/ARCHITECTURE.md

Logos implements a **5-layer architecture**:

**Layer 0 (Core TM Logic)** - COMPLETE:
- **Syntax/**: Formula type (atom, bot, imp, box, all_past, all_future)
  - Formula.lean: Inductive formula type with 6 constructors
  - Context.lean: Proof context lists
- **ProofSystem/**: Axioms and derivation trees
  - Axioms.lean: 14 axiom schemata (4 propositional + 4 modal + 4 temporal + 2 interaction)
  - Derivation.lean: DerivationTree inductive type with 7 inference rules
- **Semantics/**: Task frame semantics
  - TaskFrame.lean: Task frame structure (WorldState, time group, task relation)
  - TaskModel.lean: Models with valuation
  - Truth.lean: Truth evaluation at world history and time
  - Validity.lean: Semantic consequence
  - WorldHistory.lean: World history functions over task frames
- **Metalogic/**: Soundness and completeness
  - Soundness.lean: Soundness theorem (derivability → validity)
  - SoundnessLemmas.lean: Helper lemmas for soundness proof
  - Completeness.lean: Canonical model construction (infrastructure only)
  - DeductionTheorem.lean: Deduction theorem for TM logic
- **Theorems/**: Key theorems and principles
  - Propositional.lean: Propositional tautologies
  - ModalS4.lean: S4 modal theorems
  - ModalS5.lean: S5 modal theorems
  - Perpetuity/: Perpetuity principles P1-P6 (all proven)
    - Principles.lean: P1-P5 proofs
    - Bridge.lean: P6 proof and bridge lemmas
    - Helpers.lean: Helper lemmas
  - Combinators.lean: Propositional combinators
  - GeneralizedNecessitation.lean: Generalized necessitation rule
- **Automation/**: Proof automation (partial)
  - Tactics.lean: Custom tactics (stubs)
  - ProofSearch.lean: Automated proof search (partial)
  - AesopRules.lean: Aesop integration rules

**Layer 1 (Explanatory Extension)** - PLANNED:
- Counterfactual operators (□→, ◇→)
- Constitutive operators (≤, ⊑, ≡)
- Causal operators (○→)

**Layer 2 (Epistemic Extension)** - PLANNED:
- Belief operators (B, B_a)
- Probability operators (Pr, Pr_a)
- Knowledge operators (K, K_a)

**Layer 3 (Normative Extension)** - PLANNED:
- Deontic operators (O, P, F)
- Preference operators (≻, ≽)
- Ought operators (Ought, Ought_a)

**Examples/**: Proof examples and strategies
- BimodalProofs.lean, ModalProofs.lean, TemporalProofs.lean
- BimodalProofStrategies.lean, ModalProofStrategies.lean, TemporalProofStrategies.lean
- TemporalStructures.lean

**Key Observations**:
1. Layer 0 (Core) is production-ready with 100% completion
2. Future layers (1-3) are planned but not implemented
3. Core layer has 5 major components matching LaTeX structure
4. Perpetuity principles (P1-P6) are fully proven in Lean
5. Automation layer is partial (tactics stubs, proof search incomplete)

### Finding 3: Source-to-Target Mapping

**Direct Mapping** (Source LaTeX → Logos Core):

| Source Section | Lines | Logos Component | Target Subfile |
|----------------|-------|-----------------|----------------|
| Propositional Logic - Hilbert System | 323-360 | ProofSystem/Axioms.lean (prop_k, prop_s) | 03-ProofSystem.tex |
| Modal Logic - Syntax | 428-470 | Syntax/Formula.lean (box operator) | 01-Syntax.tex |
| Modal Logic - Axiomatic Systems | 471-557 | ProofSystem/Axioms.lean (modal_t, modal_4, modal_b, modal_5) | 03-ProofSystem.tex |
| Modal Logic - Frames | 558-607 | Semantics/TaskFrame.lean (frame structure) | 02-Semantics.tex |
| Modal Logic - Logical Consequence | 608-688 | Semantics/Validity.lean (validity definition) | 02-Semantics.tex |
| Modal Logic - Metalogic | 689-778 | Metalogic/Soundness.lean, Completeness.lean | 04-Metalogic.tex |
| Tense Logic - Syntax | 779-848 | Syntax/Formula.lean (all_past, all_future) | 01-Syntax.tex |
| Tense Logic - Frames | 849-906 | Semantics/TaskFrame.lean (temporal constraints) | 02-Semantics.tex |
| Tense Logic - Axiomatic System | 965-1026 | ProofSystem/Axioms.lean (temp_k_dist, temp_4, temp_a, temp_l) | 03-ProofSystem.tex |
| Bimodal Logic - Motivation | 1099-1123 | (Introduction to main document) | LogosReference.tex |
| Bimodal Logic - Syntax | 1124-1176 | Syntax/Formula.lean (complete formula type) | 01-Syntax.tex |
| Bimodal Logic - Semantics | 1177-1237 | Semantics/ (all files) | 02-Semantics.tex |
| Bimodal Logic - Axiomatic System | 1238-1287 | ProofSystem/ (complete axiom set) | 03-ProofSystem.tex |
| Bimodal Logic - Extensions | 1345-1436 | (Future work - Layer 1) | [Appendix or omit] |
| Perpetuity Principles P1-P6 | 1251-1263 | Theorems/Perpetuity/ | 05-Theorems.tex |

**Content Transformation Rules**:
1. **Include**: All definition environments (enumerate with \bf labels)
2. **Include**: Axiom schemata with formal notation
3. **Include**: Theorem statements (without proofs)
4. **Include**: Semantic clauses (truth conditions, validity)
5. **Exclude**: All problem sets (sections with \it Problem Set)
6. **Exclude**: All proofs (fitch environments, proof blocks)
7. **Exclude**: Fitch natural deduction system (not in Logos)
8. **Exclude**: Motivational examples (unless brief)
9. **Transform**: Reorder content by Logos layer component
10. **Transform**: Add "Extensions from previous layer" sections

**Mapping Confidence**: HIGH
- Clear 1-to-1 correspondence between LaTeX sections and Lean modules
- Consistent terminology (box, all_past, all_future, task frame, etc.)
- Perpetuity principles explicitly named P1-P6 in both sources

### Finding 4: LaTeX Formatting Standards

**Source**: /home/benjamin/Projects/Philosophy/Teaching/LogicNotes/assets/

**Style Files** (5 total):
1. **formatting.sty** (6039 bytes):
   - Bibliography support (natbib, bibentry)
   - Graphics and color (graphicx, xcolor)
   - Glossary support (glossaries)
   - Custom citation commands (\citepos for possessive citations)
   
2. **notation.sty** (19573 bytes):
   - Custom logic notation commands
   - Operator definitions (\Box, \Diamond, \Past, \Future, etc.)
   - Abbreviation macros (\PL, \ML, \TL, \BL for languages)
   - Semantic notation (\PLmodels, \MLmodels, \taskmodel, etc.)
   - Proof system notation (\Kproves, \TMproves, etc.)
   
3. **proof_styles.sty** (20798 bytes):
   - Fitch-style proof environments
   - Natural deduction rule formatting
   - Proof tree macros
   
4. **bib_style.bst** (30890 bytes):
   - Bibliography style definitions
   
5. **glossary.tex** (4251 bytes):
   - Glossary entries for logic terms

**Document Class and Packages** (LogicNotes.tex lines 1-25):
```latex
\documentclass[a4paper, 11pt]{article}
\usepackage[top=1.1in, bottom=1.1in]{geometry}
\usepackage[protrusion=true,expansion=true]{microtype}
\usepackage{assets/formatting}
\usepackage{assets/proof_styles}
\usepackage{assets/notation}
```

**Formatting Conventions**:
1. **Section headers**: `\section*{\sc Title}` (small caps, unnumbered)
2. **Definition lists**: `\begin{enumerate}[leftmargin=1.2in]` with `\item[\bf Label:]`
3. **Abbreviations**: `\coloneq` for definitional equality (≔)
4. **Formulas**: Inline math `$\Box\metaA$` with metavariables `\metaA`, `\metaB`
5. **Semantic notation**: `\M\vDash \metaA` for truth, `\MetaG \vDash \metaA` for consequence
6. **Proof notation**: `\MetaG \Qproves \metaA` for derivability in system Q
7. **Multicols**: Two-column layouts for axiom lists
8. **Corner quotes**: `\corner{\cdot}` for quotation names

**Key Observations**:
1. Heavy reliance on custom notation.sty for logic symbols
2. Consistent use of enumerate environments for definitions
3. Small caps for section titles, bold for definition labels
4. Metavariables (φ, ψ, χ) vs. concrete formulas (p₁, p₂)
5. Proof_styles.sty only needed for Fitch proofs (exclude from target)

**Recommendation**: 
- **Preserve**: formatting.sty, notation.sty (essential)
- **Exclude**: proof_styles.sty (Fitch proofs not in Logos)
- **Preserve**: bib_style.bst, glossary.tex (for references)
- **Add**: Custom macros for Logos-specific notation (task frames, world histories)

### Finding 5: Target Documentation Structure

**Target Directory**: /home/benjamin/Projects/ProofChecker/Documentation/LaTeX/

**Proposed Structure**:
```
Documentation/LaTeX/
├── LogosReference.tex              # Main document
├── subfiles/
│   ├── 00-Introduction.tex         # Overview, motivation, perpetuity intuitions
│   ├── 01-Syntax.tex               # Layer 0 Syntax component
│   ├── 02-Semantics.tex            # Layer 0 Semantics component
│   ├── 03-ProofSystem.tex          # Layer 0 ProofSystem component
│   ├── 04-Metalogic.tex            # Layer 0 Metalogic component
│   └── 05-Theorems.tex             # Layer 0 Theorems component
├── assets/
│   ├── formatting.sty              # Copied from source
│   ├── notation.sty                # Copied from source (may need extensions)
│   ├── logos-notation.sty          # NEW: Logos-specific macros
│   ├── bib_style.bst               # Copied from source
│   └── glossary.tex                # Copied from source (may need extensions)
├── bibliography/
│   └── LogosReferences.bib         # Bibliography entries
└── build/
    └── LogosReference.pdf          # Compiled output
```

**Main Document Structure** (LogosReference.tex):
```latex
\documentclass[a4paper, 11pt]{article}
\usepackage[top=1.1in, bottom=1.1in]{geometry}
\usepackage[protrusion=true,expansion=true]{microtype}
\usepackage{subfiles}               % NEW: Subfile support
\usepackage{assets/formatting}
\usepackage{assets/notation}
\usepackage{assets/logos-notation}  % NEW: Logos-specific macros

\title{Logos Reference: Bimodal Logic TM}
\author{Benjamin Brast-McKie}
\date{Updated: \today}

\begin{document}
\maketitle
\tableofcontents

\subfile{subfiles/00-Introduction}
\subfile{subfiles/01-Syntax}
\subfile{subfiles/02-Semantics}
\subfile{subfiles/03-ProofSystem}
\subfile{subfiles/04-Metalogic}
\subfile{subfiles/05-Theorems}

\bibliographystyle{assets/bib_style}
\bibliography{bibliography/LogosReferences}
\end{document}
```

**Subfile Template** (e.g., 01-Syntax.tex):
```latex
\documentclass[../LogosReference.tex]{subfiles}
\begin{document}

\section{Syntax}

\subsection{Language Definition}
% Core language BL definition from Bimodal Logic - Syntax

\subsection{Well-Formed Formulas}
% Inductive definition of wfs(BL)

\subsection{Derived Operators}
% Abbreviations: negation, conjunction, disjunction, diamond, some_past, some_future, always, sometimes

\subsection{Scope Conventions}
% Operator precedence and binding

\subsection{Extensions from Propositional Logic}
% What was added: modal box, temporal all_past/all_future

\subsection{Extensions from Modal Logic}
% What was added: temporal operators all_past, all_future

\subsection{Extensions from Temporal Logic}
% What was added: modal operator box

\end{document}
```

**Standardized Section Structure** (per requirement):

Each subfile MUST include:
1. **Syntax Extensions from Previous Layer**: What operators/formulas were added
2. **Semantic Frames and Models Definitions**: Frame structure, model definition, truth conditions
3. **Proof System Extensions from Previous Layer**: What axioms/rules were added
4. **Metalogical Properties**: Soundness, completeness, decidability (established results only)

**Content Guidelines**:
- **Definitions**: Clear, concise, formal
- **No Proofs**: Theorem statements only
- **Minimal Explanation**: Brief motivation, no pedagogical examples
- **Compilation Focus**: Definitions in logical order
- **Cross-References**: Link to Lean source files in footnotes

---

## Detailed Analysis

### Analysis 1: Content Extraction Strategy

**Objective**: Define precise rules for extracting content from source LaTeX.

**Extraction Rules by Section Type**:

**1. Syntax Sections** (INCLUDE):
- Language definition (enumerate with \bf Language)
- Well-formed sentence definition (enumerate with \bf Well-Formed Sentences)
- Abbreviation definitions (enumerate with \bf Abbreviations)
- Scope conventions (if present)
- **Exclude**: Problem sets, regimentation exercises

**Example** (from lines 1124-1140):
```latex
\item[\bf Language:] The \textit{bimodal language} $\BL$ combines...
\item[\bf Well-Formed Sentences:] The set of well-formed sentences $\wfs{\BL}$ is defined inductively:
  \[ \metaA ::= p_i \mid \bot \mid \metaA \rightarrow \metaA \mid \Box \metaA \mid \Past \metaA \mid \Future \metaA \]
\item[\bf Abbreviations:] Derived operators $\Diamond$, $\past$, $\future$, $\always$, and $\sometimes$...
```
**Action**: Extract verbatim, add to 01-Syntax.tex

**2. Semantics Sections** (INCLUDE):
- Frame definitions (enumerate with \bf Frame, \bf Task Frame)
- Model definitions (enumerate with \bf Model, \bf Task Model)
- Truth condition clauses (enumerate with semantic clauses)
- Validity definitions (enumerate with \bf Validity)
- **Exclude**: Problem sets, countermodel exercises

**Example** (from lines 1177-1214):
```latex
\item[\bf Task Frame:] A \textbf{task frame} is a triple $\taskframe = \tuple{\worldstateset, \Tor, \taskrel}$ where:...
\item[\bf World History:] A \textbf{world history} over a frame...
\item[\bf Task Model:] A \textbf{task model} is a tuple...
\item[\bf Truth Conditions:] Given a task model $\taskmodel$, world history $\worldhist$, and time $x$, we define $\taskmodel, \worldhist, x \models \metaA$ inductively:...
\item[\bf Validity:] A formula $\metaA$ is \textbf{valid over task frames}...
```
**Action**: Extract verbatim, add to 02-Semantics.tex

**3. Proof System Sections** (INCLUDE):
- Axiom schemata (enumerate with \bf Axiom Schemata, or individual axiom labels)
- Inference rules (enumerate with \bf Rules, \bf Necessitation Rule)
- Derivability definition (enumerate with \bf Derivable)
- System definitions (enumerate with \bf System Components)
- **Exclude**: Problem sets, proof exercises, proof trees

**Example** (from lines 1238-1263):
```latex
\item[\bf TM System:] The \textit{TM proof system} combines...
\item[\bf System Components:] TM includes:
  \begin{enumerate}
    \item All S5 axioms and rules (MT, M4, MB, MK, MP)
    \item All TL axioms and rules (TL, T4, TA, TD, TK)
    \item \textbf{MF:} $\Box\metaA \rightarrow \Box\Future\metaA$ (modal-future interaction)
    \item \textbf{TF:} $\Box\metaA \rightarrow \Future\Box\metaA$ (temporal-future interaction)
  \end{enumerate}
\item[\bf Perpetuity Principles:] The bimodal interaction axioms yield the following TM-derivable theorems:
  \begin{enumerate}
    \item[\bf P1:] $\Box\metaA \rightarrow \always\metaA$
    \item[\bf P2:] $\sometimes\metaA \rightarrow \Diamond\metaA$
    ...
  \end{enumerate}
```
**Action**: Extract verbatim, add to 03-ProofSystem.tex (axioms) and 05-Theorems.tex (perpetuity)

**4. Metalogic Sections** (INCLUDE):
- Soundness definition (enumerate with \bf Sound)
- Completeness definition (enumerate with \bf Complete)
- Characterization definition (enumerate with \bf Characterization)
- Established results (enumerate with \bf Modal Logics, theorem statements)
- **Exclude**: Problem sets, proof sketches, canonical model construction details

**Example** (from lines 689-721):
```latex
\item[\bf Sound:] The system $\Q$ is \textit{sound} with respect to $\MLmodels[C]$ just in case $\MetaG \MLmodels[C] \metaB$ whenever $\MetaG \Qproves \metaB$.
\item[\bf Complete:] The system $\Q$ is \textit{complete} with respect to $\MLmodels[C]$ just in case $\MetaG \Qproves \metaB$ whenever $\MetaG \MLmodels[C] \metaB$.
\item[\bf Characterization:] The frame constraints $C$ \textit{characterize} the modal proof system $\Q$ just in case $\Q$ is both sound and complete with respect to $\MLmodels[C]$.
\item[\bf Modal Logics:] The modal proof systems are characterized the following sets of frame constraints:
  \begin{itemize}
    \item $K = \varnothing$ characterizes $\K$.
    \item $T = \set{\textsc{ref}}$ characterizes $\T$.
    ...
  \end{itemize}
```
**Action**: Extract verbatim, add to 04-Metalogic.tex

**5. Theorems Sections** (INCLUDE):
- Theorem statements (enumerate with \bf labels or theorem environments)
- Perpetuity principles (enumerate with \bf P1-P6)
- Derived results (theorem statements without proofs)
- **Exclude**: Proofs, proof sketches, derivation trees

**Example** (from lines 1251-1263):
```latex
\item[\bf Perpetuity Principles:] The bimodal interaction axioms yield the following TM-derivable theorems:
  \begin{enumerate}
    \item[\bf P1:] $\Box\metaA \rightarrow \always\metaA$
    \item[\bf P2:] $\sometimes\metaA \rightarrow \Diamond\metaA$
    \item[\bf P3:] $\Box\metaA \rightarrow \Box\always\metaA$
    \item[\bf P4:] $\Diamond\sometimes\metaA \rightarrow \Diamond\metaA$
    \item[\bf P5:] $\Diamond\sometimes\metaA \rightarrow \always\Diamond\metaA$
    \item[\bf P6:] $\sometimes\Box\metaA \rightarrow \Box\always\metaA$
  \end{enumerate}
```
**Action**: Extract verbatim, add to 05-Theorems.tex

**6. Problem Sets** (EXCLUDE):
- All sections with `\section*{\it Problem Set: ...}`
- All enumerate environments within problem set sections
- All proof exercises, regimentation tasks, countermodel construction

**Example** (from lines 1267-1287):
```latex
\section*{\it Problem Set: Derivations}
\begin{enumerate}[leftmargin=1.2in,itemsep=2pt]\small
  \item[\bf Perpetuity Proofs:] Provide formal TM-proofs for the perpetuity principles:
  ...
\end{enumerate}
```
**Action**: Skip entirely, do not include in any subfile

**7. Motivation Sections** (SELECTIVE):
- Brief motivation paragraphs (1-2 paragraphs max)
- Perpetuity intuitions (lines 1099-1123)
- **Exclude**: Extended examples, informal discussions

**Example** (from lines 1099-1123):
```latex
Natural language frequently expresses relationships between temporal and modal concepts. Consider these intuitions:
\begin{enumerate}[leftmargin=1.2in,itemsep=4pt]
  \item[\bf Perpetuity:] ``If something is necessary, then it has always been and will always be true.''...
  \item[\bf Possibility:] ``If something is sometimes true, then it is possibly true.''...
  \item[\bf Interaction:] ``Necessary truths persist through time.''...
\end{enumerate}
These principles cannot be captured by modal logic alone...
```
**Action**: Extract and condense to 2-3 paragraphs, add to 00-Introduction.tex

**Extraction Workflow**:
1. Parse source LaTeX line by line
2. Identify section type by header pattern
3. Apply inclusion/exclusion rules
4. Extract matching content blocks
5. Preserve LaTeX formatting (enumerate, itemize, math mode)
6. Add to appropriate target subfile
7. Add cross-references to Lean source in footnotes

### Analysis 2: Subfile Content Specification

**Objective**: Define precise content for each target subfile.

**00-Introduction.tex**:
- **Purpose**: Overview of Logos TM logic and motivation
- **Content Sources**:
  - Bimodal Logic - Tense and Modality (lines 1099-1123): Perpetuity intuitions
  - Brief description of layer architecture from ARCHITECTURE.md
  - Relationship to Lean implementation
- **Structure**:
  ```latex
  \section{Introduction}
  \subsection{Overview}
  % Brief description of Logos project and TM logic
  \subsection{Perpetuity Intuitions}
  % Extract from lines 1099-1123 (perpetuity, possibility, interaction)
  \subsection{Layer Architecture}
  % Brief description of Layer 0 (Core) components
  \subsection{Relationship to Lean Implementation}
  % How this reference maps to Lean source code
  \subsection{Reading Guide}
  % How to use this reference document
  ```
- **Length**: 2-3 pages
- **Lean Cross-References**: Logos/README.md, Documentation/UserGuide/ARCHITECTURE.md

**01-Syntax.tex**:
- **Purpose**: Define the language and formulas of TM logic
- **Content Sources**:
  - Propositional Logic - Syntax (lines 27-69): Base language, sentence letters
  - Modal Logic - Syntax (lines 428-470): Box operator, diamond abbreviation
  - Tense Logic - Syntax (lines 779-848): Past/Future operators, temporal abbreviations
  - Bimodal Logic - Syntax (lines 1124-1176): Complete BL language
- **Structure**:
  ```latex
  \section{Syntax}
  \subsection{Language Definition}
  % Bimodal language BL = (SL, ⊥, →, □, H, G)
  \subsection{Well-Formed Formulas}
  % Inductive definition: φ ::= p_i | ⊥ | φ → φ | □φ | Hφ | Gφ
  \subsection{Derived Operators}
  % Negation, conjunction, disjunction, diamond, some_past, some_future, always, sometimes
  \subsection{Scope Conventions}
  % Operator precedence and parentheses
  \subsection{Extensions from Propositional Logic}
  % Added: □, H, G operators
  \subsection{Extensions from Modal Logic}
  % Added: H, G temporal operators
  \subsection{Extensions from Temporal Logic}
  % Added: □ modal operator
  ```
- **Length**: 3-4 pages
- **Lean Cross-References**: Logos/Core/Syntax/Formula.lean

**02-Semantics.tex**:
- **Purpose**: Define task frames, models, truth conditions, and validity
- **Content Sources**:
  - Modal Logic - Frames (lines 558-607): Kripke frame structure (background)
  - Modal Logic - Logical Consequence (lines 608-688): Validity definition (background)
  - Tense Logic - Frames (lines 849-906): Temporal frame structure (background)
  - Bimodal Logic - Semantics (lines 1177-1237): Task frames, world histories, truth conditions
- **Structure**:
  ```latex
  \section{Semantics}
  \subsection{Task Frames}
  % Definition: F = (W, T, ·) with nullity and compositionality
  \subsection{World Histories}
  % Definition: τ: X → W with task coherence
  \subsection{Task Models}
  % Definition: M = (W, T, ·, ⟦·⟧) with valuation
  \subsection{Truth Conditions}
  % Inductive definition: M, τ, x ⊨ φ
  \subsection{Validity}
  % Definition: ⊨_TM φ (valid over all task models)
  \subsection{Extensions from Propositional Logic}
  % Added: Task frame structure, world histories
  \subsection{Extensions from Modal Logic}
  % Added: World histories, task relation
  \subsection{Extensions from Temporal Logic}
  % Added: Modal accessibility via task relation
  ```
- **Length**: 4-5 pages
- **Lean Cross-References**: Logos/Core/Semantics/ (all files)

**03-ProofSystem.tex**:
- **Purpose**: Define axioms, inference rules, and derivability
- **Content Sources**:
  - Propositional Logic - Hilbert System (lines 323-360): K, S axioms, MP rule
  - Modal Logic - Axiomatic Systems (lines 471-557): Modal axioms (T, 4, B, 5, K)
  - Tense Logic - Axiomatic System (lines 965-1026): Temporal axioms (TK, T4, TA, TL)
  - Bimodal Logic - Axiomatic System (lines 1238-1287): TM system, MF, TF axioms
- **Structure**:
  ```latex
  \section{Proof System}
  \subsection{Propositional Axioms}
  % K, S, EFQ, Peirce
  \subsection{Modal Axioms}
  % MT, M4, MB, M5, MK
  \subsection{Temporal Axioms}
  % TK, T4, TA, TL
  \subsection{Modal-Temporal Interaction Axioms}
  % MF, TF
  \subsection{Inference Rules}
  % Modus Ponens, Necessitation, Temporal Necessitation
  \subsection{Derivability}
  % Definition: Γ ⊢_TM φ
  \subsection{Extensions from Propositional Logic}
  % Added: Modal and temporal axioms/rules
  \subsection{Extensions from Modal Logic}
  % Added: Temporal axioms/rules, MF, TF
  \subsection{Extensions from Temporal Logic}
  % Added: Modal axioms/rules, MF, TF
  ```
- **Length**: 4-5 pages
- **Lean Cross-References**: Logos/Core/ProofSystem/Axioms.lean, Derivation.lean

**04-Metalogic.tex**:
- **Purpose**: State soundness, completeness, and characterization results
- **Content Sources**:
  - Modal Logic - Metalogic (lines 689-778): Soundness, completeness, characterization definitions
  - Bimodal Logic - Metatheory (lines 1288-1309): TM-specific results (commented out, incomplete)
  - Logos/Core/Metalogic/: Soundness.lean, Completeness.lean, DeductionTheorem.lean
- **Structure**:
  ```latex
  \section{Metalogic}
  \subsection{Soundness}
  % Definition: If Γ ⊢_TM φ then Γ ⊨_TM φ
  % Status: PROVEN in Lean (Logos/Core/Metalogic/Soundness.lean)
  \subsection{Completeness}
  % Definition: If Γ ⊨_TM φ then Γ ⊢_TM φ
  % Status: Infrastructure only (canonical model construction)
  \subsection{Deduction Theorem}
  % Theorem: Γ, φ ⊢ ψ iff Γ ⊢ φ → ψ
  % Status: PROVEN in Lean (Logos/Core/Metalogic/DeductionTheorem.lean)
  \subsection{Decidability}
  % Status: Not established
  \subsection{Characterization}
  % TM system characterized by task frame constraints
  \subsection{Established Properties}
  % Summary of proven metalogical results
  ```
- **Length**: 2-3 pages
- **Lean Cross-References**: Logos/Core/Metalogic/ (all files)

**05-Theorems.tex**:
- **Purpose**: State key theorems and perpetuity principles
- **Content Sources**:
  - Bimodal Logic - Axiomatic System (lines 1251-1263): Perpetuity principles P1-P6
  - Logos/Core/Theorems/: Propositional.lean, ModalS4.lean, ModalS5.lean, Perpetuity/
- **Structure**:
  ```latex
  \section{Theorems}
  \subsection{Propositional Theorems}
  % Key propositional tautologies (from Propositional.lean)
  \subsection{Modal S4 Theorems}
  % S4-specific results (from ModalS4.lean)
  \subsection{Modal S5 Theorems}
  % S5-specific results (from ModalS5.lean)
  \subsection{Perpetuity Principles}
  % P1-P6 with formal statements
  \subsubsection{P1: Necessity Implies Always}
  % □φ → △φ (PROVEN)
  \subsubsection{P2: Sometimes Implies Possibility}
  % ▽φ → ◇φ (PROVEN)
  \subsubsection{P3: Necessity of Perpetuity}
  % □φ → □△φ (PROVEN)
  \subsubsection{P4: Possibility of Occurrence}
  % ◇▽φ → ◇φ (PROVEN)
  \subsubsection{P5: Persistent Possibility}
  % ◇▽φ → △◇φ (PROVEN)
  \subsubsection{P6: Occurrent Necessity is Perpetual}
  % ▽□φ → □△φ (PROVEN)
  \subsection{Derived Results}
  % Other key theorems from Theorems/ directory
  ```
- **Length**: 3-4 pages
- **Lean Cross-References**: Logos/Core/Theorems/ (all files)

**Content Extraction Summary**:
- **Total estimated length**: 18-23 pages (excluding introduction)
- **Source lines extracted**: ~600 lines (41% of source content)
- **Source lines excluded**: ~450 lines (31% problem sets + 10% proofs)
- **New content added**: ~200 lines (14% for standardized sections)

### Analysis 3: LaTeX Macro Extensions

**Objective**: Identify required LaTeX macros for Logos-specific notation.

**Existing Macros** (from notation.sty):
- `\Box`, `\Diamond`: Modal operators
- `\Past`, `\Future`: Temporal operators (universal)
- `\past`, `\future`: Temporal operators (existential)
- `\always`, `\sometimes`: Eternal operators
- `\PL`, `\ML`, `\TL`, `\BL`: Language names
- `\wfs{\cdot}`: Well-formed sentences
- `\PLmodels`, `\MLmodels`: Semantic consequence
- `\Kproves`, `\TMproves`: Derivability in proof systems
- `\metaA`, `\metaB`, `\metaC`: Metavariables
- `\corner{\cdot}`: Corner quotes

**Required New Macros** (for logos-notation.sty):

**1. Task Frame Notation**:
```latex
% Task frame components
\newcommand{\taskframe}{\mathcal{F}}                    % Task frame F
\newcommand{\worldstateset}{W}                          % World states
\newcommand{\Tor}{\mathcal{T}}                          % Time group
\newcommand{\taskrel}{\cdot}                            % Task relation
\newcommand{\worldhist}{\tau}                           % World history
\newcommand{\worldhistset}{\mathcal{H}}                 % Set of world histories

% Task frame notation
\newcommand{\taskframetriple}[3]{\langle #1, #2, #3 \rangle}  % (W, T, ·)
\newcommand{\taskrelation}[3]{#1 \mathrel{\cdot_{#2}} #3}     % w ·_x u
```

**2. Task Model Notation**:
```latex
% Task model
\newcommand{\taskmodel}{\mathcal{M}}                    % Task model M
\newcommand{\taskmodelquad}[4]{\langle #1, #2, #3, #4 \rangle}  % (W, T, ·, ⟦·⟧)
\newcommand{\valuation}[1]{\llbracket #1 \rrbracket}   % ⟦p_i⟧
```

**3. Truth and Validity Notation**:
```latex
% Truth at world history and time
\newcommand{\truthat}[3]{#1, #2, #3 \models}            % M, τ, x ⊨ φ
\newcommand{\ntruthsat}[3]{#1, #2, #3 \not\models}      % M, τ, x ⊭ φ

% Validity over task frames
\newcommand{\TMmodels}{\models_{\textsc{tm}}}           % ⊨_TM
\newcommand{\TMproves}{\vdash_{\textsc{tm}}}            % ⊢_TM
```

**4. Lean Cross-Reference Notation**:
```latex
% Lean source references
\newcommand{\leansrc}[2]{\footnote{Lean: \texttt{#1.#2}}}  % Footnote to Lean file
\newcommand{\leandef}[2]{\texttt{#1.#2}}                    % Inline Lean reference
```

**5. Axiom Notation**:
```latex
% Axiom labels
\newcommand{\axiomK}{\textbf{K}}
\newcommand{\axiomS}{\textbf{S}}
\newcommand{\axiomEFQ}{\textbf{EFQ}}
\newcommand{\axiomPeirce}{\textbf{Peirce}}
\newcommand{\axiomMT}{\textbf{MT}}
\newcommand{\axiomMfour}{\textbf{M4}}
\newcommand{\axiomMB}{\textbf{MB}}
\newcommand{\axiomMK}{\textbf{MK}}
\newcommand{\axiomTK}{\textbf{TK}}
\newcommand{\axiomTfour}{\textbf{T4}}
\newcommand{\axiomTA}{\textbf{TA}}
\newcommand{\axiomTL}{\textbf{TL}}
\newcommand{\axiomMF}{\textbf{MF}}
\newcommand{\axiomTF}{\textbf{TF}}
```

**6. Perpetuity Principle Notation**:
```latex
% Perpetuity principles
\newcommand{\Pone}{\textbf{P1}}
\newcommand{\Ptwo}{\textbf{P2}}
\newcommand{\Pthree}{\textbf{P3}}
\newcommand{\Pfour}{\textbf{P4}}
\newcommand{\Pfive}{\textbf{P5}}
\newcommand{\Psix}{\textbf{P6}}
```

**7. Temporal Notation Extensions**:
```latex
% Temporal operators (if not in notation.sty)
\newcommand{\allpast}{\mathsf{H}}                       % H (all past)
\newcommand{\allfuture}{\mathsf{G}}                     % G (all future)
\newcommand{\somepast}{\mathsf{P}}                      % P (some past)
\newcommand{\somefuture}{\mathsf{F}}                    % F (some future)
```

**Macro File Structure** (logos-notation.sty):
```latex
\NeedsTeXFormat{LaTeX2e}
\ProvidesPackage{logos-notation}[2026/01/08 Logos TM Logic Notation]

% Require base notation package
\RequirePackage{assets/notation}

% Task Frame Notation
% ... (macros from above)

% Task Model Notation
% ... (macros from above)

% Truth and Validity Notation
% ... (macros from above)

% Lean Cross-Reference Notation
% ... (macros from above)

% Axiom Notation
% ... (macros from above)

% Perpetuity Principle Notation
% ... (macros from above)

% Temporal Notation Extensions
% ... (macros from above)

\endinput
```

**Verification Strategy**:
1. Test each macro in isolation
2. Verify compatibility with notation.sty
3. Check rendering in compiled PDF
4. Ensure consistent spacing and formatting
5. Validate cross-references to Lean source

---

## Decisions

### Decision 1: Subfile Architecture

**Decision**: Use LaTeX subfiles package for modular document structure.

**Rationale**:
1. **Modularity**: Each Logos component (Syntax, Semantics, ProofSystem, Metalogic, Theorems) in separate file
2. **Independent Compilation**: Each subfile can be compiled standalone for testing
3. **Maintainability**: Easy to update individual components without touching others
4. **Scalability**: Future layers (1-3) can be added as new subfiles
5. **Standard Practice**: Subfiles package is widely used and well-documented

**Alternatives Considered**:
- **Single File**: Rejected due to poor maintainability (1452+ lines)
- **Input/Include**: Rejected because subfiles can't be compiled independently
- **Standalone Documents**: Rejected due to duplication of preamble and formatting

**Implementation**:
```latex
% Main document
\usepackage{subfiles}
\subfile{subfiles/01-Syntax}

% Subfile
\documentclass[../LogosReference.tex]{subfiles}
\begin{document}
% Content
\end{document}
```

### Decision 2: Exclude Fitch Natural Deduction

**Decision**: Exclude all Fitch-style natural deduction content from target documentation.

**Rationale**:
1. **Not in Logos**: Logos uses Hilbert-style axiomatic system, not natural deduction
2. **Proof Exclusion**: Requirement specifies "no proofs", Fitch proofs are excluded
3. **Style File Dependency**: Can exclude proof_styles.sty, reducing dependencies
4. **Pedagogical Focus**: Fitch system is pedagogical tool, not part of TM logic definition

**Content Excluded**:
- Lines 117-270: Propositional Logic - Fitch System (entire section)
- Lines 271-322: Problem Set - Regimentation and Deduction
- All fitch environments in source document

**Impact**:
- Reduces source content by ~150 lines (10%)
- Simplifies LaTeX dependencies
- Aligns with Logos implementation (Hilbert-style only)

### Decision 3: Standardized Section Structure

**Decision**: Add standardized sections to each subfile as specified in requirements.

**Rationale**:
1. **Requirement Compliance**: Task explicitly requires standardized sections
2. **Layer Clarity**: Makes extensions from previous layers explicit
3. **Pedagogical Value**: Helps readers understand incremental complexity
4. **Consistency**: Uniform structure across all subfiles

**Standardized Sections** (per subfile):
1. **Syntax Extensions from Previous Layer**: What operators/formulas were added
2. **Semantic Frames and Models Definitions**: Frame structure, model definition, truth conditions
3. **Proof System Extensions from Previous Layer**: What axioms/rules were added
4. **Metalogical Properties**: Soundness, completeness, decidability (established results only)

**Implementation Example** (01-Syntax.tex):
```latex
\subsection{Extensions from Propositional Logic}
The bimodal language $\BL$ extends propositional logic $\PL$ with three new operators:
\begin{itemize}
  \item $\Box$ (box): Modal necessity operator
  \item $\Past$ (H): Universal past temporal operator
  \item $\Future$ (G): Universal future temporal operator
\end{itemize}

\subsection{Extensions from Modal Logic}
The bimodal language $\BL$ extends modal logic $\ML$ with two temporal operators:
\begin{itemize}
  \item $\Past$ (H): Universal past temporal operator
  \item $\Future$ (G): Universal future temporal operator
\end{itemize}

\subsection{Extensions from Temporal Logic}
The bimodal language $\BL$ extends temporal logic $\TL$ with one modal operator:
\begin{itemize}
  \item $\Box$ (box): Modal necessity operator
\end{itemize}
```

**Content Sources**:
- Extensions: Inferred from source LaTeX and Logos architecture
- Semantic definitions: Extracted from Bimodal Logic - Semantics (lines 1177-1237)
- Proof system extensions: Extracted from Bimodal Logic - Axiomatic System (lines 1238-1287)
- Metalogical properties: Extracted from Modal Logic - Metalogic (lines 689-778) and Logos/Core/Metalogic/

### Decision 4: Lean Cross-References

**Decision**: Add footnote cross-references to Lean source files for each major definition.

**Rationale**:
1. **Requirement**: Documentation should "serve as reference for learning Logos system"
2. **Traceability**: Readers can find corresponding Lean implementation
3. **Verification**: Enables checking LaTeX definitions against Lean source
4. **Learning Path**: Bridges gap between LaTeX reference and Lean code

**Implementation**:
```latex
\item[\bf Task Frame:] A \textbf{task frame} is a triple $\taskframe = \tuple{\worldstateset, \Tor, \taskrel}$ where:...\leansrc{Logos.Core.Semantics}{TaskFrame}
```

**Cross-Reference Format**:
- Footnote: "Lean: `Logos.Core.Semantics.TaskFrame`"
- Links to specific Lean file and definition
- Placed at end of definition paragraph

**Coverage**:
- All major definitions (language, frame, model, axioms, theorems)
- Not for every abbreviation or minor notation
- Approximately 20-30 cross-references total

### Decision 5: Minimal Explanation Policy

**Decision**: Provide minimal explanation, focusing on formal definitions.

**Rationale**:
1. **Requirement**: "Provide minimal explanation"
2. **Reference Focus**: Document is a reference, not a textbook
3. **Conciseness**: Avoid pedagogical examples and extended discussions
4. **Readability**: Clear definitions are more valuable than verbose explanations

**Content Guidelines**:
- **Include**: Formal definitions, axiom statements, theorem statements
- **Include**: Brief motivation (1-2 sentences) for major concepts
- **Include**: Notation conventions and scope rules
- **Exclude**: Extended examples, informal discussions, pedagogical exercises
- **Exclude**: Proofs, proof sketches, derivation trees
- **Exclude**: Historical notes, philosophical discussions

**Example** (Good - Minimal):
```latex
\item[\bf Task Frame:] A \textbf{task frame} is a triple $\taskframe = \tuple{\worldstateset, \Tor, \taskrel}$ where $\worldstateset$ is a set of world states, $\Tor$ is a totally ordered abelian group of times, and $\taskrel$ is a task relation satisfying nullity and compositionality.
```

**Example** (Bad - Too Verbose):
```latex
\item[\bf Task Frame:] A \textbf{task frame} provides the semantic foundation for TM logic. Intuitively, a task frame represents the space of possible world states and the tasks that can transform one state into another over time. The task relation captures the idea that executing a task of a certain duration from one world state can result in another world state. This generalizes both Kripke frames (modal logic) and temporal frames (tense logic) by parameterizing the accessibility relation with time durations. The nullity constraint ensures that zero-duration tasks are identity transformations, while compositionality ensures that sequential task execution corresponds to time addition. This structure enables reasoning about both modal necessity (what holds across all possible worlds) and temporal persistence (what holds across all times).
```

**Length Target**:
- Definitions: 2-4 sentences
- Motivation: 1-2 sentences
- Notation: 1 sentence
- Total per subfile: 3-5 pages

---

## Recommendations

### Recommendation 1: Implementation Phases

**Recommendation**: Implement documentation generation in 4 phases.

**Phase 1: Setup and Infrastructure** (4-6 hours):
1. Create target directory structure: Documentation/LaTeX/
2. Copy source assets: formatting.sty, notation.sty, bib_style.bst, glossary.tex
3. Create logos-notation.sty with Logos-specific macros
4. Create main document LogosReference.tex with subfile structure
5. Test compilation with empty subfiles

**Deliverables**:
- Directory structure created
- Style files copied and tested
- Main document compiles successfully
- Subfile architecture validated

**Phase 2: Content Extraction** (8-12 hours):
1. Extract propositional logic content (lines 27-69, 323-360)
2. Extract modal logic content (lines 428-778)
3. Extract tense logic content (lines 779-1026)
4. Extract bimodal logic content (lines 1099-1436)
5. Organize extracted content by target subfile
6. Remove problem sets and proofs

**Deliverables**:
- Extracted content organized by subfile
- Problem sets and proofs removed
- Content validated against inclusion rules

**Phase 3: Subfile Generation** (12-16 hours):
1. Generate 00-Introduction.tex (motivation, overview)
2. Generate 01-Syntax.tex (language, formulas, abbreviations)
3. Generate 02-Semantics.tex (frames, models, truth, validity)
4. Generate 03-ProofSystem.tex (axioms, rules, derivability)
5. Generate 04-Metalogic.tex (soundness, completeness, characterization)
6. Generate 05-Theorems.tex (perpetuity principles, key theorems)
7. Add standardized sections to each subfile
8. Add Lean cross-references

**Deliverables**:
- 6 subfiles generated with content
- Standardized sections added
- Lean cross-references inserted
- Each subfile compiles independently

**Phase 4: Review and Refinement** (4-6 hours):
1. Compile full document and check formatting
2. Verify all cross-references
3. Check mathematical notation consistency
4. Proofread definitions and theorem statements
5. Validate against requirements
6. Generate final PDF

**Deliverables**:
- Full document compiles successfully
- All cross-references validated
- Formatting consistent throughout
- Requirements checklist completed
- Final PDF generated

**Total Estimated Effort**: 28-40 hours (2-3 days)

### Recommendation 2: Automation Strategy

**Recommendation**: Use semi-automated extraction with manual review.

**Rationale**:
1. **Complexity**: LaTeX structure is complex, full automation error-prone
2. **Quality**: Manual review ensures mathematical correctness
3. **Customization**: Standardized sections require manual authoring
4. **Efficiency**: Semi-automation faster than full manual transcription

**Automation Approach**:
1. **Automated Extraction**:
   - Use sed/awk to extract sections by line ranges
   - Use grep to identify section headers and boundaries
   - Use regex to remove problem set sections
   - Generate initial subfile content automatically

2. **Manual Review**:
   - Verify mathematical notation correctness
   - Add standardized sections manually
   - Insert Lean cross-references manually
   - Adjust formatting and spacing

3. **Validation**:
   - Compile each subfile independently
   - Check for LaTeX errors
   - Verify cross-references
   - Proofread definitions

**Tools**:
- **sed**: Extract line ranges from source
- **awk**: Parse section headers and boundaries
- **grep**: Identify problem sets and proofs
- **perl**: Complex regex transformations
- **latexmk**: Automated compilation and error checking

**Example Script** (extract-syntax.sh):
```bash
#!/bin/bash
# Extract syntax content from source LaTeX

SOURCE="/home/benjamin/Projects/Philosophy/Teaching/LogicNotes/LogicNotes.tex"
TARGET="Documentation/LaTeX/subfiles/01-Syntax.tex"

# Extract bimodal syntax section (lines 1124-1140)
sed -n '1124,1140p' "$SOURCE" > "$TARGET.tmp"

# Remove problem set sections
sed -i '/\\section\*{\\it Problem Set/,/^$/d' "$TARGET.tmp"

# Add subfile header
cat > "$TARGET" <<EOF
\documentclass[../LogosReference.tex]{subfiles}
\begin{document}

\section{Syntax}

EOF

# Append extracted content
cat "$TARGET.tmp" >> "$TARGET"

# Add standardized sections (manual)
cat >> "$TARGET" <<EOF

\subsection{Extensions from Propositional Logic}
% TODO: Add manual content

\subsection{Extensions from Modal Logic}
% TODO: Add manual content

\subsection{Extensions from Temporal Logic}
% TODO: Add manual content

\end{document}
EOF

# Cleanup
rm "$TARGET.tmp"
```

### Recommendation 3: Quality Assurance Checklist

**Recommendation**: Use comprehensive checklist to validate final documentation.

**Checklist**:

**Content Completeness**:
- [ ] All syntax definitions included (language, wfs, abbreviations)
- [ ] All semantic definitions included (frames, models, truth, validity)
- [ ] All proof system definitions included (axioms, rules, derivability)
- [ ] All metalogical definitions included (soundness, completeness, characterization)
- [ ] All theorem statements included (perpetuity principles P1-P6)
- [ ] All problem sets excluded
- [ ] All proofs excluded
- [ ] All Fitch natural deduction content excluded

**Standardized Sections**:
- [ ] 01-Syntax.tex has "Extensions from Previous Layer" sections
- [ ] 02-Semantics.tex has "Semantic Frames and Models Definitions" section
- [ ] 03-ProofSystem.tex has "Proof System Extensions from Previous Layer" sections
- [ ] 04-Metalogic.tex has "Metalogical Properties" section
- [ ] 05-Theorems.tex has perpetuity principles P1-P6

**Formatting**:
- [ ] All section headers use `\section*{\sc Title}` format
- [ ] All definitions use `\begin{enumerate}[leftmargin=1.2in]` format
- [ ] All definition labels use `\item[\bf Label:]` format
- [ ] All abbreviations use `\coloneq` notation
- [ ] All mathematical notation consistent with source
- [ ] All metavariables use `\metaA`, `\metaB`, `\metaC`

**Cross-References**:
- [ ] All major definitions have Lean cross-references
- [ ] All cross-references use `\leansrc{Module}{Definition}` format
- [ ] All cross-references point to correct Lean files
- [ ] All cross-references render correctly in PDF

**Compilation**:
- [ ] Main document compiles without errors
- [ ] Each subfile compiles independently without errors
- [ ] All style files load correctly
- [ ] All macros defined and used correctly
- [ ] PDF renders correctly with proper formatting

**Requirements Validation**:
- [ ] Documentation mirrors Logos layer structure
- [ ] Subfile created for each Logos layer component
- [ ] Same formatting standards as original maintained
- [ ] Problem sets excluded
- [ ] Standardized sections included for each layer
- [ ] Definitions compiled clearly and concisely without proofs
- [ ] Minimal explanation provided
- [ ] Serves as readable LaTeX reference without Lean code

**Total Checklist Items**: 38

### Recommendation 4: Future Extensions

**Recommendation**: Design structure to accommodate future Logos layers (1-3).

**Rationale**:
1. **Scalability**: Logos roadmap includes 3 future extension layers
2. **Consistency**: Future layers should follow same structure as Layer 0
3. **Modularity**: Subfile architecture supports easy addition of new layers

**Future Subfiles** (when implemented):

**Layer 1 (Explanatory Extension)**:
- 06-Explanatory-Syntax.tex: Counterfactual, constitutive, causal operators
- 07-Explanatory-Semantics.tex: Selection functions, grounding relations
- 08-Explanatory-ProofSystem.tex: Explanatory axioms and rules
- 09-Explanatory-Metalogic.tex: Soundness and completeness for Layer 1
- 10-Explanatory-Theorems.tex: Key explanatory theorems

**Layer 2 (Epistemic Extension)**:
- 11-Epistemic-Syntax.tex: Belief, probability, knowledge operators
- 12-Epistemic-Semantics.tex: Information states, doxastic alternatives
- 13-Epistemic-ProofSystem.tex: Epistemic axioms and rules
- 14-Epistemic-Metalogic.tex: Soundness and completeness for Layer 2
- 15-Epistemic-Theorems.tex: Key epistemic theorems

**Layer 3 (Normative Extension)**:
- 16-Normative-Syntax.tex: Deontic, preference, ought operators
- 17-Normative-Semantics.tex: Ideality orderings, deontic accessibility
- 18-Normative-ProofSystem.tex: Normative axioms and rules
- 19-Normative-Metalogic.tex: Soundness and completeness for Layer 3
- 20-Normative-Theorems.tex: Key normative theorems

**Main Document Update**:
```latex
% Layer 0 (Core)
\subfile{subfiles/00-Introduction}
\subfile{subfiles/01-Syntax}
\subfile{subfiles/02-Semantics}
\subfile{subfiles/03-ProofSystem}
\subfile{subfiles/04-Metalogic}
\subfile{subfiles/05-Theorems}

% Layer 1 (Explanatory) - Future
% \subfile{subfiles/06-Explanatory-Syntax}
% \subfile{subfiles/07-Explanatory-Semantics}
% ...

% Layer 2 (Epistemic) - Future
% \subfile{subfiles/11-Epistemic-Syntax}
% ...

% Layer 3 (Normative) - Future
% \subfile{subfiles/16-Normative-Syntax}
% ...
```

**Timeline**:
- Layer 1: 3-6 months post Core MVP (per Explanatory/README.md)
- Layer 2: 3-6 months post Layer 1 (per Epistemic/README.md)
- Layer 3: 3-6 months post Layer 2 (per Normative/README.md)

---

## Risks & Mitigations

### Risk 1: LaTeX Compilation Errors

**Risk**: Generated LaTeX may have syntax errors or undefined macros.

**Likelihood**: Medium

**Impact**: High (blocks PDF generation)

**Mitigation**:
1. **Incremental Compilation**: Compile each subfile independently during generation
2. **Macro Testing**: Test all new macros in logos-notation.sty before use
3. **Validation Script**: Automated script to check for common LaTeX errors
4. **Fallback**: Keep source LaTeX as reference for correct syntax

**Validation Script** (validate-latex.sh):
```bash
#!/bin/bash
# Validate LaTeX syntax

for file in Documentation/LaTeX/subfiles/*.tex; do
  echo "Validating $file..."
  pdflatex -interaction=nonstopmode "$file" > /dev/null 2>&1
  if [ $? -ne 0 ]; then
    echo "ERROR: $file failed to compile"
    exit 1
  fi
done

echo "All subfiles validated successfully"
```

### Risk 2: Mathematical Notation Inconsistency

**Risk**: Extracted content may have inconsistent notation or undefined symbols.

**Likelihood**: Medium

**Impact**: Medium (confusing to readers)

**Mitigation**:
1. **Notation Audit**: Review all mathematical notation in extracted content
2. **Macro Standardization**: Define all symbols in logos-notation.sty
3. **Cross-Reference Check**: Verify notation matches Lean source
4. **Glossary**: Maintain glossary of all notation used

**Notation Checklist**:
- [ ] All modal operators defined (□, ◇)
- [ ] All temporal operators defined (H, G, P, F, △, ▽)
- [ ] All propositional operators defined (¬, ∧, ∨, →, ↔)
- [ ] All semantic notation defined (⊨, ⊨_TM, ⊢, ⊢_TM)
- [ ] All frame notation defined (F, W, T, ·, τ, H_F)
- [ ] All model notation defined (M, ⟦·⟧)

### Risk 3: Content Omission or Duplication

**Risk**: Important definitions may be omitted or duplicated across subfiles.

**Likelihood**: Low

**Impact**: Medium (incomplete or redundant documentation)

**Mitigation**:
1. **Content Mapping**: Maintain explicit mapping of source lines to target subfiles
2. **Completeness Check**: Verify all required definitions included
3. **Duplication Check**: Ensure no content appears in multiple subfiles
4. **Review**: Manual review of all subfiles for completeness

**Content Mapping Table**:
| Definition | Source Lines | Target Subfile | Status |
|------------|--------------|----------------|--------|
| Language BL | 1124-1130 | 01-Syntax.tex | [ ] |
| Well-formed formulas | 1131-1135 | 01-Syntax.tex | [ ] |
| Abbreviations | 1136-1140 | 01-Syntax.tex | [ ] |
| Task frame | 1177-1185 | 02-Semantics.tex | [ ] |
| World history | 1186-1195 | 02-Semantics.tex | [ ] |
| Task model | 1196-1200 | 02-Semantics.tex | [ ] |
| Truth conditions | 1201-1210 | 02-Semantics.tex | [ ] |
| Validity | 1211-1214 | 02-Semantics.tex | [ ] |
| TM system | 1238-1250 | 03-ProofSystem.tex | [ ] |
| Perpetuity principles | 1251-1263 | 05-Theorems.tex | [ ] |
| Soundness | 689-692 | 04-Metalogic.tex | [ ] |
| Completeness | 693-696 | 04-Metalogic.tex | [ ] |

### Risk 4: Lean Cross-Reference Errors

**Risk**: Cross-references to Lean source may be incorrect or broken.

**Likelihood**: Low

**Impact**: Low (doesn't affect LaTeX compilation, but misleading)

**Mitigation**:
1. **Automated Verification**: Script to check all Lean file paths exist
2. **Manual Review**: Verify each cross-reference points to correct definition
3. **Documentation**: Document cross-reference format in README
4. **Testing**: Test cross-references by opening Lean files

**Verification Script** (verify-lean-refs.sh):
```bash
#!/bin/bash
# Verify Lean cross-references

LEAN_ROOT="/home/benjamin/Projects/ProofChecker"

grep -r "\\leansrc{" Documentation/LaTeX/subfiles/*.tex | while read -r line; do
  # Extract module and definition
  module=$(echo "$line" | sed -n 's/.*\\leansrc{\([^}]*\)}.*/\1/p' | cut -d'.' -f1-4)
  file="${module//./\/}.lean"
  
  if [ ! -f "$LEAN_ROOT/$file" ]; then
    echo "ERROR: Lean file not found: $file"
    exit 1
  fi
done

echo "All Lean cross-references verified"
```

---

## Appendix: Sources and Citations

### Primary Sources

1. **Source LaTeX Document**:
   - Path: /home/benjamin/Projects/Philosophy/Teaching/LogicNotes/LogicNotes.tex
   - Size: 1452 lines
   - Author: Benjamin Brast-McKie
   - Content: Comprehensive logic course from propositional to bimodal logic

2. **Logos Codebase**:
   - Path: /home/benjamin/Projects/ProofChecker/Logos/
   - Language: Lean 4
   - Structure: 5-layer architecture (Core + 3 extensions + Examples)
   - Status: Layer 0 (Core) production-ready, Layers 1-3 planned

3. **Architecture Documentation**:
   - Path: Documentation/UserGuide/ARCHITECTURE.md
   - Content: TM logic specification, layer architecture, DSL syntax
   - Lines: 150+ (excerpt read)

4. **Implementation Status**:
   - Path: Documentation/ProjectInfo/IMPLEMENTATION_STATUS.md
   - Content: Module-by-module status, sorry counts, test coverage
   - Status: Layer 0 MVP complete, all 6 perpetuity principles proven

### Secondary Sources

5. **Logos README**:
   - Path: Logos/README.md
   - Content: Module overview, quick reference, building instructions
   - Lines: 184 total

6. **Perpetuity README**:
   - Path: Logos/Core/Theorems/Perpetuity/README.md
   - Content: P1-P6 perpetuity principle proofs, helper lemmas
   - Lines: 59 total

7. **Layer Extension READMEs**:
   - Epistemic: Logos/Epistemic/README.md (30 lines)
   - Explanatory: Logos/Explanatory/README.md (29 lines)
   - Normative: Logos/Normative/README.md (29 lines)
   - Status: All planned for future development

### Lean Source Files

8. **Syntax Module**:
   - Formula.lean: Inductive formula type (6 constructors)
   - Context.lean: Proof context lists

9. **ProofSystem Module**:
   - Axioms.lean: 14 axiom schemata (4 prop + 4 modal + 4 temporal + 2 interaction)
   - Derivation.lean: DerivationTree inductive type (7 inference rules)

10. **Semantics Module**:
    - TaskFrame.lean: Task frame structure (WorldState, time group, task relation)
    - TaskModel.lean: Models with valuation
    - Truth.lean: Truth evaluation at world history and time
    - Validity.lean: Semantic consequence
    - WorldHistory.lean: World history functions

11. **Metalogic Module**:
    - Soundness.lean: Soundness theorem (derivability → validity)
    - SoundnessLemmas.lean: Helper lemmas
    - Completeness.lean: Canonical model construction (infrastructure)
    - DeductionTheorem.lean: Deduction theorem for TM logic

12. **Theorems Module**:
    - Perpetuity/Principles.lean: P1-P5 proofs
    - Perpetuity/Bridge.lean: P6 proof and bridge lemmas
    - Perpetuity/Helpers.lean: Helper lemmas
    - Propositional.lean: Propositional tautologies
    - ModalS4.lean: S4 modal theorems
    - ModalS5.lean: S5 modal theorems

### LaTeX Style Files

13. **formatting.sty**: Bibliography, graphics, color support (6039 bytes)
14. **notation.sty**: Logic notation, operator definitions (19573 bytes)
15. **proof_styles.sty**: Fitch proof environments (20798 bytes) [EXCLUDE]
16. **bib_style.bst**: Bibliography style (30890 bytes)
17. **glossary.tex**: Logic term glossary (4251 bytes)

### External References

18. **JPL Paper**: "The Perpetuity Calculus of Agency" (referenced in TaskFrame.lean)
19. **Subfiles Package**: LaTeX package for modular documents (CTAN)
20. **Lean 4 Documentation**: https://lean-lang.org/lean4/doc/

---

## Appendix: Detailed Content Mapping

### Propositional Logic Content

**Source Lines 27-69** (Propositional Logic - Syntax and Semantics):
- Target: 01-Syntax.tex (background), 02-Semantics.tex (background)
- Content: Canonical names, language PL, sentence letters, strings, schematic variables, corner quotes, well-formed sentences, abbreviations, models, semantics, logical consequence, logical equivalence, logical truth
- Action: Extract definitions for background context, not primary focus

**Source Lines 323-360** (Propositional Logic - Hilbert System):
- Target: 03-ProofSystem.tex
- Content: Axiom schemata K and S, modus ponens rule
- Action: Extract axiom definitions, include in propositional axioms section

### Modal Logic Content

**Source Lines 428-470** (Modal Logic - Syntax):
- Target: 01-Syntax.tex
- Content: Language ML, well-formed sentences with box operator, abbreviations (diamond, strict conditional)
- Action: Extract as background for bimodal syntax

**Source Lines 471-557** (Modal Logic - Axiomatic Systems):
- Target: 03-ProofSystem.tex
- Content: Axiom schemata K, D, T, B, 4, 5; necessitation rule; modal proof systems K, D, T, B, S4, S5
- Action: Extract modal axioms, include in modal axioms section

**Source Lines 558-607** (Modal Logic - Frames):
- Target: 02-Semantics.tex
- Content: Kripke frames, accessibility relation, frame constraints (reflexive, symmetric, transitive, etc.)
- Action: Extract as background for task frame semantics

**Source Lines 608-688** (Modal Logic - Logical Consequence):
- Target: 02-Semantics.tex
- Content: Truth at world, validity, logical consequence, logical equivalence
- Action: Extract validity definition as background

**Source Lines 689-778** (Modal Logic - Metalogic):
- Target: 04-Metalogic.tex
- Content: Soundness, completeness, characterization definitions; modal logic characterization results
- Action: Extract definitions, adapt for TM logic

### Temporal Logic Content

**Source Lines 779-848** (Tense Logic - Syntax):
- Target: 01-Syntax.tex
- Content: Language TL, well-formed sentences with Past and Future operators, abbreviations (past, future, always, sometimes)
- Action: Extract as background for bimodal syntax

**Source Lines 849-906** (Tense Logic - Frames):
- Target: 02-Semantics.tex
- Content: Temporal frames, earlier-than relation, frame constraints (infinite future/past, irreflexive, asymmetric, transitive, linear, density, discrete)
- Action: Extract as background for task frame semantics

**Source Lines 907-964** (Tense Logic - Logical Consequence):
- Target: 02-Semantics.tex
- Content: Truth at time, validity over temporal frames
- Action: Extract validity definition as background

**Source Lines 965-1026** (Tense Logic - Axiomatic System):
- Target: 03-ProofSystem.tex
- Content: Temporal axioms TK, T4, TA, TL; temporal necessitation rule
- Action: Extract temporal axioms, include in temporal axioms section

### Bimodal Logic Content

**Source Lines 1099-1123** (Bimodal Logic - Tense and Modality):
- Target: 00-Introduction.tex
- Content: Motivation, perpetuity intuitions, possibility, interaction
- Action: Extract and condense to 2-3 paragraphs for introduction

**Source Lines 1124-1176** (Bimodal Logic - Syntax):
- Target: 01-Syntax.tex
- Content: Language BL, well-formed sentences combining modal and temporal operators, abbreviations, scope conventions
- Action: Extract as primary syntax content

**Source Lines 1177-1237** (Bimodal Logic - Semantics):
- Target: 02-Semantics.tex
- Content: Task frames, nullity constraint, compositionality constraint, world histories, task coherence, task models, truth conditions, validity over task frames
- Action: Extract as primary semantics content

**Source Lines 1238-1287** (Bimodal Logic - Axiomatic System):
- Target: 03-ProofSystem.tex, 05-Theorems.tex
- Content: TM system definition, system components (S5 + TL + MF + TF), perpetuity principles P1-P6
- Action: Extract axioms to ProofSystem, perpetuity principles to Theorems

**Source Lines 1345-1436** (Bimodal Logic - Extensions):
- Target: [Appendix or omit]
- Content: Extended language with inevitably, open past, open future operators; intersection, open futures, open pasts; extended semantics
- Action: Omit from Layer 0 documentation (future Layer 1 content)

### Content Statistics

**Total Source Lines**: 1452
**Content Lines Extracted**: ~600 (41%)
**Problem Set Lines Excluded**: ~400 (27%)
**Proof Lines Excluded**: ~150 (10%)
**Fitch System Lines Excluded**: ~150 (10%)
**Other Excluded**: ~150 (10%)
**New Content Added**: ~200 (14% - standardized sections)

**Target Document Length**: ~800 lines LaTeX (18-23 pages PDF)

---

**End of Research Report**
