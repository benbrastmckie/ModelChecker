# Teammate B Findings: Narrative Flow and Section Transitions

## Key Findings

### Section 3 (Modularity) Opening — Line 621-623
```
\section{Modularity, Extensibility, and Systematic Theory Comparison}\label{sec:modularity}

Semantic theories should be modular components that can be composed, compared, and extended without reimplementing core infrastructure.
```
**Assessment**: The opening is a normative claim ("should be"), not a design-rationale paragraph.
It prescribes without explaining *why* modularity matters specifically for *this* framework or what problem modularity solves in the context of what has just been presented in Section 2.
The reader has just seen the three-level pipeline architecture; the transition to modularity is abrupt.
There is no sentence linking "we have shown how a single theory works; now here is why theories must be composable."

### Section 6 (Logos Case Study) Opening — Lines 909-911
```
\section{Case Study: Logos Theory and Unified Hyperintensional Semantics}\label{sec:logos}

The \theorylogos{} theory demonstrates the framework's capacity to implement sophisticated semantic theories---a unified approach to hyperintensional reasoning needed for the language of thought.
```
**Assessment**: This is a statement of what the section does ("demonstrates"), not a rationale for *why* a case study is needed at this point or what question the case study is meant to answer.
After Section 5 (TheoryLib vision), the reader has been told about four theories abstractly.
The Logos case study could explain what a deep dive into a single theory reveals that the high-level overview does not.
The phrase "needed for the language of thought" introduces a philosophical concept (language of thought) without prior context from earlier sections.

---

## Section Transition Analysis

### Sections with Weak Openings (Descriptive Rather Than Motivating)

| Section | Line | Opening Pattern | Problem |
|---------|------|-----------------|---------|
| Sec 2 (Methodology) | 299 | No intro paragraph; dives immediately into subsection | Abrupt; no bridge from Introduction |
| Sec 3 (Modularity) | 621-623 | Normative claim ("should be") | Prescribes without connecting to Section 2 |
| Sec 6 (Logos) | 909-911 | "demonstrates the framework's capacity" | States what it does, not why it's needed here |
| Sec 7 (Results) | 1042 | No intro paragraph; starts with `\paragraph{Experimental Setup.}` | Jumps to setup without motivating what questions the results answer |

### Sections with Adequate or Good Openings

| Section | Line | Why it works |
|---------|------|--------------|
| Sec 4 (Finite Model) | 713-715 | Opens with a rhetorical question: "How can finite model checking provide evidence for semantic validity claims when model classes are infinite?" — this directly motivates the problem the section solves |
| Sec 5 (TheoryLib) | 842-844 | Opens with the guiding principle; frames what follows as flowing from that principle |
| Sec 8 (Discussion) | 1248/1252 | Uses a back-reference "Having demonstrated the methodology... we examine what these results mean" — explicitly connects to prior work |

### The Finite Model Section (Sec 4) as a Model

The rhetorical-question opening at line 713-715 is the best transition in the paper:
> "How can finite model checking provide evidence for semantic validity claims when model classes are infinite?"

This pattern works because it names the tension the section must resolve.
Section 3 and Section 6 lack this tension-naming.

---

## Recommended Improvements

### Section 3 (Modularity) — Replacement Opening (~2 sentences)

**Current** (line 623):
> Semantic theories should be modular components that can be composed, compared, and extended without reimplementing core infrastructure.

**Recommended replacement**:
> The three-level architecture of Section~\ref{sec:methodology} enables any single theory to compile and validate examples---but a framework that requires rewriting core infrastructure for each new theory would limit rather than accelerate semantic research.
> Modularity addresses this: by separating theory-specific semantics from theory-agnostic infrastructure, new theories can be added, combined, and systematically compared without touching the core pipeline.

This replacement: (1) links back to Section 2, (2) names the problem modularity solves, (3) previews the three topics of the section (adding, combining, comparing).

### Section 6 (Logos Case Study) — Replacement Opening (~2 sentences)

**Current** (line 911):
> The \theorylogos{} theory demonstrates the framework's capacity to implement sophisticated semantic theories---a unified approach to hyperintensional reasoning needed for the language of thought.

**Recommended replacement**:
> The four theories catalogued in Section~\ref{sec:theorylib} illustrate the framework's breadth, but breadth alone does not demonstrate depth: can the framework handle a semantically demanding theory that integrates multiple operator subtheories, bilateral evaluation, mereological state structure, and configurable modal axioms?
> The \theorylogos{} theory answers this question---a unified hyperintensional framework that extends truthmaker semantics to cover grounding, essence, counterfactuals, and relevance within a single coherent architecture.

This replacement: (1) links to Section 5, (2) names the specific question the case study answers (depth vs. breadth), (3) previews the scope of Logos without using "language of thought" cold.

### Section 7 (Results) — Minimal Addition (~1 sentence intro before `\paragraph{Experimental Setup.}`)

**Recommendation**: Add one sentence before the experimental setup paragraph at line 1044:
> The preceding sections establish the framework's design and theoretical properties; this section asks whether it works empirically---whether the encoding is tractable, the theories validate correctly, and the performance scales to practical use.

---

## Other Observations

### Section 2 (Methodology) has no section-level intro
Lines 299-301 go directly from `\section` to `\subsection` with no bridging sentence.
The section title "The Programmatic Methodology" provides no motivation.
However, the Introduction does have a roadmap sentence ("Section 2 presents the programmatic methodology...") so this is borderline — a single sentence would still improve the flow.

### Back-Reference Pattern
Section 8 (Discussion, line 1252) uses the back-reference pattern well:
> "Having demonstrated the methodology (Sections 2-6), we examine what these results mean..."

This pattern could be adapted for Section 6:
> "Having established the framework's architecture and comparative capabilities, we now demonstrate depth..."

### The Roadmap (Lines 285-293)
The roadmap paragraph at lines 285-293 is still present and lists all sections mechanically.
(Noted for Teammate A's focus; not addressed here.)

---

## Confidence Level

**High** for the Section 3 and Section 6 assessments — both openings clearly state what the section does rather than motivating *why* it follows from what precedes it.

**High** for Section 4 as the best existing transition model — the rhetorical question technique is demonstrably stronger.

**Medium** for Section 7 — it is weak but the `\paragraph{Experimental Setup.}` structure suggests a deliberate choice to foreground methodology; the fix is minimal.

**Medium** for Section 2 — borderline; the Introduction's roadmap partially substitutes for a section-level motivating sentence.
