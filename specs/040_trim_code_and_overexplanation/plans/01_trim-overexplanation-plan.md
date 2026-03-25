# Implementation Plan: Trim Code Listings, Over-Explanation, and Aspirational Content

- **Task**: 40 - Trim code listings, over-explanation, and aspirational content
- **Status**: [NOT STARTED]
- **Effort**: 2.5 hours
- **Dependencies**: None
- **Research Inputs**: specs/040_trim_code_and_overexplanation/reports/01_trim-overexplanation.md
- **Artifacts**: plans/01_trim-overexplanation-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: latex
- **Lean Intent**: false

## Overview

This plan implements targeted verbosity reduction in `latex/paper.tex` across three categories identified in the research report: (1) code listings that show boilerplate or redundant patterns, (2) over-explanations of concepts familiar to JAR readers, and (3) aspirational TheoryLib content that reads like project documentation rather than journal content. Estimated savings: 1,300-1,600 words total. Each phase targets one category, with LaTeX compilation verification after each phase.

### Research Integration

The research report (01_trim-overexplanation.md) provides specific line numbers and word savings estimates for each cut. High-priority cuts (largest impact, lowest risk) are prioritized within each phase.

## Goals & Non-Goals

**Goals**:
- Reduce paper length by approximately 1,300 words
- Remove README-style content inappropriate for JAR
- Trim code listings to essential patterns
- Condense explanations of standard concepts
- Maintain all technical depth and novel contributions

**Non-Goals**:
- Restructuring sections or moving content
- Changing hyperintensional operator definitions (these are novel)
- Removing the Conjunction operator listing (serves as canonical example)
- Modifying the empirical results section

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Breaking LaTeX compilation | H | M | Compile after each phase; use `latexmk -pdf` |
| Removing content that reviewers expect | M | L | Keep all standard JAR content; only cut README material |
| Line number drift during editing | M | H | Work in reverse order within each section; re-verify line numbers before each edit |
| Accidental removal of cross-references | M | L | Check `\ref{}` and `\cite{}` usage before cutting |

## Implementation Phases

### Phase 1: Remove Aspirational TheoryLib Content [COMPLETED]

**Goal**: Remove README-style content from Section 5 (TheoryLib vision subsection) and conclusion. This is the highest-impact category with lowest risk since it removes entire subsections of promotional content.

**Tasks**:
- [ ] Remove Community and Contribution Model subsection (lines 981-987)
  - Delete entire `\subsection{Community and Contribution Model}` including MIT license, GitHub, contribution incentives
  - Estimated savings: ~120 words
- [ ] Condense Vision subsection (lines 903-937)
  - Remove BibTeX listing (lines 921-930)
  - Remove benchmark API listing (lines 907-915)
  - Replace three paragraphs with single sentence: "The framework enables systematic cross-theory comparison via benchmark suites, with theories as citable, versioned components supporting reproducible research."
  - Estimated savings: ~250 words
- [ ] Trim Benefits of theory-agnosticism (line 968)
  - Replace enumerated list with: "This separation enables independent theory development without framework modification."
  - Estimated savings: ~40 words
- [ ] Trim Sharing, Reuse paragraph (lines 973-974)
  - Remove: "Classical conjunction behaves identically in \theorylogos{} and \theoryexclusion{}, while negation differs." (already stated in Section 7)
  - Estimated savings: ~20 words
- [ ] Trim Conclusion TheoryLib vision (lines 1457-1458)
  - Change: "...serving as a comparative research platform, archival and citation system, educational resource, and collaborative community hub."
  - To: "...serving as a comparative research platform with version-controlled archival."
  - Estimated savings: ~15 words
- [ ] Remove promotional final sentence (line 1462)
  - Delete: "The future of semantic theory is computational, modular, and collaborative---and it starts with frameworks like \modelchecker{} making that future accessible to researchers today."
  - Estimated savings: ~30 words
- [ ] Trim Broader Impact generic items (lines 1440-1441)
  - Remove "Cumulative knowledge building" and "Lower barrier to entry" items
  - Estimated savings: ~25 words
- [ ] Compile and verify no errors

**Timing**: 45 minutes

**Files to modify**:
- `latex/paper.tex` - lines 903-987 (Vision and Community subsections), lines 1436-1462 (Conclusion)

**Verification**:
- `latexmk -pdf latex/paper.tex` compiles without errors
- All cross-references resolve

---

### Phase 2: Trim Code Listings [COMPLETED]

**Goal**: Reduce code listing verbosity by removing boilerplate, merging redundant examples, and showing only semantically interesting code.

**Tasks**:
- [ ] Trim Theory plugin inheritance listing (lines 634-650)
  - Reduce to signature-only view showing class name and method signatures with `...` bodies
  - Estimated savings: ~80 words (6 lines)
- [ ] Trim Semantic interface listing (lines 942-964)
  - Remove `__init__` method entirely
  - Remove docstrings
  - Keep only `fusion` and `is_part_of` method bodies
  - Remove `LogosSemantics` stub at bottom
  - Add prose: "Theories extend \texttt{SemanticDefaults}, overriding primitive declarations as needed."
  - Estimated savings: ~90 words (8 lines)
- [ ] Trim Dynamic operator loading (lines 660-672)
  - Reduce three examples to one, add comment about analogous calls
  - Keep: `logos_modal = logos.get_theory(['extensional', 'modal'])`
  - Add comment: `# Analogous calls load counterfactual, constitutive, relevance subtheories`
  - Estimated savings: ~50 words (4 lines)
- [ ] Trim Multi-theory comparison (lines 686-702)
  - Remove settings dict, simplify to essential pattern
  - Estimated savings: ~60 words (7 lines)
- [ ] Trim Logos Z3 primitives listing (lines 1032-1047)
  - Consolidate comment lines (merge "Core evaluation functions" and "Mereology" into one line)
  - Estimated savings: ~30 words (3 lines)
- [ ] Trim Necessity operator listing (lines 1083-1093)
  - Simplify list comprehension, remove intermediate variable
  - Estimated savings: ~30 words (2 lines)
- [ ] Compile and verify no errors

**Timing**: 50 minutes

**Files to modify**:
- `latex/paper.tex` - multiple code listings in Sections 3, 5, and 6

**Verification**:
- `latexmk -pdf latex/paper.tex` compiles without errors
- Code listings remain syntactically valid Python (even if abbreviated)

---

### Phase 3: Trim Over-Explanations for JAR Audience [NOT STARTED]

**Goal**: Condense explanations of standard concepts that JAR readers already know (Kripke semantics, De Morgan, bitvector encodings).

**Tasks**:
- [ ] Trim Bilateral Evaluation explanation (lines 1021-1025)
  - Replace two paragraphs with: "Bilateral evaluation uses exact verifiers and falsifiers (Section~\ref{sec:state-space})."
  - Estimated savings: ~40 words
- [ ] Condense State space binary representation (lines 757-767)
  - Keep first example ($000_2 = 0 \mapsto \nullstate$) and last ($111_2 = 7 \mapsto \text{full state}$)
  - Replace middle 5 lines with `\vdots`
  - Estimated savings: ~50 words
- [ ] Condense Frame constraints list (line 1049)
  - Replace enumerated list with: "Frame constraints include null state existence, downward/fusion closure, world existence/maximality, and configurable modal axioms (reflexivity, transitivity for S4/S5)."
  - Estimated savings: ~40 words
- [ ] Trim Extensional operator prose (lines 1073-1078)
  - Keep Conjunction interpretation
  - Replace Negation + other operators with: "Negation swaps verifiers/falsifiers; remaining extensional operators follow standard definitions (De Morgan for disjunction, material implication)."
  - Estimated savings: ~70 words
- [ ] Trim Modal operator explanation (lines 1095-1097)
  - Replace with: "Standard Kripke semantics with configurable accessibility (K, S4, S5)."
  - Estimated savings: ~40 words
- [ ] Trim Design goals list (line 1029)
  - Replace with: "The implementation prioritizes modularity and tractability."
  - Estimated savings: ~50 words
- [ ] Trim Validation process description (lines 1138-1139)
  - Replace with: "Each example is manually constructed with expected validity, then regression-tested on every commit."
  - Estimated savings: ~50 words
- [ ] Compile and verify no errors

**Timing**: 45 minutes

**Files to modify**:
- `latex/paper.tex` - prose sections in Sections 4 and 6

**Verification**:
- `latexmk -pdf latex/paper.tex` compiles without errors
- Technical accuracy preserved (no semantic information lost)

---

## Testing & Validation

- [ ] Full LaTeX compilation succeeds with no errors
- [ ] No overfull hbox warnings in trimmed sections
- [ ] All cross-references (`\ref{}`, `\Cref{}`) still resolve
- [ ] All citations (`\cite{}`) still present
- [ ] Word count reduction of approximately 1,300 words (use `texcount latex/paper.tex`)
- [ ] Visual review of PDF confirms no formatting issues
- [ ] Hyperintensional operator definitions unchanged
- [ ] Conjunction listing (canonical example) preserved

## Artifacts & Outputs

- `specs/040_trim_code_and_overexplanation/plans/01_trim-overexplanation-plan.md` (this file)
- `latex/paper.tex` (modified)
- `specs/040_trim_code_and_overexplanation/summaries/01_trim-overexplanation-summary.md` (after implementation)

## Rollback/Contingency

If edits cause compilation failures or remove essential content:
1. Use `git checkout latex/paper.tex` to restore original
2. Re-apply edits one at a time to isolate problematic change
3. Consult research report for alternative trimming strategies
4. Consider keeping more context for ambiguous cuts (e.g., state space enumeration)
