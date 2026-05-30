# Implementation Plan: Task #41

- **Task**: 41 - Final conciseness pass: throat-clearing, roadmap, narrative flow
- **Status**: [COMPLETED]
- **Effort**: 1 hour
- **Dependencies**: None
- **Research Inputs**: specs/041_final_conciseness_pass/reports/01_team-research.md
- **Artifacts**: plans/01_conciseness-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: latex
- **Lean Intent**: false

## Overview

Final polish pass on `latex/paper.tex` to remove throat-clearing phrases and improve narrative flow between sections.
Research reveals the six originally-named phrases do not exist in the paper; actual savings are ~102 words from genuine throat-clearing (roadmap paragraph, transition sentence, minor hedges).
Narrative flow improvements add ~80 words of motivated transitions for Sections 3, 6, and 7.
Net word change is modest (~22 word reduction), but quality improvement in paper flow is significant.

### Research Integration

- **Teammate A**: Identified 4 throat-clearing items totaling ~102 words (roadmap paragraph is the largest at 61 words)
- **Teammate B**: Identified weak openings for Sections 3, 6, and 7 with concrete replacement text modeled on Section 4's rhetorical-question pattern

## Goals and Non-Goals

**Goals**:
- Remove throat-clearing phrases and redundant roadmap paragraph
- Improve narrative flow with motivated section transitions
- Maintain paper's technical accuracy and content

**Non-Goals**:
- Structural reorganization of sections
- Content additions beyond transition text
- Word count reduction as primary objective (quality over quantity)

## Risks and Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Line numbers shift after deletions | M | High | Phase 1 (deletions) before Phase 2 (additions); re-verify line numbers |
| Replacement text breaks LaTeX | L | Low | Follow semantic linefeed conventions; test compile |
| Over-editing loses author voice | M | Low | Use exact replacement text from research |

## Implementation Phases

### Phase 1: Throat-Clearing Removal [COMPLETED]

**Goal**: Remove redundant phrases and the roadmap paragraph (~102 words saved)

**Tasks**:
- [ ] Delete roadmap paragraph (lines 285-293): Remove `\paragraph{Paper Roadmap.}` and all 8 section preview sentences
- [ ] Delete transition sentence at line 1252: Remove "Having demonstrated the methodology..." sentence entirely
- [ ] Cut "Perhaps most significantly," at line 264: Replace with "Theories are typically assessed..."
- [ ] Cut "(as expected theoretically)" at line 1034: Remove parenthetical from counterfactual examples list
- [ ] Skip line 1142 "as expected" (borderline; serves comparative function per research)

**Timing**: 20 minutes

**Files to modify**:
- `latex/paper.tex` - 4 edits (3 deletions, 1 rewrite)

**Verification**:
- Paper compiles without errors
- No orphaned cross-references
- Line 264 sentence reads grammatically correct
- Line 1034 list item reads cleanly without parenthetical

**Specific Edits**:

1. **Lines 285-293 (delete)**: Remove entire block:
   ```latex
   \paragraph{Paper Roadmap.}
   Section~\ref{sec:methodology} presents the programmatic methodology...
   ...
   Section~\ref{sec:discussion} discusses future directions, limitations, and conclusions.
   ```

2. **Line 264 (rewrite)**: Change from:
   ```latex
   Perhaps most significantly, theories are typically assessed via subjective aesthetic criteria---``elegance,'' ``simplicity,'' ``naturalness''---rather than empirical measures.
   ```
   To:
   ```latex
   Theories are typically assessed via subjective aesthetic criteria---``elegance,'' ``simplicity,'' ``naturalness''---rather than empirical measures.
   ```

3. **Line 1034 (trim)**: Change from:
   ```latex
   \textbf{Counterfactual} (32 examples): modus ponens ($A, A \boxright B \vdash B$), contraposition failures, strengthening antecedent failures, transitivity failures (as expected theoretically).
   ```
   To:
   ```latex
   \textbf{Counterfactual} (32 examples): modus ponens ($A, A \boxright B \vdash B$), contraposition failures, strengthening antecedent failures, transitivity failures.
   ```

4. **Line 1252 (delete)**: Remove sentence:
   ```latex
   Having demonstrated the methodology (Sections~\ref{sec:methodology}--\ref{sec:logos}), we examine what these results mean for the field (contributions enumerated in Section~\ref{sec:contribution}).
   ```

---

### Phase 2: Narrative Flow Improvements [COMPLETED]

**Goal**: Replace weak section openings with motivated transitions (~80 words added)

**Note**: Line numbers below are AFTER Phase 1 deletions.
Phase 1 removes ~9 lines at 285-293 and 1 line at 1252.
Sections 3, 6, 7 are after the roadmap deletion, so line numbers shift down by 9.

**Tasks**:
- [ ] Replace Section 3 opening (original line 623, adjusted ~line 614): Replace normative claim with design-rationale paragraph
- [ ] Replace Section 6 opening (original line 911, adjusted ~line 902): Replace descriptive statement with motivated question
- [ ] Add Section 7 intro sentence (original before line 1044, adjusted ~line 1035): Insert motivating sentence before Experimental Setup

**Timing**: 30 minutes

**Files to modify**:
- `latex/paper.tex` - 3 edits (2 replacements, 1 insertion)

**Verification**:
- Paper compiles without errors
- Each new opening links to preceding section
- Semantic linefeeds maintained (one sentence per line)
- Cross-references resolve correctly

**Specific Edits**:

1. **Section 3 opening (find by content, not line number)**: Replace:
   ```latex
   Semantic theories should be modular components that can be composed, compared, and extended without reimplementing core infrastructure.
   ```
   With (using semantic linefeeds):
   ```latex
   The three-level architecture of Section~\ref{sec:methodology} enables any single theory to compile and validate examples---but a framework that requires rewriting core infrastructure for each new theory would limit rather than accelerate semantic research.
   Modularity addresses this: by separating theory-specific semantics from theory-agnostic infrastructure, new theories can be added, combined, and systematically compared without touching the core pipeline.
   ```

2. **Section 6 opening (find by content)**: Replace:
   ```latex
   The \theorylogos{} theory demonstrates the framework's capacity to implement sophisticated semantic theories---a unified approach to hyperintensional reasoning needed for the language of thought.
   ```
   With (using semantic linefeeds):
   ```latex
   The four theories catalogued in Section~\ref{sec:theorylib} illustrate the framework's breadth, but breadth alone does not demonstrate depth: can the framework handle a semantically demanding theory that integrates multiple operator subtheories, bilateral evaluation, mereological state structure, and configurable modal axioms?
   The \theorylogos{} theory answers this question---a unified hyperintensional framework that extends truthmaker semantics to cover grounding, essence, counterfactuals, and relevance within a single coherent architecture.
   ```

3. **Section 7 intro (insert before Experimental Setup paragraph)**: Insert after `\section{...}\label{sec:results}` and before `\paragraph{Experimental Setup.}`:
   ```latex
   The preceding sections establish the framework's design and theoretical properties; this section asks whether it works empirically---whether the encoding is tractable, the theories validate correctly, and the performance scales to practical use.

   ```

---

## Testing and Validation

- [ ] Paper compiles with `pdflatex latex/paper.tex` (no errors)
- [ ] No undefined references or warnings
- [ ] Manual review: Section 3 opening links to Section 2
- [ ] Manual review: Section 6 opening links to Section 5
- [ ] Manual review: Section 7 has motivating intro before Experimental Setup
- [ ] Word count change approximately matches estimate (net ~22 word reduction)

## Artifacts and Outputs

- Modified `latex/paper.tex` with throat-clearing removed and narrative flow improved
- Implementation summary at `specs/041_final_conciseness_pass/summaries/01_conciseness-summary.md`

## Rollback/Contingency

If implementation introduces errors:
1. `git checkout latex/paper.tex` to restore original
2. Re-verify line numbers against current file state
3. Apply edits incrementally with compile check after each
