# Implementation Plan: Eliminate Structural Redundancy

- **Task**: 39 - Eliminate structural redundancy across sections
- **Status**: [NOT STARTED]
- **Effort**: 4 hours
- **Dependencies**: Tasks 37-38 (new content must be in place before consolidation)
- **Research Inputs**: specs/039_eliminate_structural_redundancy/reports/01_redundancy-research.md
- **Artifacts**: plans/01_redundancy-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: latex

## Overview

This plan consolidates redundant explanations in `latex/paper.tex` (1559 lines) to reduce length by an estimated 3.5-5 pages. The research report identified six categories of redundancy: bitvector representation (4 locations), bilateral semantics (6 locations), arity discussion (5 locations with 3 tables), "first implementation" novelty claims (5 locations), overlapping comparison tables (Tables 6 and 8), and contribution re-enumeration (Sections 1.3 and 9.1). The approach uses back-references to primary explanations rather than deletion, preserving accessibility while eliminating repetition.

### Research Integration

Key findings from 01_redundancy-research.md:
- Primary locations established for each concept
- Tables 6 and 8 share 3 identical rows (Table 8 is superset)
- "First implementation" claims appear 5 times but should appear only 2
- Section 6 re-derives concepts already covered in Sections 2-4
- Estimated savings: 1130-1450 words (3.5-5 pages)

## Goals & Non-Goals

**Goals**:
- Reduce redundant explanations by adding back-references
- Consolidate or differentiate Tables 6 and 8
- Limit "first implementation" claims to 2 strategic locations
- Restructure Section 9.1 to analyze rather than re-enumerate contributions
- Trim Section 6 re-explanations with cross-references to earlier sections

**Non-Goals**:
- Removing any concepts entirely (only consolidating explanations)
- Restructuring document section order
- Adding new content beyond cross-reference phrases
- Modifying Tables 3, 4, 5 (arity tables) in this task

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Over-aggressive cutting loses clarity | H | M | Use back-references liberally; keep one-sentence summaries |
| Broken forward/backward references | M | L | Verify each cross-reference target exists |
| Reviewers may not follow cross-references | M | M | Maintain brief inline reminders with section numbers |
| Line numbers shift during editing | L | H | Work from highest line numbers downward within each phase |

## Implementation Phases

### Phase 1: Remove Redundant "First Implementation" Claims [COMPLETED]

**Goal**: Reduce "first implementation" novelty claims from 5 occurrences to 2 (Abstract and Contributions Summary)

**Tasks**:
- [ ] Keep line 232 (Abstract): "To our knowledge, this represents the first computational implementation..."
- [ ] Keep line 1378 (Section 9.1): "to our knowledge, the first computational realization..."
- [ ] Replace line 1479 (Section 9.4) with: "rich semantics (bilateral truthmaker semantics with integrated hyperintensional operators)"
- [ ] Replace line 1337 (Section 8.3) with: "Our implementation translates Fine's informal semantics into executable Z3 constraints."
- [ ] Replace line 1146 (Section 6.4) with: "This unification demonstrates the framework's expressiveness."

**Timing**: 30 minutes

**Files to modify**:
- `latex/paper.tex` - lines 1146, 1337, 1479

**Verification**:
- grep for "first.*implementation" shows only 2 matches (lines 232 and 1378)
- Document compiles without errors

---

### Phase 2: Consolidate Tables 6 and 8 [COMPLETED]

**Goal**: Eliminate duplication between Table 6 (line 709) and Table 8 (line 1247)

**Tasks**:
- [ ] Option A (preferred): Remove Table 6 entirely and add forward reference
  - Delete Table 6 (around line 709)
  - Replace with: "Table~\ref{tab:comparative-inference} in Section~\ref{sec:inference-comparison} provides a comprehensive comparison of inference validity across theories."
- [ ] Update any references to Table 6 to point to Table 8
- [ ] If Table 6 has unique label, update cross-references

**Timing**: 45 minutes

**Files to modify**:
- `latex/paper.tex` - Table 6 region (around line 709), any \ref{} to old table

**Verification**:
- Only one comparison table remains (Table 8)
- All cross-references resolve correctly
- Document compiles without undefined references

---

### Phase 3: Add Back-References for Bitvector Representation [IN PROGRESS]

**Goal**: Establish Section 4.2 (lines 767-789) as primary bitvector explanation; add back-references elsewhere

**Tasks**:
- [ ] Lines 432-444 (Section 2.5.2): Keep code example, add at end: "(see Section~\ref{sec:state-space} for complete bitvector representation)"
- [ ] Line 513 (Section 2.5.4): Add parenthetical: "(detailed in Section~\ref{sec:state-space})"
- [ ] Lines 1058-1068 (Section 6.2): Keep code listing, trim prose explaining BitVecSort; add: "using the bitvector representation from Section~\ref{sec:state-space}"
- [ ] Lines 1402-1405 (Section 9.2.1): Keep as-is (different context: limitations for N>64)

**Timing**: 45 minutes

**Files to modify**:
- `latex/paper.tex` - lines 432-444, 513, 1058-1068

**Verification**:
- grep for "BitVec" shows primary explanation at 767-789 and brief references elsewhere
- All \ref{sec:state-space} references resolve
- Document compiles

---

### Phase 4: Add Back-References for Bilateral Semantics [NOT STARTED]

**Goal**: Establish Section 6.1 (lines 1032-1038) as primary bilateral explanation; add back-references elsewhere

**Tasks**:
- [ ] Lines 499-504 (Section 2.5.5): Replace full explanation with: "the bilateral approach (detailed in Section~\ref{sec:logos-bilateral})"
- [ ] Lines 890-894 (Section 5.1): Replace with brief mention and cross-reference: "Bilateral Hyperintensional semantics (Section~\ref{sec:logos-bilateral})"
- [ ] Lines 1334-1337 (Section 8.3): Trim to: "Fine's bilateral truthmaker framework, which we implement (Section~\ref{sec:logos-bilateral})"
- [ ] Abstract (231-232) and line 323: Keep as-is (appropriate for context)

**Timing**: 45 minutes

**Files to modify**:
- `latex/paper.tex` - lines 499-504, 890-894, 1334-1337

**Verification**:
- grep for "bilateral" shows concise mentions with cross-references to primary location
- All \ref{sec:logos-bilateral} references resolve
- Document compiles

---

### Phase 5: Trim Section 6 Re-explanations [NOT STARTED]

**Goal**: Reduce Section 6 (Logos Case Study) re-derivations by referencing earlier sections

**Tasks**:
- [ ] Lines 1015-1032: Move Definition 6 (Hyperintensional Operator) to Section 2; replace with reference
- [ ] Lines 1042-1047 (mereological structure): Replace with: "The mereological structure (Section~\ref{sec:state-space}) enables..."
- [ ] Line 1071 (frame constraints): Add: "(as defined in Section~\ref{sec:frame-conditions})"
- [ ] Review 1013-1014 (truthmaker basics): Keep brief intro sentence only

**Timing**: 45 minutes

**Files to modify**:
- `latex/paper.tex` - lines 1013-1071 (Section 6.1-6.2)

**Verification**:
- Section 6 assumes reader has read Sections 2-4
- Definition 6 appears in Section 2 (or has clear forward reference)
- All cross-references resolve

---

### Phase 6: Restructure Section 9.1 (Contributions Summary) [NOT STARTED]

**Goal**: Rewrite Section 9.1 to focus on implications rather than re-listing contributions

**Tasks**:
- [ ] Lines 1374-1386: Replace contribution enumeration with analysis
- [ ] New structure:
  - Opening: "Having demonstrated the methodology in Sections 2-6, we now examine what these results mean for the field."
  - Focus on implications: "The systematic comparison reveals that..."
  - Focus on methodology contributions: "The finite model approach enables..."
- [ ] Add cross-reference to Section 1.3 for complete contribution list: "(contributions enumerated in Section~\ref{sec:contributions})"

**Timing**: 30 minutes

**Files to modify**:
- `latex/paper.tex` - lines 1374-1386 (Section 9.1)

**Verification**:
- Section 9.1 discusses implications, not enumeration
- Cross-reference to Section 1.3 present
- No redundant contribution statements

## Testing & Validation

- [ ] Document compiles without errors: `pdflatex paper.tex`
- [ ] No undefined references: check for "??" in output
- [ ] Word count reduced: compare before/after (target: 1000+ words reduction)
- [ ] All cross-references resolve to correct sections
- [ ] grep verification for each redundancy category (see phase verification steps)
- [ ] Visual review: Section 6 reads as case study, not tutorial

## Artifacts & Outputs

- `specs/039_eliminate_structural_redundancy/plans/01_redundancy-plan.md` (this file)
- `specs/039_eliminate_structural_redundancy/summaries/01_redundancy-summary.md` (after completion)
- Modified `latex/paper.tex` with consolidated explanations

## Rollback/Contingency

- Git commit before starting implementation preserves original state
- If changes break document structure: `git checkout latex/paper.tex`
- If cross-references cause issues: restore individual sections from git history
- Keep copy of original line numbers in this plan for reference
