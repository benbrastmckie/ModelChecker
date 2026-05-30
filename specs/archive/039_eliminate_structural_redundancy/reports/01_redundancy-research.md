# Research Report: Task #39

**Task**: 39 - Eliminate structural redundancy across sections
**Started**: 2026-03-24T16:59:33-07:00
**Completed**: 2026-03-24T17:15:00-07:00
**Effort**: Medium (structural analysis of 1559-line document)
**Dependencies**: None
**Sources/Inputs**: latex/paper.tex (1559 lines)
**Artifacts**: This report
**Standards**: report-format.md, semantic linefeeds (latex.md)

## Executive Summary

- **Bitvector representation** explained 4 times (lines 434-444, 513, 769-789, 1058-1068, 1402-1405)
- **Bilateral semantics** explained 6 times (lines 231-232, 323, 499-504, 890-894, 1032-1038, 1334-1337)
- **Arity/exponential growth** discussed 5 times across Section 2.5 (413-553) and performance tables
- **"First implementation" novelty claim** asserted 5 times (lines 232, 1146, 1337, 1378, 1479)
- Tables 6 (line 709) and 8 (line 1247) have significant overlap in comparing theory predictions
- Section 9.1 re-enumerates contributions already listed in Section 1.3

## Context & Scope

This research identifies structural redundancy in `latex/paper.tex` to enable consolidation.
The goal is to reduce repetition while maintaining readability and coherence.
The paper is a JAR (Journal of Automated Reasoning) submission at 1559 lines.

## Findings

### 1. Bitvector Representation Redundancy

| Location | Lines | Content | Role |
|----------|-------|---------|------|
| Section 2.5.2 | 432-444 | Function arity examples with `BitVecSort` | Technical detail |
| Section 2.5.4 | 513 | "uses bitvector OR ($s_1 \mathbin{|}s_2$)" | Design principle |
| Section 4.2 | 769-789 | Full bitvector representation explanation | **PRIMARY** |
| Section 6.2 | 1058-1068 | Z3 primitive declarations with `BitVecSort` | Code example |
| Section 9.2.1 | 1402-1405 | "States represented as $N$-bit bitvectors" | Limitations |

**Recommendation**:
- **Primary location**: Section 4.2 (lines 767-789) - State Space Representation
- Lines 432-444: Keep code example but remove prose explanation; add back-reference to Section 4.2
- Line 513: Keep brief mention, add "see Section 4.2"
- Lines 1058-1068: Keep code listing but remove redundant prose about BitVecSort
- Lines 1402-1405: Keep as limitation discussion (different context - N>64 limits)

**Estimated savings**: ~80-100 words

### 2. Bilateral Semantics Redundancy

| Location | Lines | Content | Role |
|----------|-------|---------|------|
| Abstract | 231-232 | "bilateral truthmaker semantics" | First mention |
| Section 2.1.2 | 323 | "Bilateral theories add falsify" | Technical detail |
| Section 2.5.5 | 499-504 | "bilateral \theorylogos{} theory" vs unilateral | Comparison |
| Section 5.1 | 890-894 | "Bilateral Hyperintensional..." full description | **PRIMARY** |
| Section 6.1 | 1032-1038 | "Bilateral Evaluation" definition | Case study context |
| Section 8.3 | 1334-1337 | "Fine's bilateral truthmaker framework" | Related work |

**Recommendation**:
- **Primary location**: Section 6.1 (lines 1032-1038) provides the definitive explanation
- Abstract (231-232): Keep, but ensure it's the only place using "first computational implementation"
- Line 323: Keep one-line mention
- Lines 499-504: Replace with back-reference "the bilateral approach (Section 6.1)"
- Lines 890-894: Consolidate with Section 6.1 or cross-reference
- Lines 1334-1337: Keep for related work context but trim explanation

**Estimated savings**: ~150-200 words

### 3. Arity and Exponential Growth Redundancy

| Location | Lines | Content | Role |
|----------|-------|---------|------|
| Section 2.5 header | 413-415 | "arity (number of arguments)" intro | Definition |
| Section 2.5.2 | 428-447 | Arity and Quantifier Complexity | **PRIMARY** |
| Section 2.5.3 | 449-467 | Theory Comparison by Primitive Arity (Table 3) | Analysis |
| Section 2.5.4 | 469-494 | Empirical Performance by Arity (Table 4) | Benchmarks |
| Section 2.6 | 537-553 | Constraint Scaling by Primitive Arity (Table 5) | Scaling |
| Section 6 perf | 1187-1199 | Performance table (Table 9) | Case study data |

**Analysis**: The arity discussion spans ~140 lines (413-553) with 3 related tables.
This is thorough but could be consolidated.

**Recommendation**:
- Merge Tables 3, 4, and 5 into a single comprehensive table
- Lines 413-470: Keep as primary arity explanation
- Lines 472-507: Consider moving to appendix or condensing
- Section 6 (1187-1199): Keep performance data but cross-reference arity discussion

**Estimated savings**: ~200-300 words by consolidating tables

### 4. "First Implementation" Novelty Claim Redundancy

| Location | Lines | Text |
|----------|-------|------|
| Abstract | 232 | "To our knowledge, this represents the first computational implementation of bilateral truthmaker semantics..." |
| Section 6.4 | 1146 | "To our knowledge, \theorylogos{} represents the first computational implementation integrating bilateral evaluation..." |
| Section 8.3 | 1337 | "to our knowledge, \modelchecker{} provides the first computational implementation of bilateral truthmaker semantics..." |
| Section 9.1 | 1378 | "to our knowledge, the first computational realization of Fine's informal semantics..." |
| Section 9.4 | 1479 | "to our knowledge, the first computational implementation of bilateral truthmaker semantics..." |

**Recommendation**:
- **Keep in 2 places only**: Abstract (232) and Contributions Summary (1378)
- Line 1146: Replace with "This unification demonstrates the framework's expressiveness."
- Line 1337: Replace with "Our implementation translates Fine's informal semantics into executable Z3 constraints."
- Line 1479: Replace with "rich semantics (bilateral truthmaker semantics with integrated hyperintensional operators)"

**Estimated savings**: ~100 words and improved readability

### 5. Table Comparison Analysis: Tables 6 and 8

**Table 6** (line 709): "Comparative Predictions Across Theories"
```
Columns: Argument | Classical | Modal S4 | Logos | Exclusion | Notes
Rows: 3 examples (conjunction commutativity, disjunction intro, K axiom)
```

**Table 8** (line 1247): "Comparative Inference Results Across Theories"
```
Columns: Inference | Class. | S4 | Logos | Excl. | Notes
Rows: 7 examples (the 3 from Table 6 plus 4 more)
```

**Overlap Analysis**:
- Both tables compare the same 4 theories
- Both use Valid/Invalid notation
- Table 8 is a superset of Table 6 (contains all 3 Table 6 rows plus 4 more)
- Table 6: line 709 (Section 3.3)
- Table 8: line 1247 (Section 7.3)

**Recommendation**:
- **Option A (preferred)**: Delete Table 6, forward-reference Table 8 from Section 3.3
- **Option B**: Keep Table 6 as "preview" with 3 examples, ensure no row duplication in Table 8
- If keeping both: differentiate purposes (Table 6 = quick example, Table 8 = comprehensive)

**Estimated savings**: ~200 words (if Option A)

### 6. Discussion Section Contribution Re-enumeration

**Section 1.3** (lines 275-283): "Our Contribution" - 6 numbered items
**Section 9.1** (lines 1374-1386): "Contributions Summary" - 8 items under Theoretical/Practical

**Overlap Analysis**:
| Sec 1.3 Item | Sec 9.1 Equivalent |
|--------------|-------------------|
| Compiles semantic theories to SMT | Programmatic methodology (1377) |
| Modular theory composition | Theory-agnostic framework (1379) |
| Systematic comparison | Systematic comparative analysis (1384) |
| Finite model exploration | Finite model methodology (1380) |
| Implements TheoryLib | TheoryLib (1383) |
| Objective complexity measures | (not explicitly restated) |
| N/A | Bilateral truthmaker implementation (1378) |
| N/A | Educational resources (1385) |
| N/A | Open source (1386) |

**Recommendation**:
Rewrite Section 9.1 to focus on **implications and analysis** rather than re-listing contributions:
- "Having demonstrated X, we now discuss its implications for Y"
- Focus on what the contributions mean rather than what they are
- Cross-reference Section 1.3 for the contribution list

**Estimated savings**: ~150-200 words

### 7. Logos Case Study Re-explanations (Section 6)

Section 6 (lines 1007-1160) re-explains concepts from Sections 2-4:

| Re-explanation | Location | Already Covered |
|----------------|----------|-----------------|
| Truthmaker semantics basics | 1013-1022 | Section 2 methodology |
| Hyperintensional definition | 1015-1022 | Could be in Section 2 |
| Bilateral evaluation | 1035-1040 | Lines 231-232, 323, 499-504 |
| Mereological structure | 1042-1047 | Section 4.2 (769-789) |
| Bitvector encoding | 1057-1069 | Section 2.5, 4.2 |
| Frame constraints list | 1071 | Section 2.4 (399-411) |

**Recommendation**:
- Lines 1013-1014: Keep brief intro
- Lines 1015-1032: Move Definition 6 (Hyperintensional Operator) to Section 2
- Lines 1035-1040: Replace with back-reference to Section 2 or new consolidated location
- Lines 1042-1047: Replace with "The mereological structure (Section 4.2) enables..."
- Lines 1057-1069: Keep code listing, remove prose already in Section 2.5
- Line 1071: Keep enumeration but note "as defined in Section 2.4"

**Estimated savings**: ~250-350 words

## Decisions

1. **Primary explanation locations** established for each redundant concept
2. **Tables 6 and 8**: Recommend merging (Option A) to eliminate duplication
3. **"First implementation" claims**: Reduce from 5 to 2 occurrences
4. **Section 9.1**: Restructure to analyze rather than enumerate

## Risks & Mitigations

| Risk | Mitigation |
|------|------------|
| Over-aggressive cutting loses clarity | Use back-references liberally |
| Forward/backward references break flow | Add brief inline reminders |
| Reviewers may not follow cross-references | Keep one-sentence summaries |
| Different audiences need different entry points | Maintain Abstract + Intro completeness |

## Word/Page Savings Estimate

| Area | Estimated Words Saved |
|------|----------------------|
| Bitvector representation | 80-100 |
| Bilateral semantics | 150-200 |
| Arity discussion consolidation | 200-300 |
| "First implementation" claims | 100 |
| Table 6 removal | 200 |
| Section 9.1 restructure | 150-200 |
| Section 6 back-references | 250-350 |
| **Total** | **1130-1450 words** |

At ~300 words/page, this represents **3.5-5 pages** of savings.

## Implementation Priority

1. **High Impact, Low Risk**: Remove duplicate "first implementation" claims (4 of 5)
2. **High Impact, Medium Risk**: Merge or differentiate Tables 6 and 8
3. **Medium Impact, Low Risk**: Add back-references throughout Section 6
4. **Medium Impact, Medium Risk**: Consolidate arity tables (3 tables -> 1)
5. **Low Impact, High Value**: Restructure Section 9.1 as analysis

## Appendix

### Search Queries Used
- `bitvector|bit-vector|BitVec|bit vector` (case-insensitive)
- `bilateral`
- `first.*(implementation|computational)|first.*bilateral`
- `arity|exponential|2\^N`

### Line Number Reference Summary

| Concept | Primary Location | Redundant Locations |
|---------|------------------|---------------------|
| Bitvector | 767-789 | 432-444, 513, 1058-1068, 1402-1405 |
| Bilateral | 1032-1038 | 231-232, 323, 499-504, 890-894, 1334-1337 |
| Arity | 428-470 | 472-553 (consolidate tables) |
| "First impl" | 232, 1378 | 1146, 1337, 1479 (remove) |
| Tables overlap | Table 8 (1247) | Table 6 (709) (merge) |
| Contributions | 275-283 | 1374-1386 (restructure) |
