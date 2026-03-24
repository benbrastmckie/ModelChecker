# Implementation Plan: Task #38

- **Task**: 38 - Strengthen proofs, add limitations, qualify novelty claims
- **Status**: [NOT STARTED]
- **Effort**: 3.5 hours
- **Dependencies**: None
- **Research Inputs**: specs/038_strengthen_proofs_and_limitations/reports/01_proofs-limitations-research.md
- **Artifacts**: plans/01_proofs-limitations-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: latex

## Overview

This plan addresses three areas of technical rigor improvement in `latex/paper.tex` for JAR submission: (1) expanding the proof sketch for Z3 encoding correctness with explicit theorems, (2) consolidating and expanding the limitations section with standard threats-to-validity categories, and (3) qualifying novelty claims with precise language about what combination of features is novel while expanding related work coverage.

### Research Integration

Key findings from the research report:
- JAR papers require explicit correctness theorems with structured proof sketches
- Limitations should be organized by validity type (internal, external, construct, conclusion)
- Survey confirms the combination of bilateral evaluation + hyperintensional operators + counterfactuals + SMT model-finding is genuinely novel, but claims should specify which aspects
- Ready-to-use LaTeX templates provided in research appendix

## Goals & Non-Goals

**Goals**:
- Add Encoding Correctness section with Definition, Soundness Theorem, and Countermodel Extraction Theorem
- Create structured Limitations section with threats-to-validity organization
- Qualify novelty claims with precise language specifying the novel combination
- Expand Related Work with modal logic solvers and hyperintensional logic coverage
- Maintain consistency with existing paper structure and terminology

**Non-Goals**:
- Creating mechanized proofs in Coq/Isabelle/Lean (noted as future work)
- Fundamentally restructuring the paper
- Adding new experimental results
- Changing the underlying implementation

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Proof sketch deemed insufficient | H | M | Note mechanized verification as future work; emphasize 177-example empirical validation |
| Limitations section too long | M | L | Keep each point concise; use subsections for organization |
| Missing relevant existing tools | M | L | Use "to our knowledge" qualifier consistently |
| Claims perceived as overclaiming | H | M | Precise language specifying exact combination that is novel |
| LaTeX compilation errors | L | L | Test compilation after each phase |

## Implementation Phases

### Phase 1: Add Encoding Correctness Section [COMPLETED]

**Goal**: Add formal correctness theorems for the Z3 encoding in Section 2 (Methodology)

**Tasks**:
- [ ] Read Section 2 (lines 299-558) to identify best insertion point
- [ ] Create new subsection `\subsection{Encoding Correctness}\label{sec:encoding-correctness}` after Section 2.5 (Computational Complexity)
- [ ] Add Definition (Encoding Function) with structural mapping
- [ ] Add Theorem (Encoding Soundness) with proof sketch covering base case, conjunction, and necessity
- [ ] Add Theorem (Countermodel Extraction) with brief proof sketch
- [ ] Add forward reference to limitations regarding lack of mechanized verification
- [ ] Update paper roadmap in Section 1.3 to mention encoding correctness

**Timing**: 1 hour

**Files to modify**:
- `latex/paper.tex` - Insert new subsection around line 558 (after Section 2.5)

**Verification**:
- LaTeX compiles without errors
- New theorems have labels for cross-referencing
- Proof sketches cover key cases (atomic, conjunction, modal)

---

### Phase 2: Restructure and Expand Limitations Section [NOT STARTED]

**Goal**: Consolidate scattered limitations into structured threats-to-validity format in Section 9.2

**Tasks**:
- [ ] Review existing limitations in Section 5.5 (lines 809-817) and Section 9.2 (lines 1314-1325)
- [ ] Replace Section 9.2 content with structured subsection
- [ ] Add `\subsubsection{Internal Validity: Encoding Correctness}`
- [ ] Add `\subsubsection{External Validity: Generalizability}`
- [ ] Add `\subsubsection{Construct Validity: Complexity Measurement}`
- [ ] Add `\subsubsection{Scalability Limitations}`
- [ ] Cross-reference Section 5.5 from Section 9.2 for finite model limitations
- [ ] Add "Limitations Not Addressed" paragraph listing infinite models, soundness proof automation, multi-theory comparison validity

**Timing**: 1 hour

**Files to modify**:
- `latex/paper.tex` - Rewrite lines 1314-1325 with expanded content

**Verification**:
- All four validity categories present
- Cross-references to relevant sections work
- Content covers all items from research report

---

### Phase 3: Expand Related Work Section [NOT STARTED]

**Goal**: Add detailed coverage of modal logic solvers and hyperintensional implementations

**Tasks**:
- [ ] Read current Related Work (Section 8, lines 1226-1293)
- [ ] Add paragraph on Modal Logic Solvers (MLSolver, PRONOM) to Section 8.1
- [ ] Add paragraph on Hyperintensional Logic (TIL, hyperlogic) to Section 8.3
- [ ] Add paragraph on Truthmaker Semantics (Fine, Yablo) expanding existing brief mention
- [ ] Ensure each paragraph contrasts prior work with our contribution
- [ ] Add necessary bibliography entries if not already present

**Timing**: 45 minutes

**Files to modify**:
- `latex/paper.tex` - Expand Sections 8.1, 8.3
- `latex/references.bib` - Add any missing citations (MLSolver, PRONOM, TIL if needed)

**Verification**:
- Each new paragraph follows Similarity/Difference/Our Contribution format
- Bibliography compiles without warnings
- Comparison table (Table tab:comparison-tools) still accurate

---

### Phase 4: Qualify Novelty Claims Throughout Paper [NOT STARTED]

**Goal**: Make novelty claims precise about what combination of features is novel

**Tasks**:
- [ ] Locate all "first" claims: lines 232, 1085, 1268, 1304, 1345
- [ ] Update abstract claim (line 232) with qualified language
- [ ] Update Section 7 claim (line 1085) to specify the integration being novel
- [ ] Update Section 8.3 claim (line 1268) with "to our knowledge" and specifics
- [ ] Update Section 9.1 claim (line 1304) with precise characterization
- [ ] Update conclusion claim (line 1345) consistently
- [ ] Ensure claims specify: bilateral evaluation, hyperintensional operators, counterfactuals, SMT model-finding

**Timing**: 30 minutes

**Files to modify**:
- `latex/paper.tex` - Update 5 locations with qualified claims

**Verification**:
- All claims use "to our knowledge" qualifier
- All claims specify which aspects are novel (the combination, not individual components)
- Consistency across all locations

---

### Phase 5: Final Verification and Compilation [NOT STARTED]

**Goal**: Ensure all changes compile correctly and cross-references work

**Tasks**:
- [ ] Run `pdflatex paper.tex` twice for cross-references
- [ ] Run `bibtex paper` for bibliography
- [ ] Run `pdflatex paper.tex` twice more
- [ ] Check for any LaTeX warnings (undefined references, citations)
- [ ] Verify new section labels work in cross-references
- [ ] Review PDF output for formatting issues
- [ ] Check that semantic linefeeds are maintained (one sentence per line)

**Timing**: 15 minutes

**Files to modify**:
- None (verification only)

**Verification**:
- Zero LaTeX errors
- Zero undefined reference warnings
- PDF renders correctly with new theorems and sections

## Testing & Validation

- [ ] LaTeX compiles without errors
- [ ] All new theorem/definition environments render correctly
- [ ] Cross-references to new section labels work
- [ ] Bibliography entries resolve
- [ ] Proof sketches cover base case, inductive case for conjunction, inductive case for necessity
- [ ] Limitations section has all four validity categories
- [ ] All five novelty claim locations updated consistently
- [ ] Related work paragraphs follow Similarity/Difference/Contribution format
- [ ] Semantic linefeeds maintained throughout new content

## Artifacts & Outputs

- `latex/paper.tex` - Updated with encoding correctness section, expanded limitations, qualified novelty claims, expanded related work
- `latex/references.bib` - Any new bibliography entries
- `specs/038_strengthen_proofs_and_limitations/summaries/01_proofs-limitations-summary.md` - Implementation summary (created during execution)

## Rollback/Contingency

If changes cause unexpected compilation errors or break existing structure:
1. `git checkout latex/paper.tex` to restore original
2. Apply changes incrementally, testing compilation after each phase
3. If specific phase fails, skip and note in summary for later manual fix
