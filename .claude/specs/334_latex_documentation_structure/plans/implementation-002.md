# Implementation Plan: LaTeX Documentation for Logos System

## Metadata

- **Task Number**: 334
- **Task Title**: Create LaTeX documentation for Logos system mirroring layer structure
- **Status**: [NOT STARTED]
- **Estimated Effort**: 6 hours
- **Actual Effort**: TBD
- **Language**: general
- **Priority**: Medium
- **Created**: 2026-01-08
- **Updated**: 2026-01-08
- **Blocking**: None
- **Dependencies**: None
- **Plan Version**: 2
- **Reports Integrated**:
  - research-001.md (2026-01-08): Source LaTeX analysis and target documentation design
  - research-002.md (2026-01-08): Layer 1 constitutive and causal operators for future work

## Overview

### Problem Statement

The Logos project lacks a comprehensive, readable LaTeX reference document presenting the formal definitions, semantics, proof system, and metalogical properties of the TM (Tense and Modality) logic system. While the Lean implementation provides complete formal verification, it requires Lean expertise to understand. A LaTeX reference would serve as an accessible entry point for researchers, students, and practitioners to learn the Logos system without reading Lean code.

### Scope

This plan covers creating Layer 0 (Core TM logic) LaTeX documentation by extracting and reorganizing content from the existing LogicNotes.tex source document (1452 lines). The documentation will mirror the Logos layer architecture with a modular subfile structure.

**In Scope**:
- Create Documentation/LaTeX/ directory structure with subfile architecture
- Copy source LaTeX assets (formatting.sty, notation.sty, bib_style.bst, glossary.tex)
- Create logos-notation.sty with Logos-specific macros
- Extract content from LogicNotes.tex for Layer 0 (Core TM logic)
- Generate 6 subfiles: 00-Introduction, 01-Syntax, 02-Semantics, 03-ProofSystem, 04-Metalogic, 05-Theorems
- Add standardized sections per requirement
- Add Lean cross-references to major definitions
- Validate LaTeX compilation and formatting

**Out of Scope**:
- Layer 1-3 documentation (future work)
- New mathematical content or proofs
- Automated PDF generation pipeline
- Modification of Lean source code
- Translation to HTML or other formats

### Constraints

- MUST exclude all problem sets from source (~400 lines, 27%)
- MUST exclude proofs, keeping only definitions and theorem statements
- MUST exclude Fitch natural deduction (not in Logos implementation)
- MUST maintain source formatting standards
- MUST create subfile for each Logos layer component
- MUST include standardized sections per layer
- MUST compile as valid LaTeX document
- MUST provide minimal explanation (1-2 sentences per definition)
- MUST be readable without Lean code knowledge

### Definition of Done

- [ ] Directory structure created: Documentation/LaTeX/ with subfiles/, assets/, bibliography/
- [ ] Style files copied and tested: formatting.sty, notation.sty, bib_style.bst, glossary.tex
- [ ] New logos-notation.sty created with Logos-specific macros
- [ ] Main document LogosReference.tex created with subfile architecture
- [ ] 6 subfiles generated: 00-Introduction.tex through 05-Theorems.tex
- [ ] All subfiles compile independently without errors
- [ ] Full document compiles successfully
- [ ] All Lean cross-references validated
- [ ] Mathematical notation consistent throughout
- [ ] Final PDF generated (18-23 pages) and reviewed

### Research Integration

This plan integrates findings from 2 research reports created on 2026-01-08:

**Research Report 001** (research-001.md):
- Analyzed source LaTeX structure (1452 lines) and mapped to Logos Core components
- Identified 5 major components: Syntax, Semantics, ProofSystem, Metalogic, Theorems
- Specified content extraction rules: include definitions/axioms/theorems, exclude problem sets/proofs/Fitch
- Designed subfile architecture with 6 subfiles (00-Introduction through 05-Theorems)
- Specified LaTeX macro extensions for task frames, models, truth conditions
- Recommended semi-automated extraction with manual review

**Research Report 002** (research-002.md):
- Analyzed LAYER_EXTENSIONS.md for future Layer 1 (Explanatory Extension) content
- Clarified layer terminology: Constitutive and Causal operators are Layer 1, not Layer 0
- Recommended semantic progression introduction explaining how layers build incrementally
- Specified LaTeX macros for Layer 1 operators (to be added when Layer 1 implemented)

**Key Integration Points**:
- Focus on Layer 0 (Core TM) only for current implementation
- Prepare structure to accommodate future Layer 1-3 extensions
- Add semantic progression subsection to introduction
- Use Logos implementation terminology (Layer 0/1/2/3) consistently

## Goals and Non-Goals

### Goals

1. Create readable LaTeX reference for Layer 0 (Core TM logic)
2. Mirror Logos layer architecture in documentation structure
3. Extract and reorganize content from LogicNotes.tex
4. Provide clear definitions without pedagogical overhead
5. Enable independent compilation of each component subfile
6. Establish foundation for future layer documentation

### Non-Goals

1. Document Layer 1-3 extensions (future work)
2. Create new mathematical content or proofs
3. Automate PDF generation pipeline
4. Modify Lean source code
5. Translate to HTML or other formats
6. Include pedagogical examples or exercises

## Risks and Mitigations

### Risk 1: LaTeX Compilation Errors

**Likelihood**: Medium  
**Impact**: High (blocks PDF generation)

**Mitigation**:
- Compile each subfile independently during generation
- Test all new macros in logos-notation.sty before use
- Keep source LaTeX as reference for correct syntax
- Use validation script to check for common errors

### Risk 2: Mathematical Notation Inconsistency

**Likelihood**: Medium  
**Impact**: Medium (confusing to readers)

**Mitigation**:
- Review all mathematical notation in extracted content
- Define all symbols in logos-notation.sty
- Verify notation matches Lean source
- Maintain glossary of all notation used

### Risk 3: Content Omission or Duplication

**Likelihood**: Low  
**Impact**: Medium (incomplete or redundant documentation)

**Mitigation**:
- Maintain explicit mapping of source lines to target subfiles
- Verify all required definitions included
- Ensure no content appears in multiple subfiles
- Manual review of all subfiles for completeness

## Implementation Phases

### Phase 1: Setup and Infrastructure [NOT STARTED]

**Estimated Effort**: 1.5 hours

**Objectives**:
- Create target directory structure
- Copy and test source style files
- Create logos-notation.sty with Logos-specific macros
- Create main document with subfile architecture
- Validate compilation with empty subfiles

**Tasks**:
1. Create directory structure:
   ```
   Documentation/LaTeX/
   ├── LogosReference.tex
   ├── subfiles/
   ├── assets/
   ├── bibliography/
   └── build/
   ```

2. Copy source assets to Documentation/LaTeX/assets/:
   - formatting.sty (from /home/benjamin/Projects/Philosophy/Teaching/LogicNotes/assets/)
   - notation.sty (from source)
   - bib_style.bst (from source)
   - glossary.tex (from source)

3. Create logos-notation.sty with macros:
   - Task frame notation: \taskframe, \worldstateset, \Tor, \taskrel, \worldhist
   - Task model notation: \taskmodel, \valuation
   - Truth and validity notation: \truthat, \TMmodels, \TMproves
   - Lean cross-reference notation: \leansrc, \leandef
   - Axiom labels: \axiomK, \axiomS, \axiomMT, \axiomMfour, \axiomMB, \axiomMK, \axiomTK, \axiomTfour, \axiomTA, \axiomTL, \axiomMF, \axiomTF
   - Perpetuity principles: \Pone, \Ptwo, \Pthree, \Pfour, \Pfive, \Psix

4. Create main document LogosReference.tex:
   - Document class: article, a4paper, 11pt
   - Packages: geometry, microtype, subfiles, formatting, notation, logos-notation
   - Title: "Logos Reference: Bimodal Logic TM"
   - Author: Benjamin Brast-McKie
   - Subfile includes (commented out initially)
   - Bibliography setup

5. Create empty subfile templates with proper headers:
   - 00-Introduction.tex
   - 01-Syntax.tex
   - 02-Semantics.tex
   - 03-ProofSystem.tex
   - 04-Metalogic.tex
   - 05-Theorems.tex

6. Test compilation:
   - Compile main document with empty subfiles
   - Verify no LaTeX errors
   - Verify style files load correctly

**Acceptance Criteria**:
- [ ] Directory structure created
- [ ] All source style files copied
- [ ] logos-notation.sty created with all required macros
- [ ] Main document compiles successfully
- [ ] All 6 empty subfiles compile independently
- [ ] No LaTeX errors or warnings

**Validation**:
```bash
cd Documentation/LaTeX
pdflatex LogosReference.tex
for file in subfiles/*.tex; do pdflatex "$file"; done
```

---

### Phase 2: Content Extraction and Subfile Generation [NOT STARTED]

**Estimated Effort**: 3 hours

**Objectives**:
- Extract relevant content from LogicNotes.tex
- Generate all 6 subfiles with extracted content
- Add standardized sections to each subfile
- Insert Lean cross-references
- Ensure each subfile compiles independently

**Tasks**:

**2.1 Generate 00-Introduction.tex** (30 min):
- Overview of Logos TM logic
- Perpetuity intuitions (extract from LogicNotes.tex lines 1099-1123)
- Layer architecture description
- Semantic progression subsection (from research-002.md)
- Relationship to Lean implementation
- Reading guide
- Length: 2-3 pages

**2.2 Generate 01-Syntax.tex** (30 min):
- Language definition (BL = ⟨SL, ⊥, →, □, H, G⟩)
- Well-formed formulas (inductive definition from lines 1124-1140)
- Derived operators (negation, conjunction, disjunction, diamond, some_past, some_future, always, sometimes)
- Scope conventions
- Extensions from Propositional Logic (added: □, H, G)
- Extensions from Modal Logic (added: H, G)
- Extensions from Temporal Logic (added: □)
- Lean cross-reference: \leansrc{Logos.Core.Syntax}{Formula}
- Length: 3-4 pages

**2.3 Generate 02-Semantics.tex** (30 min):
- Task frames (F = ⟨W, T, ·⟩ from lines 1177-1185)
- World histories (τ: X → W from lines 1186-1195)
- Task models (M = ⟨W, T, ·, ⟦·⟧⟩ from lines 1196-1200)
- Truth conditions (M, τ, x ⊨ φ from lines 1201-1210)
- Validity (⊨_TM φ from lines 1211-1214)
- Extensions from previous layers
- Lean cross-references: \leansrc{Logos.Core.Semantics}{TaskFrame}, {TaskModel}, {Truth}, {Validity}
- Length: 4-5 pages

**2.4 Generate 03-ProofSystem.tex** (30 min):
- Propositional axioms (K, S from lines 323-360)
- Modal axioms (MT, M4, MB, M5, MK from lines 471-557)
- Temporal axioms (TK, T4, TA, TL from lines 965-1026)
- Modal-temporal interaction axioms (MF, TF from lines 1238-1250)
- Inference rules (Modus Ponens, Necessitation, Temporal Necessitation)
- Derivability (Γ ⊢_TM φ definition)
- Extensions from previous layers
- Lean cross-references: \leansrc{Logos.Core.ProofSystem}{Axioms}, {Derivation}
- Length: 4-5 pages

**2.5 Generate 04-Metalogic.tex** (30 min):
- Soundness (if Γ ⊢_TM φ then Γ ⊨_TM φ) - PROVEN in Lean
- Completeness (if Γ ⊨_TM φ then Γ ⊢_TM φ) - infrastructure only
- Deduction theorem (Γ, φ ⊢ ψ iff Γ ⊢ φ → ψ) - PROVEN in Lean
- Decidability - not established
- Characterization (TM system characterized by task frame constraints)
- Established properties summary
- Lean cross-references: \leansrc{Logos.Core.Metalogic}{Soundness}, {Completeness}, {DeductionTheorem}
- Length: 2-3 pages

**2.6 Generate 05-Theorems.tex** (30 min):
- Propositional theorems (from Propositional.lean)
- Modal S4 theorems (from ModalS4.lean)
- Modal S5 theorems (from ModalS5.lean)
- Perpetuity principles P1-P6 (from lines 1251-1263):
  - P1: □φ → △φ (Necessity implies always) - PROVEN
  - P2: ▽φ → ◇φ (Sometimes implies possibility) - PROVEN
  - P3: □φ → □△φ (Necessity of perpetuity) - PROVEN
  - P4: ◇▽φ → ◇φ (Possibility of occurrence) - PROVEN
  - P5: ◇▽φ → △◇φ (Persistent possibility) - PROVEN
  - P6: ▽□φ → □△φ (Occurrent necessity is perpetual) - PROVEN
- Derived results (from Theorems/ directory)
- Lean cross-references: \leansrc{Logos.Core.Theorems.Perpetuity}{Principles}, {Bridge}
- Length: 3-4 pages

**Content Extraction Rules**:
- **Include**: All definition environments, axiom schemata, theorem statements, semantic clauses, validity definitions
- **Exclude**: All problem sets (sections with \it Problem Set), all proofs (fitch environments, proof blocks), all Fitch natural deduction (lines 117-270)
- **Transform**: Reorder content by Logos layer component, add "Extensions from previous layer" sections

**Acceptance Criteria**:
- [ ] All 6 subfiles generated with content
- [ ] Standardized sections added to each subfile
- [ ] Lean cross-references inserted (20-30 total)
- [ ] Each subfile compiles independently
- [ ] Mathematical notation consistent
- [ ] Formatting follows source standards

**Validation**:
```bash
for file in subfiles/*.tex; do
  pdflatex "$file"
  if [ $? -ne 0 ]; then
    echo "ERROR: $file failed to compile"
  fi
done
```

---

### Phase 3: Integration and Validation [NOT STARTED]

**Estimated Effort**: 1 hour

**Objectives**:
- Compile full document and verify formatting
- Validate all cross-references
- Check mathematical notation consistency
- Proofread definitions and theorem statements
- Generate final PDF

**Tasks**:
1. Compile full document:
   - Uncomment all \subfile{} includes in LogosReference.tex
   - Run pdflatex LogosReference.tex
   - Verify no compilation errors
   - Check for undefined references

2. Validate cross-references:
   - Verify all \leansrc{} references point to existing Lean files
   - Check that Lean file paths are correct
   - Test cross-references by opening Lean files

3. Check notation consistency:
   - Verify all modal operators defined (□, ◇)
   - Verify all temporal operators defined (H, G, P, F, △, ▽)
   - Verify all propositional operators defined (¬, ∧, ∨, →, ↔)
   - Verify all semantic notation defined (⊨, ⊨_TM, ⊢, ⊢_TM)
   - Verify all frame notation defined (F, W, T, ·, τ, H_F)
   - Verify all model notation defined (M, ⟦·⟧)

4. Proofread definitions:
   - Check all definition labels use \item[\bf Label:] format
   - Verify all abbreviations use \coloneq notation
   - Check all metavariables use \metaA, \metaB, \metaC
   - Verify all section headers use \section*{\sc Title} format

5. Generate final PDF:
   - Run pdflatex LogosReference.tex twice (for cross-references)
   - Run bibtex LogosReference (for bibliography)
   - Run pdflatex LogosReference.tex twice more
   - Move PDF to build/LogosReference.pdf

6. Final review:
   - Read through entire PDF
   - Check page layout and formatting
   - Verify table of contents
   - Check bibliography entries
   - Verify all figures/tables render correctly

**Acceptance Criteria**:
- [ ] Full document compiles without errors
- [ ] All cross-references validated
- [ ] Notation consistent throughout
- [ ] All definitions proofread
- [ ] Final PDF generated in build/
- [ ] PDF reviewed and approved

**Validation**:
```bash
cd Documentation/LaTeX
pdflatex LogosReference.tex
bibtex LogosReference
pdflatex LogosReference.tex
pdflatex LogosReference.tex
mv LogosReference.pdf build/
ls -lh build/LogosReference.pdf
```

---

### Phase 4: Documentation and Cleanup [NOT STARTED]

**Estimated Effort**: 0.5 hours

**Objectives**:
- Create README.md for LaTeX documentation
- Document usage instructions
- Clean up temporary files
- Validate final deliverables

**Tasks**:
1. Create README.md:
   - Overview of LaTeX documentation structure
   - Compilation instructions
   - Subfile descriptions
   - Maintenance guidelines
   - Future extension notes

2. Clean up temporary files:
   - Remove .aux, .log, .out, .toc files
   - Keep only source .tex files and final PDF
   - Verify build/ directory contains only PDF

3. Validate deliverables:
   - Verify all required files present
   - Check file sizes reasonable
   - Test compilation from clean state

4. Document any deviations:
   - Note any content omissions
   - Document any formatting adjustments
   - List any known issues

**Acceptance Criteria**:
- [ ] README.md created with usage instructions
- [ ] Temporary files cleaned up
- [ ] All deliverables validated
- [ ] Deviations documented

**Validation**:
```bash
ls -R Documentation/LaTeX/
# Should show clean directory structure
```

---

## Testing and Validation

### Unit Testing
- Each subfile compiles independently without errors
- All LaTeX macros defined and render correctly
- Mathematical notation consistent within each subfile

### Integration Testing
- Full document compiles with all subfiles included
- Cross-references between subfiles resolve correctly
- Bibliography entries render correctly
- Table of contents generates correctly

### Validation Checklist

**Content Completeness** (8 items):
- [ ] All syntax definitions included
- [ ] All semantic definitions included
- [ ] All proof system definitions included
- [ ] All metalogical definitions included
- [ ] All theorem statements included
- [ ] All problem sets excluded
- [ ] All proofs excluded
- [ ] All Fitch content excluded

**Standardized Sections** (5 items):
- [ ] 01-Syntax.tex has "Extensions from Previous Layer" sections
- [ ] 02-Semantics.tex has "Semantic Frames and Models Definitions" section
- [ ] 03-ProofSystem.tex has "Proof System Extensions from Previous Layer" sections
- [ ] 04-Metalogic.tex has "Metalogical Properties" section
- [ ] 05-Theorems.tex has perpetuity principles P1-P6

**Formatting** (6 items):
- [ ] All section headers use \section*{\sc Title} format
- [ ] All definitions use \begin{enumerate}[leftmargin=1.2in] format
- [ ] All definition labels use \item[\bf Label:] format
- [ ] All abbreviations use \coloneq notation
- [ ] All mathematical notation consistent with source
- [ ] All metavariables use \metaA, \metaB, \metaC

**Cross-References** (4 items):
- [ ] All major definitions have Lean cross-references
- [ ] All cross-references use \leansrc{Module}{Definition} format
- [ ] All cross-references point to correct Lean files
- [ ] All cross-references render correctly in PDF

**Compilation** (5 items):
- [ ] Main document compiles without errors
- [ ] Each subfile compiles independently without errors
- [ ] All style files load correctly
- [ ] All macros defined and used correctly
- [ ] PDF renders correctly with proper formatting

**Requirements Validation** (8 items):
- [ ] Documentation mirrors Logos layer structure
- [ ] Subfile created for each Logos layer component
- [ ] Same formatting standards as original maintained
- [ ] Problem sets excluded
- [ ] Standardized sections included for each layer
- [ ] Definitions compiled clearly and concisely without proofs
- [ ] Minimal explanation provided
- [ ] Serves as readable LaTeX reference without Lean code

## Artifacts and Outputs

### Primary Artifacts
1. **LogosReference.tex**: Main document with subfile architecture
2. **subfiles/00-Introduction.tex**: Overview and motivation (2-3 pages)
3. **subfiles/01-Syntax.tex**: Language and formulas (3-4 pages)
4. **subfiles/02-Semantics.tex**: Frames, models, truth, validity (4-5 pages)
5. **subfiles/03-ProofSystem.tex**: Axioms, rules, derivability (4-5 pages)
6. **subfiles/04-Metalogic.tex**: Soundness, completeness, characterization (2-3 pages)
7. **subfiles/05-Theorems.tex**: Key theorems and perpetuity principles (3-4 pages)
8. **assets/logos-notation.sty**: Logos-specific LaTeX macros
9. **build/LogosReference.pdf**: Compiled final document (18-23 pages)

### Supporting Artifacts
1. **assets/formatting.sty**: Copied from source
2. **assets/notation.sty**: Copied from source
3. **assets/bib_style.bst**: Copied from source
4. **assets/glossary.tex**: Copied from source
5. **bibliography/LogosReferences.bib**: Bibliography entries
6. **README.md**: Documentation guide for LaTeX reference

## Rollback/Contingency

### Rollback Triggers
- LaTeX compilation fails with unresolvable errors
- Content extraction reveals major gaps in source material
- Style file incompatibilities cannot be resolved
- Timeline exceeds 8 hours (33% over estimate)

### Rollback Procedure
1. Document specific failure point and error messages
2. Preserve all work in progress in separate branch
3. Revert to clean state (no LaTeX directory)
4. Create detailed issue report with:
   - Specific errors encountered
   - Attempted solutions
   - Recommendations for alternative approach
5. Consult with stakeholders on revised approach

### Contingency Plans

**If LaTeX compilation fails**:
- Simplify macro definitions in logos-notation.sty
- Use standard LaTeX commands instead of custom macros
- Test with minimal document first, add complexity incrementally

**If content extraction is incomplete**:
- Prioritize core definitions (syntax, semantics, proof system)
- Defer metalogic and theorems to future iteration
- Document gaps for follow-up work

**If style file incompatibilities arise**:
- Create simplified versions of style files
- Use only essential formatting from source
- Document required manual formatting adjustments

## Success Metrics

### Quantitative Metrics
- [ ] All 6 subfiles compile independently (100% success rate)
- [ ] Full document compiles without errors (0 LaTeX errors)
- [ ] 20-30 Lean cross-references validated (100% accuracy)
- [ ] 36 checklist items completed (100% completion)
- [ ] Final PDF 18-23 pages (within target range)
- [ ] Implementation time ≤ 6 hours (within estimate)

### Qualitative Metrics
- [ ] Documentation is readable without Lean expertise
- [ ] Definitions are clear and concise
- [ ] Mathematical notation is consistent
- [ ] Formatting matches source standards
- [ ] Structure mirrors Logos layer architecture
- [ ] Document serves as effective reference

### Acceptance Criteria
- All quantitative metrics met
- All qualitative metrics assessed as satisfactory
- Stakeholder review and approval
- No critical issues identified in final review

## Notes

### Implementation Strategy
- Use semi-automated extraction with manual review
- Compile incrementally (test each subfile as generated)
- Prioritize correctness over speed
- Document any deviations from source

### Future Extensions
- Layer 1 (Explanatory Extension) subfiles when implemented
- Layer 2 (Epistemic Extension) subfiles when implemented
- Layer 3 (Normative Extension) subfiles when implemented
- Automated PDF generation pipeline
- HTML version for web documentation

### Related Tasks
- Task 139: Draft Layer 1 counterfactual operator plan
- Task 140: Draft Layer 2 epistemic operator plan
- Future: Implement Layer 1-3 in Lean
- Future: Create automated documentation generation

---

**Plan Version**: 2  
**Last Updated**: 2026-01-08  
**Next Review**: After Phase 1 completion
