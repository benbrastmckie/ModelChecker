# Implementation Plan: Task #5

- **Task**: 5 - logos_spatial_readme
- **Status**: [COMPLETED]
- **Effort**: 2 hours
- **Dependencies**: None
- **Research Inputs**: specs/005_logos_spatial_readme/reports/research-001.md
- **Artifacts**: plans/implementation-001.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: general
- **Lean Intent**: false

## Overview

Create a comprehensive README.md for the spatial reasoning subtheory within the logos theory library. The README will document the state-valued metric function primitive, five essential frame constraints, and derived concepts (located states, located parts, internal geometry, spatial profiles). Content will be synthesized from the Logos Theory spatial chapter (06-spatial.typ) while conforming to established subtheory README patterns from the constitutive and modal subtheories.

### Research Integration

Research report (research-001.md) identified:
- Single primitive: metric function `~` with type signature S -> Q -> S -> S
- Five essential frame constraints (A1-A5): extension, reflexivity, symmetry, triangularity, exclusion
- Key derived concepts: located states, located parts, n-balls, internal geometry, spatial profiles
- Standard README structure from existing subtheories
- Dependencies: extensional, constitutive, and modal subtheories

## Goals & Non-Goals

**Goals**:
- Create README.md matching repo documentation standards (constitutive README as template)
- Document the metric function primitive with type signature and semantics
- Explain five essential frame constraints with interpretations
- Define key derived concepts with mathematical notation
- Describe integration with existing logos framework
- Include appropriate academic references

**Non-Goals**:
- Implementing the spatial operators in Python/Z3 (operators.py not yet created)
- Creating example files or test suites
- Writing the full operators.py implementation details
- Documenting Python API (deferred to implementation task)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| README references non-existent code | M | H | Mark subtheory as "planned" status, note operators.py pending |
| Mathematical notation inconsistent with Typst source | M | M | Cross-reference 06-spatial.typ carefully for notation |
| Missing dependencies unclear | L | L | Research identified deps (extensional, constitutive, modal) |

## Implementation Phases

### Phase 1: Create README Structure and Header [COMPLETED]

**Goal**: Establish the file structure following constitutive README pattern

**Tasks**:
- [ ] Create README.md with navigation header links
- [ ] Add directory structure section (noting planned components)
- [ ] Write overview section (2-3 paragraphs introducing spatial extension)
- [ ] Add subdirectories placeholder (notebooks/, tests/ - planned)
- [ ] Include documentation section stubs (For New Users, Researchers, Developers)

**Timing**: 30 minutes

**Files to modify**:
- `Code/src/model_checker/theory_lib/logos/subtheories/spatial/README.md` - create content

**Verification**:
- README has proper navigation links
- Directory structure accurately reflects current/planned state
- Overview clearly explains spatial extension purpose

---

### Phase 2: Document Primitives and Frame Constraints [COMPLETED]

**Goal**: Translate the core theoretical content from 06-spatial.typ

**Tasks**:
- [ ] Create "Primitive Reference" section with metric function
- [ ] Document type signature: `~ : S -> Q -> S -> S`
- [ ] Add metric state notation: `(a ~_n b)`
- [ ] Document five frame constraints (A1-A5) in table format
- [ ] Include interpretations for each constraint (extension, reflexivity, symmetry, triangularity, exclusion)

**Timing**: 45 minutes

**Files to modify**:
- `Code/src/model_checker/theory_lib/logos/subtheories/spatial/README.md` - add primitives section

**Verification**:
- All five frame constraints accurately documented
- Mathematical notation consistent with source material
- Constraint interpretations clear and accurate

---

### Phase 3: Document Derived Concepts [COMPLETED]

**Goal**: Explain the derived spatial concepts with definitions

**Tasks**:
- [ ] Define located states (states where self-distance is possible)
- [ ] Define located parts Loc(s) with formal notation
- [ ] Define n-ball B_n^s(a) around a point
- [ ] Define internal geometry g_s function
- [ ] Define spatial profile Pi(s,t) with realization condition
- [ ] Explain hyperintensional character of spatial reasoning

**Timing**: 30 minutes

**Files to modify**:
- `Code/src/model_checker/theory_lib/logos/subtheories/spatial/README.md` - add derived concepts section

**Verification**:
- All derived concepts from research report covered
- Definitions match 06-spatial.typ source
- Hyperintensional aspects explained

---

### Phase 4: Add Integration, Dependencies, and References [COMPLETED]

**Goal**: Complete README with integration guidance and academic references

**Tasks**:
- [ ] Add dependencies section (extensional, constitutive, modal subtheories)
- [ ] Note integration with existing logos framework
- [ ] Add implementation status section (mark as "planned")
- [ ] Include implementation challenges from research (ternary operators, distance values, triangle inequality)
- [ ] Add references section with primary sources
- [ ] Add footer navigation links

**Timing**: 15 minutes

**Files to modify**:
- `Code/src/model_checker/theory_lib/logos/subtheories/spatial/README.md` - add final sections

**Verification**:
- Dependencies accurately listed
- Implementation status clear
- References include Logos Theory source
- Navigation links functional

## Testing & Validation

- [ ] README follows constitutive README structure pattern
- [ ] All five frame constraints (A1-A5) documented
- [ ] All derived concepts (located states, located parts, n-ball, internal geometry, spatial profile) defined
- [ ] Mathematical notation consistent with 06-spatial.typ source
- [ ] Implementation status clearly marked as "planned"
- [ ] Navigation links present and accurate

## Artifacts & Outputs

- `Code/src/model_checker/theory_lib/logos/subtheories/spatial/README.md` - Main deliverable
- `specs/005_logos_spatial_readme/summaries/implementation-summary-20260228.md` - Completion summary

## Rollback/Contingency

If implementation fails:
- The existing empty README.md can be restored from git
- Partial content can be committed incrementally per phase
- Source material (06-spatial.typ) remains available for re-synthesis
