# Research Report: Task #27 (Alternative Analysis)

**Task**: 27 - Flatten code/src/ directory structure
**Version**: 002
**Started**: 2026-03-03T14:00:00Z
**Completed**: 2026-03-03T14:45:00Z
**Effort**: Medium (research and analysis)
**Dependencies**: None
**Sources/Inputs**: Codebase directory structure analysis
**Artifacts**: This research report (second version - alternative focus)
**Standards**: report-format.md

## Executive Summary

- **Previous research** (research-027.md) correctly identified that flattening `code/src/model_checker/` to `code/src/` is HIGH RISK and not recommended
- **This research** explores alternative flattening opportunities within the existing package structure
- **7 candidate areas** identified with varying risk/benefit profiles
- **2 LOW-RISK opportunities** identified as actionable: cleanup of generated checkpoints and consolidation of embedded specs
- **Deepest nesting**: 9 levels in logos/subtheories (notebooks/.ipynb_checkpoints)

## Context & Scope

This research pivots from the original task to identify directories that could be safely flattened or reorganized without breaking the Python package structure.

### Directory Depth Analysis

From project root (`/home/benjamin/Projects/ModelChecker`):

| Depth | Count | Example Path |
|-------|-------|--------------|
| 9 levels | 6 dirs | `code/src/model_checker/theory_lib/logos/subtheories/*/notebooks/.ipynb_checkpoints` |
| 8 levels | 15 dirs | `code/src/model_checker/theory_lib/logos/subtheories/*/tests` |
| 7 levels | 40+ dirs | `code/src/model_checker/theory_lib/*/tests/unit` |
| 6 levels | 50+ dirs | `code/src/model_checker/*/tests/unit` |

## Findings

### Candidate 1: .ipynb_checkpoints Directories (CLEANUP)

**Current depth**: 9 levels (deepest in codebase)
**Location**: 7 directories across theory_lib
**Example**: `theory_lib/logos/subtheories/relevance/notebooks/.ipynb_checkpoints`

**Assessment**:
- These are Jupyter auto-generated checkpoint files
- Already in `.gitignore` (`*.ipynb_checkpoints`)
- **Action**: DELETE - these are local artifacts, not project content
- **Risk**: NONE - these should not exist in a clean clone
- **Benefit**: Removes 7 deepest directories

### Candidate 2: Embedded specs/ Directories (CONSIDER CONSOLIDATION)

**Current depth**: 7-8 levels
**Locations**:
- `theory_lib/specs/` (plans, prompts, reports)
- `theory_lib/bimodal/specs/` (cvc5 phases, plans, reports)

**Contents**:
```
theory_lib/specs/
├── plans/
├── prompts/
├── reports/
└── subagent-refactoring-guide.md

theory_lib/bimodal/specs/cvc5/
├── MASTER_PLAN.md
├── phase1_pilot/
├── phase2_abstraction/
└── phase3_integration/
```

**Assessment**:
- These are development artifacts embedded in source tree
- The cvc5/ subdirectory adds 3 extra levels (phase1_pilot, etc.)
- **Action**: Could relocate to project-level `specs/` with task references
- **Risk**: LOW - no import dependencies, pure documentation
- **Benefit**: Reduces source tree depth by 3-4 levels, centralizes planning docs

### Candidate 3: logos/subtheories/ Structure (HIGH RISK - NOT RECOMMENDED)

**Current depth**: 7 levels for source, 8-9 for tests/notebooks
**Scale**: 7 subtheories (constitutive, counterfactual, extensional, first-order, modal, relevance, spatial)
**Python files**: 38
**Notebooks**: 10

**Structure per subtheory**:
```
subtheories/{name}/
├── __init__.py
├── operators.py
├── examples.py
├── tests/
│   ├── __init__.py
│   └── test_{name}_examples.py
└── notebooks/ (optional)
    └── {name}_examples.ipynb
```

**Assessment**:
- The `subtheories/` level IS semantically meaningful (these extend logos)
- Moving to `theory_lib/logos_{subtheory}/` would flatten by 1 level but create namespace pollution
- **Action**: KEEP AS IS - the nesting reflects actual code organization
- **Risk**: HIGH if changed - import paths like `from ...logos.subtheories.modal import` would break
- **Benefit**: Minimal (1 level) vs effort required

### Candidate 4: Embedded Test Directories (ARCHITECTURAL CONSIDERATION)

**Current pattern**: Tests embedded in source packages
**Scale**: 204 test files embedded in `code/src/model_checker/**/tests/`
**Contrast**: 36 test files in `code/tests/`

**Structure**:
```
module/
├── __init__.py
├── core.py
└── tests/
    ├── __init__.py
    ├── unit/
    ├── integration/
    ├── fixtures/
    └── e2e/
```

**Assessment**:
- This is a deliberate architectural choice (tests co-located with modules)
- Moving tests to `code/tests/` would flatten source tree but:
  - Lose locality (tests near code they test)
  - Create massive test directory (200+ files)
  - Break relative test imports
- **Action**: KEEP AS IS - this is a valid Python testing pattern
- **Risk**: HIGH if changed
- **Benefit**: Would reduce source depth but at significant cost

### Candidate 5: semantic/ Subdirectories (MIXED)

**Locations**:
- `theory_lib/exclusion/semantic/` - 4 Python files
- `theory_lib/imposition/semantic/` - 4 Python files
- `theory_lib/bimodal/semantic/` - 2 Python files

**Assessment**:
- These split large semantic.py files into modules
- exclusion and imposition also have `semantic.py` at parent level (wrapper)
- Could potentially merge back into single files
- **Action**: INVESTIGATE FURTHER - may be intentional refactoring
- **Risk**: MEDIUM - would affect imports within theories
- **Benefit**: Minimal depth reduction (1 level)

### Candidate 6: reports/imposition_comparison/ (LOW VALUE)

**Current depth**: 8 levels
**Location**: `theory_lib/imposition/reports/imposition_comparison/data/`
**Contents**: Research artifacts (frame_constraints.md, modals_defined.md)

**Assessment**:
- Small, isolated directory
- Could relocate to project-level specs or flatten
- **Action**: LOW PRIORITY - affects very few files
- **Risk**: LOW
- **Benefit**: Minimal

### Candidate 7: output/notebook/templates/ (KEEP)

**Current depth**: 7 levels
**Contents**: Python template modules (base.py, logos.py, etc.)

**Assessment**:
- These are actual Python modules, not just templates
- The nesting reflects module organization
- **Action**: KEEP AS IS
- **Risk**: Would break imports
- **Benefit**: None

## Recommendations

### Immediate Actions (LOW RISK)

1. **Delete .ipynb_checkpoints directories**
   - Already gitignored, should not be in repo
   - Removes 7 directories at max depth
   - Command: `find code/src -name ".ipynb_checkpoints" -type d -exec rm -rf {} +`

### Consider for Future (MEDIUM RISK)

2. **Consolidate embedded specs/ to project-level specs/**
   - Move `theory_lib/specs/` content to `specs/theory_lib/`
   - Move `theory_lib/bimodal/specs/` to `specs/bimodal/`
   - Reduces source tree depth by 4 levels
   - No import breakage (pure documentation)

### Do Not Pursue (HIGH RISK)

3. **Do NOT flatten subtheories/** - semantic organization is correct
4. **Do NOT move embedded tests/** - co-location is intentional
5. **Do NOT change semantic/ subdirectories** without deeper analysis

## Depth Comparison Summary

| Area | Current Depth | After Cleanup | After Consolidation |
|------|---------------|---------------|---------------------|
| .ipynb_checkpoints | 9 | N/A (deleted) | N/A |
| bimodal/specs/cvc5/phase* | 8 | 8 | 5 (if moved) |
| subtheories/*/tests | 8 | 8 | 8 (keep) |
| theory_lib/*/tests/unit | 7 | 7 | 7 (keep) |

## Alternative Task Recommendations

Given the original task goal of "reducing directory depth," consider these alternative tasks:

1. **Task: Clean generated artifacts from source tree**
   - Delete .ipynb_checkpoints (should be in .gitignore)
   - Risk: None
   - Effort: Trivial

2. **Task: Relocate development specs from source to project specs/**
   - Move theory_lib/specs/* and theory_lib/bimodal/specs/*
   - Update any documentation references
   - Risk: Low
   - Effort: Small

3. **Task: Review exclusion/history/ directory relevance**
   - Contains historical documentation (IMPLEMENTATION_STORY.md, etc.)
   - Could move to project-level docs/ if desired
   - Risk: Low
   - Effort: Trivial

## Questions for Stakeholder

1. **Is the goal depth reduction or cleanup?** The deepest directories are either gitignored artifacts or embedded specs
2. **Should embedded specs be consolidated?** Would centralize planning docs but separate them from code
3. **Is the subtheories/ organization intentional?** The depth reflects module hierarchy

## Appendix

### A. Complete Depth Analysis

```
# Directories at depth 8+ from model_checker root
8: theory_lib/logos/subtheories/*/notebooks/.ipynb_checkpoints (6 dirs)
8: theory_lib/logos/subtheories/first-order/tests/unit (1 dir)
7: theory_lib/bimodal/specs/cvc5/phase*/ (3 dirs)
7: theory_lib/imposition/reports/imposition_comparison/data (1 dir)
7: theory_lib/logos/subtheories/*/tests (7 dirs)
7: theory_lib/logos/subtheories/*/notebooks (6 dirs)
7: theory_lib/*/tests/unit (many)
```

### B. Commands Used

```bash
# Find deepest directories
find code/src/model_checker -type d | awk -F'/' '{print NF-6, $0}' | sort -rn | head -30

# Count Python files in subtheories
find code/src/model_checker/theory_lib/logos/subtheories -name "*.py" | wc -l

# Verify .ipynb_checkpoints is gitignored
cat .gitignore | grep ipynb
```

### C. File Counts

| Directory Type | Count |
|----------------|-------|
| .ipynb_checkpoints | 7 |
| Embedded tests/ dirs | 20+ |
| specs/ dirs in source | 2 |
| notebooks/ dirs | 8 |
| semantic/ subdirs | 3 |
