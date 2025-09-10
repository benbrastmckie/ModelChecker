# TODO

## Priority 1: Critical Path to v1.0 Release

### 1.1 Framework Refactoring Completion (HIGHEST PRIORITY)

**Current Status**: 2 of 7 packages meet 95% target
- builder: 92% (acceptable as exemplar, no action needed)
- models: 85% (NEEDS Phase 5)
- tests: 90% (NEEDS Phase 5)  
- iterate: 76% (NEEDS full refactor)
- output: 95%+ (COMPLETE ✅ with Plan 064 + 070)
- jupyter: 95% (COMPLETE ✅)
- settings: 78% (NEEDS full refactor)

- [ ] **Complete Plan 060 Framework Refactoring** - Achieve 95%+ compliance for all packages
  - [ ] **models/ package enhancement (Plan 061)** - NEEDS PHASE 5
    - Current: 85% → Target: 95%+ compliance
    - [x] Phase 1: Foundation Cleanup (completed)
    - [x] Phase 2: Error Handling (ModelError hierarchy created)
    - [x] Phase 3: Type Safety (comprehensive type hints added)
    - [x] Phase 4: Test Coverage (60 tests passing)
    - [ ] Phase 5: Enhanced compliance to reach 95%
      - [ ] Additional method complexity reduction
      - [ ] Complete test coverage (target 90%+)
      - [ ] Full documentation update
  - [ ] **tests/ package enhancement (Plan 062)** - NEEDS PHASE 5
    - Current: 90% → Target: 95%+ compliance
    - [x] Phase 1: Test Organization (directory structure created)
    - [x] Phase 2: Method Refinement (utilities extracted)
    - [x] Phase 3: Error Handling (85 edge case tests added)
    - [x] Phase 4: Architectural Improvements (300+ tests)
    - [ ] Phase 5: Final enhancements to reach 95%
      - [ ] Complete fixture standardization
      - [ ] Enhanced parameterization patterns
      - [ ] Performance test expansion
  - [x] **jupyter/ package refactor (Plan 063)** - COMPLETE ✅
    - Current: 71% → Achieved: 95%+ compliance
    - [x] Phase 1: Foundation Cleanup (test structure, imports, docstrings)
    - [x] Phase 2: Method Refinement (ui_builders.py extracted)
    - [x] Phase 3: Error Handling (JupyterError hierarchy with 8 types)
    - [x] Phase 4: Comprehensive Tests (unit/integration/fixtures added)
    - [x] All tests passing, comprehensive coverage achieved
    - [x] **Manual Verification & Documentation** - COMPLETE ✅:
      - [x] Manually tested all Jupyter functionality with explicit examples
      - [x] Created comprehensive example notebooks for all theories:
        - [x] Logos subtheories: counterfactual, extensional, modal, constitutive, relevance
        - [x] Exclusion theory: witness negation examples
        - [x] Imposition theory: semantic examples
      - [x] Standardized all notebooks with professional formatting
      - [x] Removed all '\n' display issues
      - [x] Fixed all syntax errors
      - [x] Created consistent countermodel/theorem display patterns
      - [x] Updated all notebook README files with comprehensive documentation
  - [x] **output/ package refactor (Plan 064 + 070)** - COMPLETE ✅
    - Current: 72% → Achieved: 95%+ compliance
    - [x] Phase 1: Foundation (constants.py, errors.py, config.py created)
    - [x] Phase 2: Strategy Pattern (batch/sequential/interactive strategies)
    - [x] Phase 3: Formatter Pattern (markdown/json/notebook formatters)
    - [x] Phase 4: Manager Integration (OutputManager refactored)
    - [x] Phase 5: CLI Integration (--output flag with format selection)
    - [x] Phase 6: Documentation (comprehensive README.md files for all subdirectories)
    - [x] Cleanup: Removed 548+ lines of legacy code
    - [x] All tests passing (167 output tests, 218 builder tests)
    - [x] **Plan 071: Notebook Generation via --save jupyter** - COMPLETE ✅
      - [x] Issue: Generated notebooks didn't match reference notebook style/structure
      - [x] Problem Analysis: Data lost through intermediate formats, wrong cell structure
      - [x] Solution Design: Direct generation from examples.py using theory templates
      - [x] Plan: [071_notebook_generation_fix.md](Code/docs/specs/plans/071_notebook_generation_fix.md) - COMPLETED ✅
      - [x] Implementation completed but revealed architectural coupling issues
    - [x] **Plan 072: Complete Separation of Notebook Generation** - COMPLETE ✅
      - [x] Problem: Notebook generation coupled with JSON/markdown pipeline
      - [x] Solution: Independent notebook package working directly with module variables
      - [x] Plan: [072_notebook_generation_separation.md](Code/docs/specs/plans/072_notebook_generation_separation.md)
      - [x] Implementation Tasks:
        - [x] Phase 1: Create independent notebook generation path
        - [x] Phase 2: Create new notebook package structure
        - [x] Phase 3: Refactor templates for direct generation
        - [x] Phase 4: Remove notebook generation from OutputManager
        - [x] Phase 5: Update CLI flow
      - [x] Benefits Achieved:
        - [x] Complete separation from JSON serialization (no more serialization errors)
        - [x] Direct access to module variables (no data transformation)
        - [x] No intermediate data layers (works directly from examples.py)
        - [x] Simpler, cleaner architecture (notebook/ package independent from output/)
  - [ ] **iterate/ package refactor (Plan 065)** - MEDIUM PRIORITY (Week 3-4)
    - Current: 76% → Target: 95%+ compliance
    - [ ] Phase 1: Foundation Cleanup
    - [ ] Phase 2: Method Refinement (complex algorithms)
    - [ ] Phase 3: Error Handling (IterateError hierarchy)
    - [ ] Phase 4: Architectural Improvements
    - [ ] Phase 5: Complete Documentation & Testing (to reach 95%)
  - [ ] **settings/ package refactor (Plan 066)** - LOW PRIORITY (Week 5)
    - Current: 78% → Target: 95%+ compliance
    - [ ] Phase 1: Foundation Cleanup
    - [ ] Phase 2: Method Refinement
    - [ ] Phase 3: Error Handling (SettingsError hierarchy)
    - [ ] Phase 4: Architectural Improvements
    - [ ] Phase 5: Full Compliance Enhancement (to reach 95%)
  - [ ] **Success Validation**:
    - [ ] Achieve framework average compliance ≥95% (current: 78.6%)
    - [ ] All packages at 95%+ individual compliance
    - [ ] All tests passing throughout refactoring
    - [ ] Zero regression in functionality
    - [ ] Update all package documentation post-refactor

### 1.2 Witness Framework Abstraction (HIGH PRIORITY)

- [ ] **witness subpackage** - Abstract witness methodology/framework for reuse
  - [ ] Create abstract base framework for witness-based approaches
    - [ ] Define protocol for registering theory-specific witness predicates
    - [ ] Abstract pattern for witness constraint generation
    - [ ] Framework for witness-aware model evaluation
    - [ ] Generic witness predicate querying interface
  - [ ] Extract common methodological patterns (not specific predicates)
    - [ ] Registration pattern for witness functions
    - [ ] Constraint generation workflow
    - [ ] Model adaptation strategies
    - [ ] Witness evaluation protocols
  - [ ] Implement flexible framework that theories can customize
    - [ ] Allow theories to define their own witness predicates
    - [ ] Support different witness function signatures per theory
    - [ ] Enable theory-specific constraint patterns
  - [ ] Refactor exclusion/ to use the abstract framework
  - [ ] Adapt bimodal/ to use witness framework with bimodal-specific predicates
  - [ ] Document witness methodology patterns for future theories
  - [ ] Write framework tests that don't depend on specific predicates

## Priority 2: Essential Features & Quality

### 2.1 Documentation Consistency (CRITICAL FOR v1.0)

- [ ] **Bottom-Up Documentation Audit**
  - [ ] Phase 1: Audit lowest-level docs (test dirs, utils, helpers)
  - [ ] Phase 2: Package-level README updates and link verification  
  - [ ] Phase 3: Framework component documentation consistency
  - [ ] Phase 4: Top-level consolidation and redundancy removal
  - [ ] Phase 5: Comprehensive link testing and validation
  - [ ] Create documentation dependency graph to track relationships
  - [ ] Generate checklist of all documentation files for systematic review

### 2.2 Code Quality & Testing

- [ ] **linting and cleanup**
  - [ ] Remove unused imports in `/home/benjamin/Documents/Philosophy/Projects/ModelChecker/Code/src/model_checker/builder/example.py`
  - [ ] Run pylint systematically across entire codebase
  - [ ] Fix all critical and major issues

- [ ] **output formatting improvements**
  - [ ] Replace empty set braces '{}' with Unicode empty set symbol '∅' in countermodel outputs
    - [ ] Update output formatters to detect empty sets and use ∅ character
    - [ ] Ensure proper Unicode encoding for the empty set symbol
    - [ ] Test with various output formats (markdown, json, notebook)

- [ ] **unit test coverage**
  - [ ] Check coverage metrics (target 80%+)
  - [ ] Add missing test cases for new builder modules
  - [ ] Update test documentation

### 2.3 Theory Metadata & Documentation

- [ ] **theory metadata completion**
  - [ ] Add proper citations (logos/CITATION.md)
  - [ ] Implement versioning system
    - [ ] model_checker core versioning
    - [ ] Theory and subtheory versioning
    - [ ] Ensure project builder integrates properly
  - [ ] Complete license checking

## Priority 3: Theory Improvements

### 3.1 Bimodal Theory

- [ ] **bimodal optimization**
  - [ ] Implement witness framework with bimodal-specific predicates
    - [ ] Define bimodal witness functions (different from exclusion's)
    - [ ] Use abstract framework for registration and constraint generation
    - [ ] Adapt model evaluation for bimodal semantics
  - [ ] Complete infinite times refactor
  - [ ] Fix `print_over_times` to loop over all times
  - [ ] Remove/enforce `max_world_id`
  - [ ] Clean up frame constraints
  - [ ] Develop bimodal lambda-only strategy
  - [ ] Update PyPI documentation

### 3.2 Exclusion Theory

- [ ] **exclusion completion**
  - [ ] Move from complete lattice to boolean lattice
  - [ ] Compare with bilateral semantics
  - [ ] Update links to docs moved to `history/`
  - [ ] Integrate `TECHNICAL_REFERENCE.md` into `ARCHITECTURE.md`
  - [ ] Run performance comparisons:
    - [ ] Max atomic complexity `N` before timeout
    - [ ] Max sentence/atomic complexity before constraint overflow

### 3.3 Imposition Theory

- [ ] Complete `tests/README.md`
- [ ] Add missing standard files to `docs/` directory

### 3.4 Logos Theory (MAJOR EXPANSION PLANNED)

#### Immediate Tasks
- [ ] Consider witness framework adoption
  - [ ] Evaluate if Logos would benefit from witness predicates
  - [ ] Define Logos-specific witness functions if applicable
- [ ] Move iterate components out of semantic.py

#### Phase 1: Logos Restructuring into Logic Types (PREREQUISITE)
- [ ] **Pure Logic Implementation**
  - [ ] Create pure/ subdirectory structure
  - [ ] Implement individual operator logics with just intro/elim rules
    - [ ] Pure counterfactual logic
    - [ ] Pure modal logic
    - [ ] Pure relevance logic
    - [ ] Pure ground logic
    - [ ] Pure essence logic
  - [ ] Document theorems and countermodels for each pure logic
  - [ ] Create test suites for pure operator behaviors

- [ ] **Impure Logic Implementation**
  - [ ] Create impure/ subdirectory structure
  - [ ] Implement single non-extensional + classical combinations
    - [ ] Counterfactual + classical (defining other operators)
    - [ ] Modal + classical variations
    - [ ] Relevance + classical variations
  - [ ] Document derived operators and their relationships
  - [ ] Catalog theorems and countermodels for impure combinations

- [ ] **Interaction Logic Framework**
  - [ ] Create interaction/ subdirectory structure
  - [ ] Implement multi-operator combinations
    - [ ] Modal-counterfactual interactions
    - [ ] Relevance-ground interactions
    - [ ] Essence-counterfactual interactions
  - [ ] Document complex interaction patterns
  - [ ] Build comprehensive test coverage

#### Phase 2: Tense Operator Integration (MAJOR UNDERTAKING - POST-BIMODAL)
- [ ] **Prerequisites**
  - [ ] Complete bimodal theory implementation
  - [ ] Complete logos restructuring (Phase 1)
  - [ ] Adapt bimodal temporal methods for logos framework

- [ ] **Tense Operator Implementation**
  - [ ] Design tense operator semantics for truthmaker framework
    - [ ] Past operator (P)
    - [ ] Future operator (F)
    - [ ] Always past (H)
    - [ ] Always future (G)
  - [ ] Implement temporal accessibility relations
  - [ ] Add temporal frame constraints
  - [ ] Create temporal proposition evaluation

- [ ] **Pure Tense Logic**
  - [ ] Implement standalone tense logic in pure/
  - [ ] Document intro/elim rules
  - [ ] Catalog basic temporal theorems
  - [ ] Identify characteristic countermodels

- [ ] **Tense-Counterfactual Interaction Logic (CRITICAL)**
  - [ ] Create interaction/tense_counterfactual/ subdirectory
  - [ ] Implement combined temporal-counterfactual semantics
    - [ ] Past counterfactuals ("If it had been...")
    - [ ] Future counterfactuals ("If it will be...")
    - [ ] Temporal alternative selection
  - [ ] Document interaction patterns
    - [ ] Backtracking counterfactuals
    - [ ] Forward-tracking counterfactuals
    - [ ] Temporal rigidity constraints
  - [ ] Develop comprehensive theorem catalog
  - [ ] Build countermodel database for interactions
  - [ ] Create visualization tools for temporal-modal structures

- [ ] **Other Tense Interactions**
  - [ ] Tense-modal combinations
  - [ ] Tense-relevance interactions
  - [ ] Tense-ground relationships
  - [ ] Tense-essence connections

#### Phase 3: Integration and Testing
- [ ] **Unified Framework**
  - [ ] Ensure all logic types work within logos framework
  - [ ] Create consistent API across pure/impure/interaction
  - [ ] Implement logic type selection mechanism
  - [ ] Build cross-logic comparison tools

- [ ] **Documentation and Examples**
  - [ ] Create comprehensive documentation for each logic type
  - [ ] Build example notebooks for each combination
  - [ ] Document migration path from current logos structure
  - [ ] Create user guides for logic selection

## Priority 4: Framework Infrastructure

### 4.1 Subpackage Refactoring

- [ ] **jupyter** - Integrate with sequence output
- [ ] **models** - Extract as independent package
- [ ] **settings** - Simplify configuration system
- [ ] **syntactic** - Permit Unicode operators
- [ ] **utils** - Consolidate utility functions

### 4.2 Documentation Overhaul

- [ ] **Systematic Documentation Update (Bottom-Up Approach)**
  - [ ] **Level 1: Deepest Component Documentation** (Start Here)
    - [ ] Theory-specific test directories (e.g., `theory_lib/*/tests/README.md`)
    - [ ] Package utility modules (e.g., `builder/utils/`, `iterate/utils/`)
    - [ ] Fixture and helper directories
    - [ ] Check completeness, accuracy, and examples
  - [ ] **Level 2: Package/Module Documentation**
    - [ ] Individual package READMEs (`builder/README.md`, `models/README.md`, etc.)
    - [ ] Theory documentation (`theory_lib/logos/README.md`, etc.)
    - [ ] Test suite documentation (`tests/unit/README.md`, etc.)
    - [ ] Verify all internal links work
    - [ ] Remove redundant information covered at higher levels
  - [ ] **Level 3: Framework Component Documentation**
    - [ ] Main component READMEs (`src/model_checker/README.md`)
    - [ ] Cross-package documentation (`docs/specs/README.md`)
    - [ ] Maintenance standards (`maintenance/README.md`)
    - [ ] Ensure consistency across all packages
    - [ ] Verify cross-references between components
  - [ ] **Level 4: Top-Level Documentation**
    - [ ] Main `Code/README.md` for v1.0
    - [ ] Project-wide `Docs/README.md`
    - [ ] Installation and setup guides
    - [ ] Consolidate information, remove redundancy
    - [ ] Ensure all downward links are valid
  - [ ] **Documentation Quality Checks**
    - [ ] All relative links tested and working
    - [ ] No redundant information between levels
    - [ ] Consistent terminology throughout
    - [ ] Version numbers and dates updated
    - [ ] Code examples tested and working
    - [ ] File paths accurate and current
    - [ ] No orphaned documentation files
    - [ ] Cross-references bidirectional where appropriate

- [ ] **Legacy Documentation Tasks**
  - [ ] Complete methodology documentation
  - [ ] Update `/home/benjamin/Documents/Philosophy/Projects/ModelChecker/Docs/usage/WORKFLOW.md`
  - [ ] Update `/home/benjamin/Documents/Philosophy/Projects/ModelChecker/Docs/usage/COMPARE_THEORIES.md`
  - [ ] Revise `/home/benjamin/Documents/Philosophy/Projects/ModelChecker/Docs/theory/README.md`

### 4.3 Development Tools

- [ ] **iterate improvements**
  - [ ] Report when networkx not available
  - [ ] Make dependencies explicit
  - [ ] Update documentation for new builder structure
- [x] **jupyter verification and documentation** - COMPLETE ✅
  - [x] Manual testing with explicit examples:
    - [x] Created and tested comprehensive notebooks for all theories
    - [x] Verified all model checking functionality through notebooks
    - [x] Tested countermodel and theorem display functionality
    - [x] Validated all operator implementations across theories
  - [x] Created comprehensive tutorial documentation:
    - [x] Example notebooks serve as step-by-step guides for each theory
    - [x] Working code examples for countermodels and theorems
    - [x] Professional formatting with clear result interpretation sections
    - [x] Comprehensive README documentation for each notebook directory
  - [x] All existing examples verified working
  - [ ] Implement convenience methods (see `/home/benjamin/Documents/Philosophy/Projects/ModelChecker/Code/specs/CONV_METHODS.md`) - Future enhancement

## Priority 5: Future Enhancements

### 5.1 Additional Enhancements

### 5.2 Project Management

- [ ] Add comprehensive change log
- [ ] Create project wiki
- [ ] Decapitalize directory names for consistency

## Recently Completed (Since Last Update)

### Major Refactoring (COMPLETED)

- [x] **Builder refactor** - Successfully modularized from monolithic 1267-line file:
  - [x] Extracted into: runner.py, loader.py, validation.py, serialize.py, translation.py, etc.
  - [x] Created proper test structure (unit/, integration/, e2e/)
  - [x] Maintained iterate integration
  - [x] Preserved output formats
  - [x] Achieved 92% compliance (exemplar package)

- [x] **Iterate refactor** - Extracted from semantic.py into dedicated package:
  - [x] Created modular structure: base.py, core.py, iterator.py, models.py, etc.
  - [x] All theories now have iterate support
  - [x] Documentation updated
  - [x] Currently at 76% compliance (needs enhancement to 95%)

### Framework Refactoring Progress (NEEDS COMPLETION)

- [~] **models/ package refactor** - Phases 1-4 complete (85% compliance achieved, needs Phase 5 for 95%)
- [~] **tests/ package refactor** - Phases 1-4 complete (90% compliance achieved, needs Phase 5 for 95%)
- [x] **jupyter/ package refactor** - COMPLETE (95% compliance achieved ✅)
- [~] **output/ package refactor** - Needs notebook generation fix (see below)
- [ ] **iterate/ package refactor** - Not started (76% compliance, needs all phases for 95%)
- [ ] **settings/ package refactor** - Not started (78% compliance, needs all phases for 95%)

### Notebook Generation Refactor (URGENT)

**Problem**: Current notebook generation fails due to module import issues when trying to reload examples.py files.

**Solution**: Template-based approach (Plan 071)
- [ ] **Phase 1**: Modify BuildModule to pass example definitions through pipeline
- [ ] **Phase 2**: Extend NotebookTemplate base class with complete notebook methods
- [ ] **Phase 3**: Refactor NotebookGenerator to use templates only (no file reloading)
- [ ] **Phase 4**: Update OutputManager to collect and pass example data
- [ ] **Phase 5**: Update all theory templates to provide complete notebook structure

**Key Principles**:
- Templates in notebooks/ directories provide all imports and setup
- Example data flows through normal execution pipeline
- No absolute paths or module reloading
- Theory-agnostic output/ directory
- Each theory controls its own notebook format completely

### Theory Completions

- [x] All theories have docs/ directories (bimodal, exclusion, imposition, logos)
- [x] Exclusion semantics fully functional with witness predicates
- [x] Fixed exclusion falsify attribute error (inherits from LogosSemantics)
- [x] Reorganized EX_TH_2 to EX_CM_23 (disjunctive syllogism)

### Documentation & Standards

- [x] Added relative imports requirement to CODE_ORGANIZATION.md
- [x] Renamed pypi_link_requirements.md to PYPI_LINK_REQUIREMENTS.md
- [x] Updated maintenance/README.md with new standards
- [x] Added TEST_STATUS.md and TEST_ORGANIZATION.md

### Cleanup

- [x] Removed all output\_ directories
- [x] Fixed test expectations in exclusion theory

---

## Notes on Current State

**Progress Summary**: 
- Builder refactor: COMPLETE at 92% compliance (exemplar package, no further work needed)
- Jupyter refactor: COMPLETE at 95% compliance ✅
- Output refactor: COMPLETE at 95% compliance ✅
- Iterate extraction: COMPLETE but at 76% compliance (needs refactoring to 95%)
- Models package: Phases 1-4 done, stuck at 85% (needs Phase 5 for 95%)
- Tests package: Phases 1-4 done, stuck at 90% (needs Phase 5 for 95%)
- Settings package: Not started (78% compliance)

**Critical Path to v1.0**: Complete ALL packages to ≥95% compliance

**Immediate Priorities (in order)**:
1. **Fix notebook generation** - Template-based approach (Plan 071)
2. **Complete Phase 5 for models/** - Push from 85% to 95% compliance
3. **Complete Phase 5 for tests/** - Push from 90% to 95% compliance  
4. **Full refactor of iterate/** - Already extracted but needs 76% → 95%
5. **Full refactor of settings/** - Closest to target at 78%

**Success Criteria**: No package below 95% compliance (currently TWO packages meet this: jupyter and output)

**Secondary Priority**: The witness framework abstraction, which will:

1. Provide a general methodology for witness-based approaches
2. Allow each theory to define its own specific witness predicates
3. Create a reusable framework pattern without forcing theories to share predicates
4. Enable bimodal and exclusion to use the same framework with different witness functions

**Major Future Enhancement**: Logos Theory Expansion (Post-v1.0)

The logos theory will undergo a major restructuring and expansion:

1. **Restructuring into Logic Types**:
   - Pure logics: Individual operators with intro/elim rules only
   - Impure logics: Single non-extensional + classical operators
   - Interaction logics: Multiple non-extensional operator combinations

2. **Tense Operator Integration** (Major undertaking post-bimodal):
   - Adapt bimodal temporal methods to truthmaker framework
   - Implement P, F, H, G operators with temporal accessibility
   - Create critical tense-counterfactual interaction logic

3. **Tense-Counterfactual Interactions** (Especially important):
   - Past/future counterfactuals
   - Backtracking and forward-tracking patterns
   - Temporal rigidity constraints
   - Comprehensive theorem and countermodel catalogs

**Quality Focus**: With major refactoring done, focus shifts to:

- Code quality (linting, unused imports)
- Test coverage improvements
- Documentation updates for the new architecture

The project is now much closer to v1.0 release with the major architectural improvements completed!
