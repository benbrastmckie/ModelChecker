# TODO

## Priority 1: Critical Path to v1.0 Release

### 1.1 Framework Refactoring Completion (HIGHEST PRIORITY - 0% Complete at 95% target)

- [ ] **Complete Plan 060 Framework Refactoring** - Bring to 100% implementation at 95% compliance
  - [ ] **models/ package enhancement (Plan 061)** - IN PROGRESS
    - Current: 85% → Target: 95%+ compliance
    - [x] Phase 1-4: Completed (achieved 85%)
    - [ ] Phase 5: Enhanced compliance to reach 95%
    - [ ] Additional method refinement
    - [ ] Complete test coverage
    - [ ] Full documentation update
  - [ ] **tests/ package enhancement (Plan 062)** - IN PROGRESS
    - Current: 90% → Target: 95%+ compliance
    - [x] Phase 1-4: Completed (achieved 90%)
    - [ ] Phase 5: Final enhancements to reach 95%
    - [ ] Additional test organization improvements
    - [ ] Complete fixture standardization
    - [ ] Enhanced error case coverage
  - [ ] **jupyter/ package refactor (Plan 063)** - HIGH PRIORITY (Week 1-2)
    - Current: 71% → Target: 95%+ compliance
    - [ ] Phase 1: Foundation Cleanup (imports, style, UTF-8)
    - [ ] Phase 2: Method Refinement (extract complex methods)
    - [ ] Phase 3: Error Handling (JupyterError hierarchy)
    - [ ] Phase 4: Architectural Improvements (protocols, DI)
    - [ ] Phase 5: Enhanced Testing & Documentation (to reach 95%)
    - [ ] Add comprehensive test coverage (missing tests are liability)
  - [ ] **output/ package refactor (Plan 064)** - MEDIUM PRIORITY (Week 3)
    - Current: 72% → Target: 95%+ compliance
    - [ ] Phase 1: Foundation Cleanup
    - [ ] Phase 2: Method Refinement
    - [ ] Phase 3: Error Handling (OutputError hierarchy)
    - [ ] Phase 4: Architectural Improvements
    - [ ] Phase 5: Enhanced Standards Compliance (to reach 95%)
    - [ ] Add Jupyter notebook generation capability
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

### 2.1 Code Quality & Testing

- [ ] **linting and cleanup**
  - [ ] Remove unused imports in `/home/benjamin/Documents/Philosophy/Projects/ModelChecker/Code/src/model_checker/builder/example.py`
  - [ ] Run pylint systematically across entire codebase
  - [ ] Fix all critical and major issues

- [ ] **unit test coverage**
  - [ ] Check coverage metrics (target 80%+)
  - [ ] Add missing test cases for new builder modules
  - [ ] Update test documentation

### 2.2 Theory Metadata & Documentation

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

- [ ] **finalize documentation**
  - [ ] Complete methodology documentation
  - [ ] Update `/home/benjamin/Documents/Philosophy/Projects/ModelChecker/Docs/usage/WORKFLOW.md`
  - [ ] Update `/home/benjamin/Documents/Philosophy/Projects/ModelChecker/Docs/usage/COMPARE_THEORIES.md`
  - [ ] Revise `/home/benjamin/Documents/Philosophy/Projects/ModelChecker/Docs/theory/README.md`
  - [ ] Update `/home/benjamin/Documents/Philosophy/Projects/ModelChecker/Code/README.md` for v1.0
  - [ ] Fix all broken links from `Docs/`

### 4.3 Development Tools

- [ ] **iterate improvements**
  - [ ] Report when networkx not available
  - [ ] Make dependencies explicit
  - [ ] Update documentation for new builder structure
- [ ] **jupyter enhancements**
  - [ ] Check all examples work
  - [ ] Implement convenience methods (see `/home/benjamin/Documents/Philosophy/Projects/ModelChecker/Code/specs/CONV_METHODS.md`)

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

### Partial Progress (IN PROGRESS)

- [~] **models/ package refactor** - Phase 1-4 complete (85% compliance, target 95%)
- [~] **tests/ package refactor** - Phase 1-4 complete (90% compliance, target 95%)
- [~] **Test organization** - Basic structure done, needs enhancement for 95% compliance

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

**Major Wins**: The builder refactor is COMPLETE! The iterate package has been extracted and modularized. Framework refactoring has begun with models/ at 85% and tests/ at 90% compliance.

**Next Critical Path**: Complete the Framework Refactoring (Plan 060) to achieve 100% implementation:

- **Immediate Priority**: jupyter/ package (Plan 063) - critical for user interaction
- **Then**: output/, iterate/, and settings/ packages in priority order
- **Enhanced models/ and tests/**: Bring from current 85%/90% to 95%
- **Goal**: Achieve ≥95% maintenance standards compliance for ALL packages

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
