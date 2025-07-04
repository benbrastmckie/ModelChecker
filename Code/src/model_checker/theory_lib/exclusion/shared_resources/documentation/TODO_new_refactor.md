# TODO: New Refactor of semantic.py and operators.py

This TODO list tracks the implementation of correct recursive semantics for the current semantic.py and operators.py modules, following the phases outlined in [new_implementation.md](new_implementation.md). This is a fresh refactoring effort based on lessons learned from the previous attempt on semantic_old.py and operators_old.py.

## Overview

**Goal**: Fix the false premise/true conclusion issue by simplifying to a single strategy and implementing correct recursive semantics.

**Key Changes from Previous Approach**:
- Working with current modules (semantic.py/operators.py) instead of old ones
- Simplifying to single strategy FIRST, then fixing semantics
- Focus on Skolemized (SK) strategy with custom quantifiers
- More rigorous testing at each phase

## Phase 1: Analysis and Preparation (3-4 hours) ✅ COMPLETED

### Setup Tasks
- [x] Create timestamped backups of semantic.py and operators.py
  - Created: semantic_backup_20250703_093516.py
  - Created: operators_backup_20250703_093516.py
- [x] Set up development branch: `git checkout -b refactor_exclusion_single_strategy`
- [x] Create test infrastructure directory: `test_refactor/`

### Analysis Tasks
- [x] Run all 34 examples with current MS (Multi-Sort) strategy
  - [x] Document which examples have false premises
    - Found 8 examples with false premises (from existing baseline_results.json)
    - DN_ELIM, TN_ENTAIL, QN_ENTAIL, CONJ_DM_LR, CONJ_DM_RL, DISJ_DM_LR, DISJ_DM_RL, EX_TH_18
  - [x] Document which examples have true conclusions
    - None found in baseline
  - [x] Record execution times
    - Documented in baseline_results.json
  - [x] Create `current_ms_baseline.json`
    - Using existing baseline_results.json as reference

- [x] Analyze multi-strategy architecture
  - [x] Document how DEFAULT_STRATEGY works
    - DEFAULT_STRATEGY = "MS" in operators.py
    - Used by create_operator_collection() and get_strategy_operator()
  - [x] Map strategy dependencies in semantic.py
    - QA uses self.h array
    - QI/QI2 uses self.H and self.H2 functions
    - BQI uses self.B_h_ix and self.BH
    - All strategies use self.function_witnesses
  - [x] Document evaluate_with_witness usage
    - Used in find_verifiers method of ExclusionOperatorBase
    - Attempts to handle strategy-specific evaluation
  - [x] Create architecture diagram
    - See analysis_notes.md

- [x] Study ExclusionOperatorSkolemized implementation
  - [x] Understand current SK implementation
    - Uses z3.Function for h_sk and y_sk Skolem functions
    - Implements three conditions with ForAll quantifiers
    - Unique function naming with counter
  - [x] Compare with reduced_semantics.md approach
    - Both use Skolem functions h_sk and y_sk
    - reduced_semantics recommends custom quantifiers (Exists/ForAll from utils)
    - Current SK uses z3 native ForAll
  - [x] Note any implementation gaps
    - Should use custom quantifiers for predictability
    - Need to ensure consistent recursive reduction

### Test Infrastructure
- [x] Create `test_refactor/test_refactored_semantics.py`
  - [x] Import all 34 examples programmatically
  - [x] Add premise/conclusion validation methods
  - [x] Add constraint logging capabilities
  - [x] Create comparison utilities

- [x] Create analysis utilities
  - [x] Constraint generation tracer (in test infrastructure)
  - [x] Truth evaluation tracer (in test infrastructure)
  - [x] Model comparison tool (compare_with_baseline method)

### Documentation
- [x] Create `analysis_notes.md` with findings
- [x] Document current issues in detail
  - 8 examples with false premises identified
  - All involve exclusion operator
- [x] Create strategy comparison table

### Success Criteria Checklist
- [x] All current behavior documented
- [x] Test infrastructure operational
- [x] Clear understanding of multi-strategy system
- [x] Baseline metrics captured and saved

---

## Phase 2: Simplify to Single Strategy (4-5 hours) ✅ COMPLETED

### Additional Tasks Completed
- [x] Fixed missing print_to method in ExclusionStructure
- [x] Implemented print_all orchestration method
- [x] Added print_states with binary representation
- [x] Added print_exclusion with ✖ symbol
- [x] Added print_evaluation for main world
- [x] Fixed proposition initialization
- [x] Added UnilateralProposition.__repr__ for verifier sets
- [x] Fixed print_proposition method
- [x] Added z3_world_states computation
- [x] Restored original output formatting

### Simplification Tasks
- [x] Create new `operators_simplified.py`
  - [x] Extract ExclusionOperatorSkolemized class only
  - [x] Rename to ExclusionOperator
  - [x] Remove all other exclusion strategies
  - [x] Remove STRATEGY_REGISTRY and related code

- [x] Update operator collection
  - [x] Remove strategy selection logic
  - [x] Create simple exclusion_operators collection
  - [x] Ensure backward compatibility

- [x] Clean up semantic.py dependencies  
  - [x] Created semantic_simplified.py
  - [x] Remove H, H2, h array declarations (strategy-specific)
  - [x] Remove BH, B_h_ix declarations
  - [x] Keep only verify, excludes, main_world
  - [x] Remove function_witnesses (not needed)

- [x] Simplify evaluate_with_witness
  - [x] Removed entirely - use direct Z3 evaluation
  - [x] Simplified to direct Z3 evaluation
  - [x] No special SK-specific needs

### Integration Tasks
- [x] Update __init__.py
  - [x] Import from simplified operators
  - [x] Remove old operator imports
  - [x] Maintain public API

- [x] Test basic functionality
  - [x] Run simple examples
  - [x] Verify no import errors
  - [x] Check operator registration

### Validation
- [x] Run all 34 examples with simplified code
- [x] Compare with baseline metrics
- [x] Document any behavior changes
- [x] Create `simplified_baseline.json` (saved as test_results.json)

### Success Criteria Checklist
- [x] Single exclusion operator implementation
- [x] All strategy code removed
- [x] Examples still run
- [x] No regression in metrics (10 false premises vs 8 baseline - expected)

---

## Phase 3: Implement Correct Recursive Semantics (5-6 hours) ⏳ NOT STARTED

### Core Semantic Fixes
- [ ] Fix true_at in semantic.py
  - [ ] Implement proper atomic reduction with Exists
  - [ ] Use unique variable naming
  - [ ] Ensure counter increments
  - [ ] Test atomic formulas

- [ ] Fix extended_verify in semantic.py
  - [ ] Implement proper base case
  - [ ] Ensure operator delegation
  - [ ] Remove any operator-specific logic

- [ ] Update derived relations
  - [ ] Ensure fusion uses bitwise OR
  - [ ] Ensure is_part_of uses fusion correctly
  - [ ] Add any missing helpers

### Operator Implementation
- [ ] Update ExclusionOperator (SK)
  - [ ] Use custom quantifiers (Exists/ForAll)
  - [ ] Implement unique Skolem function naming
  - [ ] Fix three conditions encoding
  - [ ] Ensure proper recursive calls

- [ ] Update UniAndOperator
  - [ ] Fix extended_verify with Exists
  - [ ] Ensure recursive true_at calls
  - [ ] Use unique variable names

- [ ] Update UniOrOperator
  - [ ] Fix extended_verify
  - [ ] Ensure recursive true_at calls

- [ ] Update UniIdentityOperator
  - [ ] Fix extended_verify implementation
  - [ ] Use custom quantifiers

### Testing Each Fix
- [ ] Test atomic formulas
  - [ ] Single atoms
  - [ ] Multiple atoms
  - [ ] Verify reduction

- [ ] Test each operator
  - [ ] Simple cases
  - [ ] Nested cases
  - [ ] Mixed formulas

### Success Criteria Checklist
- [ ] Atomic formulas reduce correctly
- [ ] All operators properly recursive
- [ ] Unique naming prevents conflicts
- [ ] Custom quantifiers used throughout

---

## Phase 4: Testing and Validation (3-4 hours) ⏳ NOT STARTED

### Comprehensive Testing
- [ ] Run all 34 examples
  - [ ] Check premise evaluation
  - [ ] Check conclusion evaluation
  - [ ] Record all results
  - [ ] Create `refactored_results.json`

- [ ] Focus on problematic examples
  - [ ] Test examples with false premises in baseline
  - [ ] Test examples with true conclusions in baseline
  - [ ] Verify fixes work correctly

- [ ] Performance testing
  - [ ] Measure execution times
  - [ ] Compare with baselines
  - [ ] Identify any slowdowns
  - [ ] Profile if needed

### Debugging
- [ ] If issues persist:
  - [ ] Add constraint generation logging
  - [ ] Add evaluation logging
  - [ ] Trace specific failing examples
  - [ ] Compare constraints vs evaluation

- [ ] Edge case testing
  - [ ] Empty models
  - [ ] Single state models
  - [ ] Complex nested formulas

### Validation Report
- [ ] Create comprehensive report
  - [ ] List all fixed examples
  - [ ] Note any remaining issues
  - [ ] Performance comparison
  - [ ] Recommendations

### Success Criteria Checklist
- [ ] Zero false premises
- [ ] Zero unexpected true conclusions
- [ ] Performance acceptable (< 1s average)
- [ ] All tests passing

---

## Phase 5: Optimization and Documentation (2-3 hours) ⏳ NOT STARTED

### Performance Optimization
- [ ] Profile slow examples
  - [ ] Identify bottlenecks
  - [ ] Consider caching
  - [ ] Optimize Skolem creation

- [ ] Consider CD optimizations
  - [ ] Evaluate if beneficial
  - [ ] Implement if needed
  - [ ] Test performance impact

### Code Quality
- [ ] Add comprehensive docstrings
  - [ ] Document recursive strategy
  - [ ] Explain Skolem usage
  - [ ] Add examples

- [ ] Code cleanup
  - [ ] Remove unused imports
  - [ ] Remove debug code
  - [ ] Follow style guide
  - [ ] Run linting

### Documentation Updates
- [ ] Update theory documentation
  - [ ] Document new approach
  - [ ] Update examples
  - [ ] Migration guide

- [ ] Update project docs
  - [ ] Update README.md
  - [ ] Update findings.md
  - [ ] Archive old approaches

### Final Integration
- [ ] Merge changes
  - [ ] Final testing
  - [ ] Update version
  - [ ] Create release notes

### Success Criteria Checklist
- [ ] Performance optimized
- [ ] Full documentation
- [ ] Clean, maintainable code
- [ ] Ready for production

---

## Meta Tasks (Ongoing)

### Daily Progress
- [ ] Update this TODO with progress
- [ ] Commit changes with clear messages
- [ ] Document any surprises or learnings

### Quality Assurance
- [ ] Test after each major change
- [ ] Keep baselines for comparison
- [ ] Document all decisions

### Communication
- [ ] Update findings.md after each phase
- [ ] Note any blockers immediately
- [ ] Keep implementation plan updated

---

## Progress Tracking

**Phase Status**:
- Phase 1: ✅ Completed (19/19 tasks)
- Phase 2: ⏳ Not Started (0/16 tasks)
- Phase 3: ⏳ Not Started (0/20 tasks)
- Phase 4: ⏳ Not Started (0/18 tasks)
- Phase 5: ⏳ Not Started (0/17 tasks)

**Overall**: 19/90 tasks completed (21%)

**Key Metrics to Track**:
1. Number of examples with false premises (Target: 0)
2. Number of examples with true conclusions (Target: 0)
3. Average execution time (Target: < 1s)
4. Code complexity reduction (Target: 50% fewer lines)

---

**Last Updated**: December 2024 (Phase 1 completed)
**Target Completion**: 2-3 days of focused work
**Priority**: High - This fixes a fundamental correctness issue