# TODO: New Refactor of semantic.py and operators.py

This TODO list tracks the implementation of correct recursive semantics for the current semantic.py and operators.py modules, following the phases outlined in [new_implementation.md](new_implementation.md). This is a fresh refactoring effort based on lessons learned from the previous attempt on semantic_old.py and operators_old.py.

## Overview

**Goal**: Fix the false premise/true conclusion issue by simplifying to a single strategy and implementing correct recursive semantics.

**Key Changes from Previous Approach**:
- Working with current modules (semantic.py/operators.py) instead of old ones
- Simplifying to single strategy FIRST, then fixing semantics
- Focus on Skolemized (SK) strategy with custom quantifiers
- More rigorous testing at each phase

## Phase 1: Analysis and Preparation (3-4 hours) ⏳ NOT STARTED

### Setup Tasks
- [ ] Create timestamped backups of semantic.py and operators.py
- [ ] Set up development branch: `git checkout -b refactor_exclusion_single_strategy`
- [ ] Create test infrastructure directory: `test_refactor/`

### Analysis Tasks
- [ ] Run all 34 examples with current MS (Multi-Sort) strategy
  - [ ] Document which examples have false premises
  - [ ] Document which examples have true conclusions
  - [ ] Record execution times
  - [ ] Create `current_ms_baseline.json`

- [ ] Analyze multi-strategy architecture
  - [ ] Document how DEFAULT_STRATEGY works
  - [ ] Map strategy dependencies in semantic.py
  - [ ] Document evaluate_with_witness usage
  - [ ] Create architecture diagram

- [ ] Study ExclusionOperatorSkolemized implementation
  - [ ] Understand current SK implementation
  - [ ] Compare with reduced_semantics.md approach
  - [ ] Note any implementation gaps

### Test Infrastructure
- [ ] Create `test_refactor/test_refactored_semantics.py`
  - [ ] Import all 34 examples programmatically
  - [ ] Add premise/conclusion validation methods
  - [ ] Add constraint logging capabilities
  - [ ] Create comparison utilities

- [ ] Create analysis utilities
  - [ ] Constraint generation tracer
  - [ ] Truth evaluation tracer
  - [ ] Model comparison tool

### Documentation
- [ ] Create `analysis_notes.md` with findings
- [ ] Document current issues in detail
- [ ] Create strategy comparison table

### Success Criteria Checklist
- [ ] All current behavior documented
- [ ] Test infrastructure operational
- [ ] Clear understanding of multi-strategy system
- [ ] Baseline metrics captured and saved

---

## Phase 2: Simplify to Single Strategy (4-5 hours) ⏳ NOT STARTED

### Simplification Tasks
- [ ] Create new `operators_simplified.py`
  - [ ] Extract ExclusionOperatorSkolemized class only
  - [ ] Rename to ExclusionOperator
  - [ ] Remove all other exclusion strategies
  - [ ] Remove STRATEGY_REGISTRY and related code

- [ ] Update operator collection
  - [ ] Remove strategy selection logic
  - [ ] Create simple exclusion_operators collection
  - [ ] Ensure backward compatibility

- [ ] Clean up semantic.py dependencies
  - [ ] Remove H, H2, h array declarations (strategy-specific)
  - [ ] Remove BH, B_h_ix declarations
  - [ ] Keep only verify, excludes, main_world
  - [ ] Remove function_witnesses if SK doesn't need it

- [ ] Simplify evaluate_with_witness
  - [ ] Remove strategy-specific logic
  - [ ] Simplify to direct Z3 evaluation
  - [ ] Document any SK-specific needs

### Integration Tasks
- [ ] Update __init__.py
  - [ ] Import from simplified operators
  - [ ] Remove old operator imports
  - [ ] Maintain public API

- [ ] Test basic functionality
  - [ ] Run simple examples
  - [ ] Verify no import errors
  - [ ] Check operator registration

### Validation
- [ ] Run all 34 examples with simplified code
- [ ] Compare with baseline metrics
- [ ] Document any behavior changes
- [ ] Create `simplified_baseline.json`

### Success Criteria Checklist
- [ ] Single exclusion operator implementation
- [ ] All strategy code removed
- [ ] Examples still run
- [ ] No regression in metrics

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
- Phase 1: ⏳ Not Started (0/19 tasks)
- Phase 2: ⏳ Not Started (0/16 tasks)
- Phase 3: ⏳ Not Started (0/20 tasks)
- Phase 4: ⏳ Not Started (0/18 tasks)
- Phase 5: ⏳ Not Started (0/17 tasks)

**Overall**: 0/90 tasks completed (0%)

**Key Metrics to Track**:
1. Number of examples with false premises (Target: 0)
2. Number of examples with true conclusions (Target: 0)
3. Average execution time (Target: < 1s)
4. Code complexity reduction (Target: 50% fewer lines)

---

**Last Updated**: [Current Date]
**Target Completion**: 2-3 days of focused work
**Priority**: High - This fixes a fundamental correctness issue