# ModelChecker Remaining Tasks (Deprioritized)

**Created**: 2025-07-21  
**Updated**: 2025-07-22  
**Purpose**: Tasks deprioritized from REFACTOR.md to be addressed after logos/exclusion work is complete  
**Theories**: Bimodal and Imposition theories

**NOTE**: All default theory tasks have been removed as the default theory will be merged into the logos theory.

## Overview

This document contains all tasks that were deprioritized from the main refactoring plan. These tasks should be addressed after the focused work on logos and exclusion theories is complete. The tasks here will help bring the remaining theories (bimodal and imposition) up to the same standard as logos and exclusion.

## Phase 1: Performance Testing for Logos/Exclusion

### Performance Testing for Logos/Exclusion

**Priority**: LOW (when resumed)  
**Effort**: 2 days  
**Owner**: Performance team

**Note**: This task was moved from the main refactoring plan as performance testing is not critical for the current implementation goals.

#### Tasks:
1. **Create performance benchmarks**:
   ```python
   def benchmark_logos_theory(example_size):
       """Benchmark logos theory performance."""
       
   def benchmark_exclusion_theory(example_size):
       """Benchmark exclusion theory performance."""
   ```

2. **Document performance characteristics**:
   - Time complexity for different operations
   - Memory usage patterns
   - Optimization opportunities

**Acceptance Criteria**:
- [ ] Benchmarks created for both theories
- [ ] Performance documented
- [ ] No performance regressions
- [ ] Optimization opportunities identified

## Phase 2: Exception Handling for Other Theories

### Fix Exception Handling in Imposition Theory

**Priority**: HIGH (when resumed)  
**Effort**: 1-2 days  
**Owner**: Core team

#### Tasks:
1. **Replace bare except blocks in iterate modules**
   - `src/model_checker/theory_lib/imposition/iterate.py` (8 instances)

2. **Implementation pattern**:
   ```python
   # Current (BAD):
   try:
       world_str = bitvec_to_substates(world, N)
   except:
       world_str = str(world)
   
   # Replace with:
   try:
       world_str = bitvec_to_substates(world, N)
   except (AttributeError, ValueError, TypeError) as e:
       # Let specific errors propagate as per fail-fast philosophy
       raise ValueError(f"Failed to convert world {world} to substates: {e}")
   ```

**Acceptance Criteria**:
- [ ] No bare `except:` blocks remain in imposition iterate modules
- [ ] All exception handlers specify exception types
- [ ] Errors propagate with meaningful context
- [ ] Tests still pass after changes

## Phase 3: Unit Tests for Other Theories

### Create Missing conftest.py Files

**Priority**: MEDIUM (when resumed)  
**Effort**: 1 day  
**Owner**: Test team

#### Tasks:
1. **Create test fixtures for**:
   - `bimodal/tests/conftest.py`
   - `imposition/tests/conftest.py`

2. **Follow the pattern from logos/exclusion conftest.py files**

**Acceptance Criteria**:
- [ ] All theories have proper test fixtures
- [ ] Fixtures follow consistent patterns
- [ ] Tests can share common setup code

## Phase 4: Notebooks for Other Theories

### Create Missing Notebooks

**Priority**: MEDIUM (when resumed)  
**Effort**: 2 days  
**Owner**: Documentation team

#### Tasks:
1. **Create notebook for bimodal theory**:
   - `bimodal/notebooks/bimodal_demo.ipynb`
   - Follow template from logos/exclusion notebooks

2. **Notebook template**:
   ```python
   # 1. Theory Introduction
   # 2. Basic Examples
   # 3. Advanced Features
   # 4. Comparison with Other Theories
   # 5. Exercises
   ```

**Acceptance Criteria**:
- [ ] Bimodal has demo notebook
- [ ] Notebook executes without errors
- [ ] Clear explanations provided
- [ ] Consistent with logos/exclusion notebook style

## Phase 5: Documentation for Other Theories

### Expand Theory Documentation

**Priority**: MEDIUM (when resumed)  
**Effort**: 3-4 days  
**Owner**: Documentation team

#### Tasks:
1. **Enhance documentation**:
   - Enhance `bimodal/README.md`
   - Enhance `imposition/README.md`
   - Add examples and use cases

2. **Follow structure from logos/exclusion documentation**:
   - Theory overview
   - Key concepts
   - Usage examples
   - API reference
   - Comparison with other theories

**Acceptance Criteria**:
- [ ] All theories have comprehensive documentation
- [ ] Documentation follows consistent format
- [ ] Examples are clear and runnable
- [ ] API fully documented

## Phase 6: Theory Structure Standardization

### Standardize Remaining Theory Structures

**Priority**: HIGH (when resumed)  
**Effort**: 3-4 days  
**Owner**: Architecture team

#### Tasks:
1. **Apply decisions made for logos/exclusion to other theories**:
   - Standardize examples structure
   - Ensure consistent file organization
   - Add missing components (iterate.py where needed)

2. **Migration tasks**:
   - Update bimodal theory to match chosen structure
   - Update imposition theory to match chosen structure

**Acceptance Criteria**:
- [ ] All theories follow same structural pattern
- [ ] No inconsistencies in organization
- [ ] Clear documentation of standard structure

## Phase 7: Test Coverage Expansion

### Expand Test Coverage for Remaining Theories

**Priority**: HIGH (when resumed)  
**Effort**: 1 week  
**Owner**: Test team

#### Tasks:
1. **Add comprehensive tests for**:
   - Bimodal theory operators and semantics
   - Imposition theory operators and semantics

2. **Include**:
   - Error case testing
   - Edge case testing
   - Integration testing
   - Performance testing

**Acceptance Criteria**:
- [ ] All theories have >80% test coverage
- [ ] Error cases thoroughly tested
- [ ] Edge cases documented and tested
- [ ] No untested public methods

## Notes for Future Implementation

### Prioritization When Resuming

1. **Start with Bimodal Theory**: It has interesting temporal features and is more developed
2. **Then Imposition**: Complete the standardization across all remaining theories

### Lessons from Logos/Exclusion Work

Apply patterns and best practices discovered during the focused work:
- Test structure and organization
- Documentation templates
- Notebook examples
- Error handling patterns

### Integration Considerations

When implementing these remaining tasks:
- Ensure compatibility with improvements made to logos/exclusion
- Maintain consistency in style and approach
- Consider creating shared utilities based on logos/exclusion work
- Update any cross-theory documentation

## Timeline Estimate

**Estimated effort when resumed**: 2-3 weeks to bring all remaining theories to the same standard as logos/exclusion, assuming:
- Patterns and templates established from logos/exclusion work
- Single team working sequentially
- No major architectural changes needed
- Default theory functionality already merged into logos

This can be reduced to 1-2 weeks with parallel execution across multiple team members.