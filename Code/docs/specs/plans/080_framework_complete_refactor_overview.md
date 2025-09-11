# Plan 080: Framework Complete Refactor Overview

**Status:** Approved  
**Priority:** P1 (Critical)  
**Timeline:** 13 weeks  
**Dependencies:** Research 041 (Compliance Audit), Research 042 (Theory_lib Analysis), Research 043 (Output Issues)  

## Executive Summary

This plan orchestrates the complete refactoring of all ModelChecker packages to achieve 90%+ compliance with maintenance standards. The output package takes **immediate priority** due to failing tests and broken functionality, followed by packages with 0% type hints, then other packages by criticality (except theory_lib, which is deliberately scheduled last due to its complexity and size).

## Package Priority Order

Based on Research 041's compliance audit and Research 043's critical findings, packages are ordered by:
1. **Broken functionality** (output package with failing tests - HIGHEST PRIORITY)
2. **Criticality of issues** (packages with 0% type hints next)
3. **Impact on other packages** (core dependencies)
4. **Size and complexity** (smaller packages for quick wins)
5. **Theory_lib last** (due to its size and complexity)

### Refactoring Schedule

| Week | Package | Compliance | Critical Issues | Plan |
|------|---------|------------|-----------------|------|
| 1 | output | 92/100* | **FAILING TESTS**, broken notebook generation | [Plan 087](087_output_unified_architecture.md) |
| 2-3 | syntactic | 45/100 | No type hints, no errors | [Plan 081](081_syntactic_package_refactor.md) |
| 4 | utils | 55/100 | No type hints | [Plan 082](082_utils_package_refactor.md) |
| 5 | models | 73/100 | Low type hints | [Plan 083](083_models_package_refactor.md) |
| 6-7 | builder | 78/100 | Low type hints | [Plan 084](084_builder_package_refactor.md) |
| 8 | iterate | 77/100 | Low type hints | [Plan 085](085_iterate_package_enhancement.md) |
| 9-13 | theory_lib | 38/100 | Multiple critical | [Plan 086](086_theory_lib_complete_refactor.md) |

**\*Note:** Output shows 92/100 compliance but has critical architectural issues and failing tests that must be addressed immediately.

## Success Criteria

### Overall Framework Goals
- **Type Hint Coverage:** 18% → 90%
- **Error Handling:** 67% → 100%  
- **Average Compliance:** 71/100 → 90/100
- **Technical Debt:** 14 → 0 TODO/FIXME

### Package-Specific Targets

| Package | Current | Target | Key Metric |
|---------|---------|--------|------------|
| output | 92/100* | 95/100 | Fix tests, unify architecture |
| syntactic | 45/100 | 90/100 | 0% → 95% type hints |
| utils | 55/100 | 90/100 | 0% → 95% type hints |
| models | 73/100 | 90/100 | 25% → 95% type hints |
| builder | 78/100 | 90/100 | 20% → 95% type hints |
| iterate | 77/100 | 90/100 | 18% → 95% type hints |
| theory_lib | 38/100 | 90/100 | 4% → 95% type hints |

## Implementation Strategy

### Phase 0: Emergency Fix (Week 1)
**Objective:** Fix broken output package functionality

1. **output** (Week 1)
   - Fix failing test in OutputConfig
   - Unify notebook generation architecture
   - Implement --save default behavior
   - Create NotebookStrategy for unified pipeline

### Phase 1: Critical Packages (Weeks 2-4)
**Objective:** Fix packages with 0% type hint coverage

1. **syntactic** (Weeks 2-3)
   - Add type hints to 122 functions
   - Create SyntacticError hierarchy
   - Fix import organization
   - Resolve 2 TODO items

2. **utils** (Week 4)
   - Add type hints to 77 functions
   - Consider UtilityError hierarchy
   - Maintain clean imports

### Phase 2: Core Packages (Weeks 5-8)
**Objective:** Improve packages that other components depend on

3. **models** (Week 5)
   - Add type hints to 101 functions
   - Enhance error handling
   - Resolve 2 TODO items

4. **builder** (Weeks 6-7)
   - Add type hints to 419 functions
   - Refactor 4 complex methods
   - Maintain excellent test coverage

5. **iterate** (Week 8)
   - Add type hints to 320 functions
   - Resolve 1 TODO item
   - Preserve recent improvements

### Phase 3: Theory Library (Weeks 9-13)
**Objective:** Complete major refactoring of largest package

6. **theory_lib** (Weeks 9-13)
   - Week 9: Foundation (errors, imports)
   - Week 10: Base modules type hints
   - Week 11: Bimodal/Exclusion theories
   - Week 12: Imposition/Logos theories
   - Week 13: Testing and validation

## Risk Management

### High Risk Areas
1. **theory_lib complexity** - 597 functions across 27 files
2. **Breaking changes** - No backward compatibility maintained
3. **Time estimates** - Large packages may take longer

### Mitigation Strategies
1. **Incremental approach** - Package by package, file by file
2. **Comprehensive testing** - Run full test suite after each change
3. **Automation tools** - Scripts for type hint generation
4. **Feature branches** - Isolate changes until validated

## Quality Assurance

### Testing Requirements
Each package refactor must:
1. Maintain or improve test coverage
2. Pass all existing tests
3. Add tests for new error handling
4. Validate type hints with mypy

### Validation Checkpoints
- **Daily:** Run package-specific tests
- **Weekly:** Run full framework tests
- **Per Package:** Generate compliance report
- **Final:** Complete framework audit

## Resource Requirements

### Developer Time
- **Total:** 13 weeks full-time equivalent
- **Emergency fix:** 1 week (output)
- **Critical packages:** 3 weeks (syntactic, utils)
- **Core packages:** 4 weeks (models, builder, iterate)
- **Theory library:** 5 weeks

### Tooling
- **mypy** - Type checking
- **pytest** - Test validation
- **coverage** - Test coverage metrics
- **Custom scripts** - Type hint generation

## Implementation Order Rationale

### Why This Order?

1. **output first** - BROKEN FUNCTIONALITY, failing tests, needs immediate fix
2. **syntactic second** - Most critical (0% types, no errors), small scope
3. **utils third** - Critical (0% types), utilities used everywhere
4. **models fourth** - Core data structures, manageable size
5. **builder fifth** - Important but already decent, larger scope
6. **iterate sixth** - Recent improvements, just needs types
7. **theory_lib last** - Most complex, largest scope, needs dedicated effort

### Why Theory_lib Last?

1. **Size:** 597 functions vs. others with <420
2. **Complexity:** Multiple interconnected theories
3. **Dependencies:** Benefits from other refactors being complete
4. **Learning:** Apply lessons learned from other packages
5. **Focus:** Requires undivided attention

## Success Metrics

### Weekly Progress Indicators
- Functions with type hints added
- Error classes created
- TODO/FIXME resolved
- Test coverage maintained/improved
- Compliance score increase

### Package Completion Criteria
- [ ] 95%+ type hint coverage
- [ ] Custom error hierarchy implemented
- [ ] All imports follow standards
- [ ] No TODO/FIXME comments
- [ ] All tests passing
- [ ] Compliance score ≥85/100

## Communication Plan

### Status Updates
- **Daily:** Git commits with progress
- **Weekly:** Update package-specific plan
- **Per Package:** Completion report
- **Final:** Framework compliance audit

### Documentation Updates
- Update package README after refactor
- Document new error hierarchies
- Update API documentation
- Create migration guides if needed

## Detailed Implementation Plans

Each package has a detailed implementation plan with specific tasks, timelines, and technical specifications:

1. **[Plan 087: Output Package Unified Architecture](087_output_unified_architecture.md)** - Week 1 (PRIORITY)
2. **[Plan 081: Syntactic Package Refactor](081_syntactic_package_refactor.md)** - Weeks 2-3
3. **[Plan 082: Utils Package Refactor](082_utils_package_refactor.md)** - Week 4
4. **[Plan 083: Models Package Refactor](083_models_package_refactor.md)** - Week 5
5. **[Plan 084: Builder Package Enhancement](084_builder_package_refactor.md)** - Weeks 6-7
6. **[Plan 085: Iterate Package Enhancement](085_iterate_package_enhancement.md)** - Week 8
7. **[Plan 086: Theory_lib Complete Refactor](086_theory_lib_complete_refactor.md)** - Weeks 9-13

## Conclusion

This systematic refactoring will transform the ModelChecker framework from 71% to 90%+ compliance over 13 weeks. By **prioritizing the broken output package first**, then addressing critical packages with 0% type hints, and leaving the complex theory_lib for last, we ensure immediate restoration of functionality while building toward comprehensive framework quality.

The investment in code quality will yield:
- **Better maintainability** through type safety
- **Improved reliability** via error handling
- **Enhanced developer experience** with IDE support
- **Reduced bugs** from static analysis
- **Faster onboarding** for contributors

---

**Related Documents:**
- [Research 041: Framework Quality and Compliance Audit](../research/041_framework_quality_compliance_audit.md)
- [Research 042: Theory Library Compliance Deep Analysis](../research/042_theory_lib_compliance_deep_analysis.md)
- [Research 043: Output Package and Notebook Generation Issues](../research/043_output_notebook_generation_issues.md)
- [Code Maintenance Standards](../../../maintenance/README.md)