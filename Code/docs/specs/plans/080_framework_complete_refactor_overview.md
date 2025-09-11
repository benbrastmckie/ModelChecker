# Plan 080: Framework Complete Refactor Overview

**Status:** Approved  
**Priority:** P1 (Critical)  
**Timeline:** 12 weeks  
**Dependencies:** Research 041 (Compliance Audit), Research 042 (Theory_lib Analysis)  

## Executive Summary

This plan orchestrates the complete refactoring of all ModelChecker packages to achieve 90%+ compliance with maintenance standards. Packages are prioritized by criticality, with the most problematic packages addressed first (except theory_lib, which is deliberately scheduled last due to its complexity and size).

## Package Priority Order

Based on Research 041's compliance audit, packages are ordered by:
1. **Criticality of issues** (packages with 0% type hints first)
2. **Impact on other packages** (core dependencies first)
3. **Size and complexity** (smaller packages first for quick wins)
4. **Theory_lib last** (due to its size and complexity)

### Refactoring Schedule

| Week | Package | Compliance | Critical Issues | Plan |
|------|---------|------------|-----------------|------|
| 1-2 | syntactic | 45/100 | No type hints, no errors | [Plan 081](081_syntactic_package_refactor.md) |
| 3 | utils | 55/100 | No type hints | [Plan 082](082_utils_package_refactor.md) |
| 4 | models | 73/100 | Low type hints | [Plan 083](083_models_package_refactor.md) |
| 5-6 | builder | 78/100 | Low type hints | [Plan 084](084_builder_package_refactor.md) |
| 7 | iterate | 77/100 | Low type hints | [Plan 085](085_iterate_package_enhancement.md) |
| 8-12 | theory_lib | 38/100 | Multiple critical | [Plan 086](086_theory_lib_complete_refactor.md) |

**Note:** Packages already compliant (jupyter, output, settings) are excluded from refactoring.

## Success Criteria

### Overall Framework Goals
- **Type Hint Coverage:** 18% → 90%
- **Error Handling:** 67% → 100%  
- **Average Compliance:** 71/100 → 90/100
- **Technical Debt:** 14 → 0 TODO/FIXME

### Package-Specific Targets

| Package | Current | Target | Key Metric |
|---------|---------|--------|------------|
| syntactic | 45/100 | 90/100 | 0% → 95% type hints |
| utils | 55/100 | 90/100 | 0% → 95% type hints |
| models | 73/100 | 90/100 | 25% → 95% type hints |
| builder | 78/100 | 90/100 | 20% → 95% type hints |
| iterate | 77/100 | 90/100 | 18% → 95% type hints |
| theory_lib | 38/100 | 90/100 | 4% → 95% type hints |

## Implementation Strategy

### Phase 1: Critical Packages (Weeks 1-3)
**Objective:** Fix packages with 0% type hint coverage

1. **syntactic** (Weeks 1-2)
   - Add type hints to 122 functions
   - Create SyntacticError hierarchy
   - Fix import organization
   - Resolve 2 TODO items

2. **utils** (Week 3)
   - Add type hints to 77 functions
   - Consider UtilityError hierarchy
   - Maintain clean imports

### Phase 2: Core Packages (Weeks 4-7)
**Objective:** Improve packages that other components depend on

3. **models** (Week 4)
   - Add type hints to 101 functions
   - Enhance error handling
   - Resolve 2 TODO items

4. **builder** (Weeks 5-6)
   - Add type hints to 419 functions
   - Refactor 4 complex methods
   - Maintain excellent test coverage

5. **iterate** (Week 7)
   - Add type hints to 320 functions
   - Resolve 1 TODO item
   - Preserve recent improvements

### Phase 3: Theory Library (Weeks 8-12)
**Objective:** Complete major refactoring of largest package

6. **theory_lib** (Weeks 8-12)
   - Week 8: Foundation (errors, imports)
   - Week 9: Base modules type hints
   - Week 10: Bimodal/Exclusion theories
   - Week 11: Imposition/Logos theories
   - Week 12: Testing and validation

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
- **Total:** 12 weeks full-time equivalent
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

1. **syntactic first** - Most critical (0% types, no errors), small scope
2. **utils second** - Critical (0% types), utilities used everywhere
3. **models third** - Core data structures, manageable size
4. **builder fourth** - Important but already decent, larger scope
5. **iterate fifth** - Recent improvements, just needs types
6. **theory_lib last** - Most complex, largest scope, needs dedicated effort

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

1. **[Plan 081: Syntactic Package Refactor](081_syntactic_package_refactor.md)** - Weeks 1-2
2. **[Plan 082: Utils Package Refactor](082_utils_package_refactor.md)** - Week 3
3. **[Plan 083: Models Package Refactor](083_models_package_refactor.md)** - Week 4
4. **[Plan 084: Builder Package Enhancement](084_builder_package_refactor.md)** - Weeks 5-6
5. **[Plan 085: Iterate Package Enhancement](085_iterate_package_enhancement.md)** - Week 7
6. **[Plan 086: Theory_lib Complete Refactor](086_theory_lib_complete_refactor.md)** - Weeks 8-12

## Conclusion

This systematic refactoring will transform the ModelChecker framework from 71% to 90%+ compliance over 12 weeks. By addressing critical packages first and leaving the complex theory_lib for last, we ensure steady progress with quick wins while building expertise for the most challenging refactor.

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
- [Code Maintenance Standards](../../../maintenance/README.md)