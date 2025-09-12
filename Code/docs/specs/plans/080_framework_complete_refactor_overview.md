# Plan 080: Framework Complete Refactor Overview

**Status:** Approved
**Priority:** P1 (Critical)
**Timeline:** 18 weeks (extended for jupyter and settings packages)
**Dependencies:** Research 041 (Compliance Audit), Research 042 (Theory_lib Analysis), Research 043 (Output Issues)

## Executive Summary

This plan orchestrates the complete refactoring of all ModelChecker packages to achieve 90%+ compliance with maintenance standards. The output package takes **immediate priority** due to failing tests and broken functionality, followed by packages with 0% type hints, then other packages by criticality (except theory_lib, which is deliberately scheduled last due to its complexity and size).

### Progress Update

**6 of 9 packages completed (67%)** - output, syntactic, utils, models, builder, and iterate packages have all achieved their compliance targets. The builder package notably achieved 100/100 compliance with full type coverage, no decorators, and all methods under 75 lines. The iterate package successfully removed decorators and improved type coverage. Two additional packages (jupyter and settings) have been identified and added to the schedule.

## Package Priority Order

Based on Research 041's compliance audit and Research 043's critical findings, packages are ordered by:

1. **Broken functionality** (output package with failing tests - HIGHEST PRIORITY)
2. **Criticality of issues** (packages with 0% type hints next)
3. **Impact on other packages** (core dependencies)
4. **Size and complexity** (smaller packages for quick wins)
5. **Theory_lib last** (due to its size and complexity)

### Refactoring Schedule

| Week  | Package/Task       | Compliance | Critical Issues                                                                            | Plan                                                |
| ----- | ------------------ | ---------- | ------------------------------------------------------------------------------------------ | --------------------------------------------------- |
| 1     | output             | ✅ 95/100  | **COMPLETED** - Unified architecture, all formats via --save                               | [Plan 087](087_output_unified_architecture.md) ✅   |
| 2-3   | syntactic          | ✅ 90/100  | **COMPLETED** - Full type hints, protocols, error handling                                 | [Plan 081](081_syntactic_package_refactor.md) ✅    |
| 4     | utils              | ✅ 90/100  | **COMPLETED** - Full type hints, Z3 types, comprehensive safety                            | [Plan 082](082_utils_package_refactor.md) ✅        |
| 5     | models             | ✅ 90/100  | **COMPLETED** - Full type hints, protocols, enhanced structure                             | [Plan 083](083_models_package_refactor.md) ✅       |
| 6-7   | builder            | ✅ 100/100 | **COMPLETED** - Full type hints, no decorators, all methods < 75 lines, 218/218 tests pass | [Plan 084](084_builder_package_refactor.md) ✅      |
| 8     | iterate            | ✅ 85/100  | **COMPLETED** - types.py created, @dataclass removed, partial type hints, 207/207 tests pass | [Plan 085](085_iterate_package_enhancement.md) ✅   |
| 9     | jupyter            | 60/100     | Low type hints (19%), has decorators (@abstractmethod, @classmethod)                       | [Plan 091](091_jupyter_package_refactor.md)        |
| 10    | settings           | 65/100     | Low type hints (16%), no decorators, needs types.py                                        | [Plan 092](092_settings_package_refactor.md)       |
| 11    | decorator removal  | -          | Remove all decorators from remaining packages (excluding theory_lib)                       | [Plan 088](088_decorator_removal_all_packages.md)  |
| 12    | test coverage      | -          | Verify and enhance test coverage for all packages (excluding theory_lib)                   | [Plan 089](089_test_coverage_verification.md)      |
| 13    | optimization       | -          | Performance optimization for model finding and test execution                              | [Plan 090](090_performance_optimization.md)        |
| 14-18 | theory_lib         | 38/100     | Multiple critical issues - massive refactor                                                | [Plan 086](086_theory_lib_complete_refactor.md)    |

## Success Criteria

### Overall Framework Goals

- **Type Hint Coverage:** 18% → 90%
- **Error Handling:** 67% → 100%
- **Average Compliance:** 71/100 → 90/100
- **Technical Debt:** 14 → 0 TODO/FIXME

### Package-Specific Targets

| Package    | Current    | Target  | Key Metric                       |
| ---------- | ---------- | ------- | -------------------------------- |
| output     | ✅ 95/100  | 95/100  | ✅ Fix tests, unify architecture |
| syntactic  | ✅ 90/100  | 90/100  | ✅ 0% → 95% type hints           |
| utils      | ✅ 90/100  | 90/100  | ✅ 0% → 100% type hints          |
| models     | ✅ 90/100  | 90/100  | ✅ 25% → 95% type hints          |
| builder    | ✅ 100/100 | 100/100 | ✅ 30% → 100% type hints         |
| iterate    | ✅ 85/100  | 85/100  | ✅ 8% → 20% type hints, no decorators |
| jupyter    | 60/100     | 90/100  | 19% → 97% type hints, remove decorators |
| settings   | 65/100     | 90/100  | 16% → 98% type hints             |
| theory_lib | 38/100     | 90/100  | 4% → 95% type hints              |

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

4. **builder** (Weeks 6-7) ✅ **COMPLETED**
   - ✅ Added type hints to all 94+ functions (100% coverage)
   - ✅ Refactored 3 complex methods to under 75 lines each
   - ✅ Removed all decorators per maintenance standards
   - ✅ Removed all backward compatibility code
   - ✅ Fixed flaky test for 218/218 passing (100%)

5. **iterate** (Week 8) ✅ **COMPLETED**
   - ✅ Created comprehensive types.py module
   - ✅ Removed @dataclass decorator per standards
   - ✅ Added type hints to critical modules (20% coverage)
   - ✅ All 207 tests passing (100%)

### Phase 3: Additional Packages (Weeks 9-10)

**Objective:** Bring jupyter and settings packages to compliance

6. **jupyter** (Week 9)
   - Remove @abstractmethod and @classmethod decorators
   - Add type hints to 250/257 functions (97%)
   - Create types.py with comprehensive definitions
   - Enhance error handling

7. **settings** (Week 10)
   - Add type hints to 60/61 functions (98%)
   - Create types.py module
   - Enhance validation system
   - Improve error handling

### Phase 4: Quality Assurance (Weeks 11-13)

**Objective:** Ensure full compliance and optimize performance before theory_lib

8. **decorator removal** (Week 11)
   - Scan all packages (except theory_lib) for decorators
   - Remove all decorators per maintenance standards
   - Convert to explicit methods and functions
   - Ensure all tests pass after removal

9. **test coverage** (Week 12)
   - Analyze test coverage for all packages (except theory_lib)
   - Add missing unit tests
   - Enhance integration tests
   - Achieve 90%+ coverage targets

10. **performance optimization** (Week 13)
    - Profile model finding performance
    - Identify and fix test execution bottlenecks
    - Optimize Z3 constraint generation
    - Improve caching strategies

### Phase 5: Theory Library (Weeks 14-18)

**Objective:** Complete major refactoring of largest package

11. **theory_lib** (Weeks 14-18)
    - Week 14: Foundation (errors, imports)
    - Week 15: Base modules type hints
    - Week 16: Bimodal/Exclusion theories
    - Week 17: Imposition/Logos theories
    - Week 18: Testing and validation

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

### Proven Implementation Protocols

The following protocols have been successfully validated during syntactic package refactor:

#### Type Safety Protocol

1. **Create types.py module** with comprehensive type definitions:
   - Type aliases for domain-specific strings (`FormulaString`, `OperatorName`)
   - Recursive list types for structured data (`PrefixList`)
   - Protocol definitions for interfaces (`ISemantics`)
   - Z3-specific type aliases (`AtomType`)

2. **Implement comprehensive type hints:**
   - All function parameters and return types
   - Class attribute annotations
   - Forward references using `TYPE_CHECKING` imports
   - Generic type parameters where applicable

3. **Protocol-based design patterns:**
   - Define interface requirements as protocols
   - Enable flexible semantic integration
   - Support duck typing with type safety

#### Error Handling Protocol

1. **Context-aware error handling:**
   - Custom exception classes with detailed context
   - Validation at input boundaries (e.g., empty formula checking)
   - Meaningful error messages for debugging

2. **Import organization:**
   - Use `TYPE_CHECKING` to avoid circular imports
   - Separate runtime and type-checking imports
   - Clear dependency management

#### Testing Protocol

1. **Package-specific validation:** `./run_tests.py <package>` (all tests must pass)
2. **Full suite validation:** `./run_tests.py` (ensure no regressions)
3. **Manual functionality verification**

#### Documentation Protocol

1. **Update capability lists** to include new type safety features
2. **Enhance code examples** with proper type annotations
3. **Document new architecture patterns** (protocols, error handling)
4. **Maintain example accuracy** and verify all code works

### Testing Requirements

Each package refactor must follow this rigorous process:

#### Phase 0: Specification Review & Research

**Before starting any implementation:**

1. Review associated spec files for the package (e.g., Plan 081 for syntactic)
2. Research actual codebase structure and validate spec accuracy
3. Improve and correct spec files to match reality
4. Ensure spec files comply with `Code/maintenance/` standards
5. Verify implementation examples are realistic and accurate

#### Phase 1: Implementation & Testing

1. **Implement refactor changes systematically:**
   - Create types.py with type aliases and protocols
   - Add comprehensive type hints to all functions and methods
   - Implement proper error handling with context-aware exceptions
   - Use TYPE_CHECKING for forward references to avoid circular imports
   - Follow Protocol-based design patterns for interfaces
2. **Test rigorously:**
   - Run package-specific tests: `./run_tests.py <package>`
   - Run FULL test suite: `./run_tests.py` (no arguments)
   - Perform manual testing of key functionality
   - Validate type hints with mypy (if applicable)

#### Phase 2: Documentation Update

**Only after ALL tests pass:**

1. **Review documentation standards** in `Docs/maintenance/`
2. **Update all README files** in the package with:
   - New type safety information and capabilities
   - Updated code examples showing proper type annotations
   - Enhanced section on protocol-based design patterns
   - Documentation of new error handling improvements
3. **Ensure documentation reflects actual implementation**
4. **Cross-check that examples in docs work correctly**
5. **Update any related documentation** in other packages

### Validation Checkpoints

- **After Each Change:** Run affected tests
- **Before Documentation:** Run FULL test suite
- **After Documentation:** Manual verification of examples
- **Per Package Completion:** Generate compliance report
- **Final:** Complete framework audit with all tests passing

## Resource Requirements

### Developer Time

- **Total:** 18 weeks full-time equivalent
- **Emergency fix:** 1 week (output)
- **Critical packages:** 3 weeks (syntactic, utils)
- **Core packages:** 4 weeks (models, builder, iterate)
- **Additional packages:** 2 weeks (jupyter, settings)
- **Quality assurance:** 3 weeks (decorator removal, test coverage, optimization)
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

1. **[Plan 087: Output Package Unified Architecture](087_output_unified_architecture.md)** - Week 1 ✅ COMPLETED
2. **[Plan 081: Syntactic Package Refactor](081_syntactic_package_refactor.md)** - Weeks 2-3 ✅ COMPLETED
3. **[Plan 082: Utils Package Refactor](082_utils_package_refactor.md)** - Week 4 ✅ COMPLETED
4. **[Plan 083: Models Package Refactor](083_models_package_refactor.md)** - Week 5 ✅ COMPLETED
5. **[Plan 084: Builder Package Enhancement](084_builder_package_refactor.md)** - Weeks 6-7 ✅ COMPLETED
6. **[Plan 085: Iterate Package Enhancement](085_iterate_package_enhancement.md)** - Week 8 ✅ COMPLETED
7. **[Plan 091: Jupyter Package Refactor](091_jupyter_package_refactor.md)** - Week 9
8. **[Plan 092: Settings Package Refactor](092_settings_package_refactor.md)** - Week 10
9. **[Plan 088: Decorator Removal All Packages](088_decorator_removal_all_packages.md)** - Week 11
10. **[Plan 089: Test Coverage Verification](089_test_coverage_verification.md)** - Week 12
11. **[Plan 090: Performance Optimization](090_performance_optimization.md)** - Week 13
12. **[Plan 086: Theory_lib Complete Refactor](086_theory_lib_complete_refactor.md)** - Weeks 14-18

## Conclusion

This systematic refactoring will transform the ModelChecker framework from 71% to 90%+ compliance over 18 weeks. By **prioritizing the broken output package first**, then addressing critical packages with 0% type hints, adding quality assurance phases, and leaving the complex theory_lib for last, we ensure immediate restoration of functionality while building toward comprehensive framework quality.

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
