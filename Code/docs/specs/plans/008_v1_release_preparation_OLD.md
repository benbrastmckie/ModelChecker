# V1 Release Preparation Plan

**Plan ID**: 002  
**Created**: 2025-08-05  
**Last Updated**: 2025-08-06  
**Status**: In Progress - Phase 1 Pending
**Author**: AI Assistant

## Executive Summary

This plan outlines the comprehensive preparation for ModelChecker v1.0, emphasizing incremental refactoring with rigorous testing at each step. Following the iterator regression incident (see [findings/002_iterator_warnings_investigation.md](../findings/002_iterator_warnings_investigation.md)), this plan incorporates continuous validation using dev_cli.py and comprehensive test suites.

**Key Changes from Original Plan**:
- Integrated continuous CLI testing with dev_cli.py throughout each phase
- Added targeted testing requirements for each refactoring step
- Incorporated baseline capture and regression detection protocols
- Extended timeline to accommodate thorough testing

## Problem Statement

The ModelChecker codebase requires significant refactoring before v1.0 release:
- Three monolithic modules exceed 800 lines each (model.py, utils.py, syntactic.py)
- Missing module docstrings and incomplete API documentation
- Inconsistent code organization and naming conventions
- Need for comprehensive test coverage verification

## Proposed Solution

### Refactoring Strategy

1. **Incremental Refactoring**: Break monolithic modules into logical subpackages
2. **Continuous Testing**: Use dev_cli.py to validate behavior after each change
3. **Baseline Comparison**: Capture outputs before changes for regression detection
4. **Atomic Commits**: One logical change per commit with immediate testing

### Testing Protocol

Each refactoring step will follow this protocol:

1. **Baseline Capture** (before any changes):
   ```bash
   # Capture current behavior
   ./run_tests.py > baseline/tests_$(date +%Y%m%d_%H%M%S).txt 2>&1
   ./dev_cli.py -i 2 src/model_checker/theory_lib/logos/examples.py > baseline/logos_$(date +%Y%m%d_%H%M%S).txt 2>&1
   ./dev_cli.py -i 2 src/model_checker/theory_lib/*/examples.py > baseline/all_theories_$(date +%Y%m%d_%H%M%S).txt 2>&1
   ```

2. **Incremental Changes**:
   - Make one atomic change (e.g., move one class)
   - Run targeted tests immediately
   - Compare outputs with baseline
   - Commit only if no regressions

3. **Regression Detection**:
   ```bash
   # Compare outputs
   diff -u baseline/last_output.txt current_output.txt
   # Any new warnings, errors, or changed behavior = rollback
   ```

## Implementation Plan

### Phase 1: Model.py Refactoring (8-10 days)

**Status**: ⏳ Not Started (Reverted due to iterator regression)

#### Phase 1.1: Setup and Baseline (Day 1)

**Tasks**:
1. Create comprehensive baseline:
   ```bash
   mkdir -p docs/specs/baselines/phase1
   ./run_tests.py --unit --examples --package > docs/specs/baselines/phase1/all_tests.txt 2>&1
   
   # Capture CLI outputs for each theory with iteration
   for theory in logos bimodal exclusion imposition; do
     ./dev_cli.py -i 3 src/model_checker/theory_lib/$theory/examples.py > \
       docs/specs/baselines/phase1/${theory}_examples.txt 2>&1
   done
   
   # Capture specific subtheory outputs
   ./dev_cli.py -i 2 src/model_checker/theory_lib/logos/subtheories/*/examples.py > \
     docs/specs/baselines/phase1/logos_subtheories.txt 2>&1
   ```

2. Create test scripts:
   ```bash
   # Create scripts/test_refactoring.sh
   # Create scripts/compare_outputs.py
   ```

3. Document existing warnings/issues in `docs/specs/baselines/phase1/known_issues.md`

**Testing**: Verify all baseline captures completed successfully

#### Phase 1.2: Create models/ subpackage structure (Day 2)

**Tasks**:
1. Create directory structure:
   ```
   src/model_checker/models/
   ├── __init__.py
   ├── README.md
   ├── semantic.py      # SemanticDefaults
   ├── proposition.py   # PropositionDefaults
   ├── constraints.py   # ModelConstraints
   ├── structure.py     # ModelDefaults (core)
   ├── printing.py      # Printing functionality
   ├── analysis.py      # Analysis utilities
   └── tests/
       ├── __init__.py
       ├── test_semantic.py
       ├── test_proposition.py
       ├── test_constraints.py
       ├── test_structure.py
       └── test_imports.py
   ```

2. Create compatibility imports in model.py

**Testing**:
```bash
# After each file creation
./run_tests.py --unit --package
# Verify no import errors
```

#### Phase 1.3: Move SemanticDefaults (Day 3)

**Tasks**:
1. Move SemanticDefaults class to models/semantic.py
2. Update imports in model.py
3. Add comprehensive tests for SemanticDefaults

**Targeted Testing**:
```bash
# Test semantic operations directly
pytest src/model_checker/models/tests/test_semantic.py -v

# Test theories that use SemanticDefaults
./dev_cli.py src/model_checker/theory_lib/logos/examples.py | grep -E "WARNING|Error"
./dev_cli.py src/model_checker/theory_lib/bimodal/examples.py | grep -E "WARNING|Error"

# Compare with baseline
diff -u docs/specs/baselines/phase1/logos_examples.txt current_logos.txt
```

**Regression Criteria**:
- No new warnings
- No changes in model output
- All tests pass

#### Phase 1.4: Move PropositionDefaults (Day 4)

**Tasks**:
1. Move PropositionDefaults class to models/proposition.py
2. Update all imports
3. Test proposition functionality

**Targeted Testing**:
```bash
# Test proposition creation and evaluation
pytest src/model_checker/models/tests/test_proposition.py -v

# Test with complex formulas
./dev_cli.py -i 2 src/model_checker/theory_lib/logos/subtheories/counterfactual/examples.py > current_cf.txt
diff -u docs/specs/baselines/phase1/logos_subtheories.txt current_cf.txt
```

#### Phase 1.5: Move ModelConstraints (Day 5)

**Tasks**:
1. Move ModelConstraints to models/constraints.py
2. Ensure proper interaction with other components
3. Test constraint generation

**Targeted Testing**:
```bash
# Test constraint generation
pytest src/model_checker/models/tests/test_constraints.py -v

# Test all theories
for theory in logos bimodal exclusion imposition; do
  ./dev_cli.py src/model_checker/theory_lib/$theory/examples.py > current_$theory.txt
  diff -u docs/specs/baselines/phase1/${theory}_examples.txt current_$theory.txt
done
```

#### Phase 1.6: Split ModelDefaults (Days 6-7)

**Critical Step - Iterator Regression Point**

**Tasks**:
1. Extract printing functionality to models/printing.py
2. Extract analysis functionality to models/analysis.py
3. Keep core Z3 solving in models/structure.py
4. **Special attention to**:
   - Attribute initialization order
   - Iterator model creation
   - Z3 solver lifecycle

**Targeted Testing**:
```bash
# Test iterator specifically
./dev_cli.py -i 3 src/model_checker/theory_lib/logos/examples.py > current_iteration.txt
grep "WARNING" current_iteration.txt  # Should be empty

# Test attribute initialization
pytest src/model_checker/models/tests/test_structure.py::test_attribute_initialization -v

# Full regression test
./run_tests.py --unit --examples --package > current_all_tests.txt 2>&1
diff -u docs/specs/baselines/phase1/all_tests.txt current_all_tests.txt
```

#### Phase 1.7: Cleanup and Documentation (Day 8)

**Tasks**:
1. Remove old code from model.py (keep only imports)
2. Update all documentation
3. Run full test suite
4. Update this plan with completion status

**Final Validation**:
```bash
# Complete test suite
./run_tests.py --unit --examples --package

# All CLI examples
find src/model_checker/theory_lib -name "examples.py" -exec ./dev_cli.py {} \; > all_examples.txt
grep -E "WARNING|Error|FAILED" all_examples.txt  # Should be minimal/expected only

# Performance comparison
time ./run_tests.py --examples  # Should not be significantly slower
```

#### Phase 1.8: Post-Refactoring Review (Days 9-10)

**Tasks**:
1. Code review all changes
2. Document lessons learned in `docs/specs/findings/003_model_refactoring_success.md`
3. Update Phase 2 plan based on experience
4. Commit with detailed message explaining changes

**Success Criteria**:
- [ ] No new warnings in any theory
- [ ] All tests pass
- [ ] Iterator works correctly with multiple models
- [ ] No performance degradation
- [ ] Code is more maintainable (< 500 lines per file)

### Phase 2: Utils.py Refactoring (5-6 days)

**Status**: ⏳ Not Started

#### Phase 2.1: Setup and Baseline (Day 1)

**Tasks**:
1. Create baseline for utils functionality:
   ```bash
   mkdir -p docs/specs/baselines/phase2
   
   # Test all functionality that uses utils
   ./run_tests.py --unit --package > docs/specs/baselines/phase2/all_tests.txt 2>&1
   
   # Test parsing functionality specifically
   ./dev_cli.py src/model_checker/theory_lib/logos/subtheories/*/examples.py > \
     docs/specs/baselines/phase2/parsing_tests.txt 2>&1
   ```

2. Map all utils dependencies:
   ```bash
   grep -r "from model_checker.utils import" src/ > docs/specs/baselines/phase2/utils_imports.txt
   ```

#### Phase 2.2: Create utils/ subpackage structure (Day 2)

**Tasks**:
1. Create structure:
   ```
   src/model_checker/utils/
   ├── __init__.py
   ├── README.md
   ├── parsing.py       # Expression parsing utilities
   ├── z3_helpers.py    # Z3-specific utilities
   ├── bitvector.py     # Bitvector operations
   ├── file_ops.py      # File loading utilities
   ├── version.py       # Version management
   ├── testing.py       # Test utilities
   └── tests/
       └── test_*.py
   ```

#### Phase 2.3-2.6: Incremental Migration (Days 3-5)

**Daily Pattern**:
- Move one category of utilities per day
- Test after each move
- Update all imports
- Verify no regressions

**Testing After Each Migration**:
```bash
# Run targeted tests
pytest src/model_checker/utils/tests/test_[category].py -v

# Test dependent functionality
./dev_cli.py src/model_checker/theory_lib/*/examples.py | grep -E "WARNING|Error"

# Full regression check
./run_tests.py --unit --package
```

### Phase 3: Syntactic.py Refactoring (4-5 days)

**Status**: ⏳ Not Started

#### Phase 3.1: Setup and Analysis (Day 1)

**Tasks**:
1. Baseline syntactic functionality
2. Map operator dependencies
3. Test parsing edge cases

#### Phase 3.2-3.4: Incremental Migration (Days 2-4)

**Structure**:
```
src/model_checker/syntactic/
├── sentence.py     # Sentence class
├── operators.py    # Operator base classes
├── syntax.py       # Syntax processing
├── parser.py       # Expression parsing
└── collections.py  # OperatorCollection
```

**Critical Testing**:
```bash
# Test operator parsing for each theory
for theory in logos bimodal exclusion imposition; do
  pytest src/model_checker/theory_lib/$theory/tests/test_*operators.py -v
done

# Test complex formula parsing
./dev_cli.py -p src/model_checker/theory_lib/logos/subtheories/*/examples.py
```

### Phase 4: Subpackage Optimization (3-4 days)

**Status**: ⏳ Not Started

#### Targets:
1. **builder/module.py** (1031 lines) → Split into loader.py, executor.py, config.py
2. **iterate/core.py** (1007 lines) → Split into base.py, strategies.py, constraints.py

**Testing Focus**:
- Iterator regression testing (critical!)
- Module loading edge cases
- Cross-theory compatibility

### Phase 5: Code Quality and Cleanup (2-3 days)

**Status**: ⏳ Not Started

#### Tasks:
1. Add missing module docstrings
2. Remove TODO/FIXME comments
3. Fix import organization
4. Add type hints to public APIs

**Validation**:
```bash
# Lint checks
pylint src/model_checker --disable=all --enable=missing-docstring
mypy src/model_checker --ignore-missing-imports

# TODO/FIXME audit
grep -r "TODO\|FIXME" src/ > remaining_todos.txt
```

### Phase 6: Documentation Completion (2-3 days)

**Status**: ⏳ Not Started

#### Tasks:
1. Ensure every directory has README.md
2. Generate API documentation
3. Verify all cross-references
4. Update user guides

### Phase 7: Final Testing and Release Prep (3-4 days)

**Status**: ⏳ Not Started

#### Tasks:
1. Full test coverage analysis
2. Cross-platform testing
3. Performance benchmarking
4. Create CHANGELOG.md
5. Tag v1.0.0-rc1

**Final Validation Suite**:
```bash
# Complete test battery
./run_tests.py --unit --examples --package --coverage

# All theories with multiple iterations
for i in 1 2 3 5; do
  for theory in logos bimodal exclusion imposition; do
    echo "Testing $theory with $i iterations..."
    ./dev_cli.py -i $i src/model_checker/theory_lib/$theory/examples.py > \
      final_tests/${theory}_${i}iter.txt 2>&1
  done
done

# Performance comparison
time ./run_tests.py --examples > performance_v1.txt

# No regressions allowed
grep -r "WARNING\|Error" final_tests/ | grep -v "known_issues"
```

## Progress Tracking

### Completed
- [x] Iterator regression investigation (findings/002)
- [x] Model.py refactoring reverted
- [x] Comprehensive testing protocol defined

### In Progress
- [ ] Phase 1: Model.py refactoring (0/8 tasks)

### Upcoming
- [ ] Phase 2: Utils.py refactoring
- [ ] Phase 3: Syntactic.py refactoring  
- [ ] Phase 4: Subpackage optimization
- [ ] Phase 5: Code quality
- [ ] Phase 6: Documentation
- [ ] Phase 7: Release preparation

## Risk Management

### High-Risk Areas
1. **Iterator functionality** - Test extensively with multiple models
2. **Z3 solver management** - Verify proper cleanup and isolation
3. **Import compatibility** - Maintain backward compatibility
4. **Performance** - Monitor for degradation

### Mitigation Strategies
1. **Incremental changes** - One atomic change at a time
2. **Continuous testing** - Test after every change
3. **Baseline comparison** - Detect regressions immediately
4. **Quick rollback** - Git reset if issues detected

## Success Metrics

1. **No regressions**: Zero new warnings or errors
2. **Test coverage**: Maintain or improve current coverage
3. **Performance**: No significant slowdown (< 5%)
4. **Code quality**: All files < 500 lines
5. **Documentation**: 100% directory coverage with READMEs

## Timeline Summary

- **Phase 1**: 8-10 days (Model.py)
- **Phase 2**: 5-6 days (Utils.py)
- **Phase 3**: 4-5 days (Syntactic.py)
- **Phase 4**: 3-4 days (Subpackages)
- **Phase 5**: 2-3 days (Code quality)
- **Phase 6**: 2-3 days (Documentation)
- **Phase 7**: 3-4 days (Release prep)

**Total**: 27-35 days for complete v1.0 preparation

## Next Steps

1. Begin Phase 1.1: Create baselines for model.py refactoring
2. Set up automated testing scripts
3. Review iterator implementation before refactoring

## References

- [findings/002_iterator_warnings_investigation.md](../findings/002_iterator_warnings_investigation.md) - Iterator regression analysis
- [STYLE_GUIDE.md](../../STYLE_GUIDE.md) - Coding and documentation standards
- [IMPLEMENTATION.md](../../IMPLEMENTATION.md) - Development process guidelines
- [TESTS.md](../../TESTS.md) - Testing procedures and best practices
