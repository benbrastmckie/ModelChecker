# Utils.py Refactoring Implementation Plan

**Plan ID**: 012  
**Created**: 2025-08-07  
**Status**: Draft  
**Author**: AI Assistant  
**Related**: [008_v1_release_preparation.md](008_v1_release_preparation.md)

## Executive Summary

This plan details the refactoring of `utils.py` (1008 lines) into a well-organized `utils/` subpackage. Following the successful model.py refactoring pattern, this plan emphasizes incremental migration with comprehensive dual testing methodology to prevent regressions.

## Current State Analysis

### File Overview
- **Location**: `/src/model_checker/utils.py`
- **Size**: 1008 lines
- **Dependencies**: Used by 30+ files across the codebase
- **Critical Functions**: Parse expression, bitvector operations, Z3 helpers, testing utilities

### Component Categories

1. **Z3 Context Management** (lines 31-66)
   - `Z3ContextManager` class
   - Critical for solver isolation

2. **Syntactic Helpers** (lines 67-179)
   - `parse_expression()` - Core expression parser
   - `op_left_right()` - Operator parsing helper
   - Used by all theory operators

3. **Print Helpers** (lines 180-320)
   - `pretty_set_print()` - Set formatting
   - `binary_bitvector()` - Binary representation
   - `int_to_binary()` - Number conversion
   - `index_to_substate()` - State indexing
   - `bitvec_to_substates()` - Bitvector conversion
   - `bitvec_to_worldstate()` - World state conversion

4. **Z3 Helpers** (lines 321-380)
   - `ForAll()` - Quantifier wrapper
   - `Exists()` - Quantifier wrapper
   - Critical for semantic clauses

5. **Error Reporting** (lines 381-420)
   - `not_implemented_string()` - Standard error messages
   - `flatten()` - List flattening utility

6. **API Functions** (lines 421-520)
   - `get_example()` - Example retrieval
   - `get_theory()` - Theory loading

7. **Versioning and Licensing** (lines 521-720)
   - `get_model_checker_version()` - Version info
   - `get_theory_version()` - Theory versioning
   - `check_theory_compatibility()` - Compatibility checks
   - `get_license_template()` - License generation

8. **Testing Utilities** (lines 721-1008)
   - `run_test()` - Basic test runner
   - `TestResultData` class - Test results
   - `run_enhanced_test()` - Enhanced testing
   - `run_strategy_test()` - Strategy testing

### Dependency Analysis

#### Most Critical Dependencies
1. **parse_expression** - Used by all operator parsing
2. **bitvec_to_substates** - Used by semantic evaluations
3. **Z3ContextManager** - Used by test isolation
4. **ForAll/Exists** - Used by semantic clauses

#### Import Patterns
```python
# Common imports found:
from model_checker.utils import bitvec_to_substates, pretty_set_print
from model_checker.utils import ForAll, Exists
from model_checker.utils import Z3ContextManager
from model_checker.utils import get_model_checker_version
```

## Design Decisions

### Subpackage Structure

```
src/model_checker/utils/
├── __init__.py          # Re-export all public functions
├── README.md           # Comprehensive documentation
├── context.py          # Z3ContextManager
├── parsing.py          # Expression parsing (parse_expression, op_left_right)
├── bitvector.py        # Bitvector operations and conversions
├── z3_helpers.py       # ForAll, Exists, and Z3 utilities
├── formatting.py       # Print helpers (pretty_set_print, etc.)
├── errors.py           # Error reporting utilities
├── api.py              # get_example, get_theory functions
├── version.py          # Versioning and licensing
├── testing.py          # Test runner utilities
└── tests/
    ├── __init__.py
    ├── test_parsing.py
    ├── test_bitvector.py
    ├── test_z3_helpers.py
    ├── test_formatting.py
    └── test_imports.py
```

### Migration Strategy

1. **Incremental Approach**: One category per phase
2. **Import Compatibility**: Maintain backward compatibility through __init__.py
3. **Test Coverage**: Write tests before moving each component
4. **Dual Testing**: Use both test runner and dev_cli.py validation

### Risk Assessment

#### High Risk Components
1. **parse_expression** - Core to all formula parsing
2. **Z3ContextManager** - Critical for test isolation
3. **bitvec_to_substates** - Used in semantic evaluations

#### Medium Risk Components
1. **ForAll/Exists** - Z3 wrapper functions
2. **Testing utilities** - Could affect test infrastructure

#### Low Risk Components
1. **Formatting functions** - Display only
2. **Version utilities** - Metadata only
3. **Error utilities** - Simple string generation

## Implementation Phases

### Phase 2.1: Setup and Baseline (Day 1)

**Tasks**:
1. Create comprehensive baseline
2. Map all import dependencies
3. Create utils/ directory structure
4. Write initial test infrastructure

**Testing Protocol**:
```bash
# Baseline capture
mkdir -p docs/specs/baselines/phase2
./run_tests.py --unit --package > docs/specs/baselines/phase2/all_tests.txt 2>&1

# Test parsing specifically
for theory in logos exclusion imposition bimodal; do
  ./dev_cli.py src/model_checker/theory_lib/$theory/examples.py > \
    docs/specs/baselines/phase2/${theory}_parsing.txt 2>&1
done

# Map dependencies
grep -r "from model_checker.utils import" src/ > \
  docs/specs/baselines/phase2/utils_imports.txt
```

### Phase 2.2: Move Z3 Context Management (Day 2)

**Component**: Z3ContextManager
**Target**: utils/context.py

**Tasks**:
1. Write comprehensive tests for Z3ContextManager
2. Move class to context.py
3. Update imports in utils.py
4. Test with builder/tests/test_z3_isolation.py

**Critical Testing**:
```bash
# Test Z3 isolation
pytest src/model_checker/builder/tests/test_z3_isolation.py -v

# Test example isolation
./dev_cli.py -i 3 src/model_checker/theory_lib/logos/examples.py
```

### Phase 2.3: Move Parsing Utilities (Day 3)

**Components**: parse_expression, op_left_right
**Target**: utils/parsing.py

**Tasks**:
1. Write tests covering all operator types
2. Move parsing functions
3. Update all operator imports
4. Test all theory parsing

**Critical Testing**:
```bash
# Test each theory's operator parsing
for theory in logos exclusion imposition bimodal; do
  pytest src/model_checker/theory_lib/$theory/tests/test_*operators.py -v
done

# Test complex expressions
./dev_cli.py -p src/model_checker/theory_lib/logos/subtheories/*/examples.py
```

### Phase 2.4: Move Bitvector Operations (Day 4)

**Components**: All bitvector-related functions
**Target**: utils/bitvector.py

**Tasks**:
1. Write tests for bitvector conversions
2. Move all bitvector functions
3. Update semantic imports
4. Test state space representations

**Testing Focus**:
- State space generation
- Bitvector to substate conversions
- World state representations

### Phase 2.5: Move Z3 Helpers (Day 5)

**Components**: ForAll, Exists
**Target**: utils/z3_helpers.py

**Tasks**:
1. Write tests for quantifier functions
2. Move Z3 helper functions
3. Update semantic clause imports
4. Test quantified formulas

### Phase 2.6: Move Remaining Utilities (Day 6)

**Components**: formatting, errors, api, version, testing
**Targets**: Respective module files

**Tasks**:
1. Move each component group
2. Update imports progressively
3. Maintain test coverage

### Phase 2.7: Cleanup and Validation (Day 7)

**Tasks**:
1. Remove old code from utils.py
2. Ensure __init__.py exports all functions
3. Update documentation
4. Run comprehensive validation

## Testing Protocols

### Dual Testing Methodology

#### Method 1: Test-Driven Development
```bash
# Before moving each component
# 1. Write comprehensive tests
pytest src/model_checker/utils/tests/test_<component>.py -v

# 2. Move code and ensure tests pass
# 3. Run full regression
./run_tests.py --unit --package
```

#### Method 2: CLI Validation
```bash
# After each component migration
# 1. Test all theories
for theory in logos exclusion imposition bimodal; do
  ./dev_cli.py src/model_checker/theory_lib/$theory/examples.py > \
    current/${theory}_after.txt 2>&1
  diff -u docs/specs/baselines/phase2/${theory}_parsing.txt \
    current/${theory}_after.txt
done

# 2. Test subtheories with iterate=2
for sub in counterfactual constitutive extensional modal relevance; do
  ./dev_cli.py src/model_checker/theory_lib/logos/subtheories/$sub/examples.py
done

# 3. Check for regressions
grep -E "WARNING|Error|AttributeError" current/*.txt
```

### Regression Criteria

1. **No new warnings or errors**
2. **Identical parsing results**
3. **Same bitvector representations**
4. **Z3 isolation maintained**
5. **No performance degradation**

## Success Criteria

1. **Code Organization**
   - utils.py reduced to < 100 lines (imports only)
   - Each module < 300 lines
   - Clear separation of concerns

2. **Testing**
   - 100% test coverage for moved components
   - All existing tests pass
   - No CLI regressions

3. **Documentation**
   - Comprehensive README.md
   - Each module documented
   - Migration guide updated

4. **Import Compatibility**
   - All existing imports work
   - Clean import paths available
   - No circular dependencies

## Risk Mitigation

1. **Parse Expression Issues**
   - Test with complex nested expressions
   - Verify all operator types
   - Check edge cases (empty tokens, malformed input)

2. **Z3 Context Leakage**
   - Verify isolation between examples
   - Test with multiple iterations
   - Monitor solver state

3. **Import Breakage**
   - Use __init__.py for compatibility
   - Test all dependent files
   - Provide clear migration path

## Timeline

- **Day 1**: Setup and baseline
- **Day 2**: Z3 context management
- **Day 3**: Parsing utilities (HIGH RISK)
- **Day 4**: Bitvector operations
- **Day 5**: Z3 helpers
- **Day 6**: Remaining utilities
- **Day 7**: Cleanup and validation

**Total**: 7 days with buffer for issues

## Next Steps

1. Review and approve this plan
2. Begin Phase 2.1 baseline capture
3. Create test infrastructure
4. Start incremental migration

## References

- [008_v1_release_preparation.md](008_v1_release_preparation.md) - Main refactoring plan
- [010_model_py_removal_and_polish.md](010_model_py_removal_and_polish.md) - Successful pattern
- [findings/011_model_py_removal_success.md](../findings/011_model_py_removal_success.md) - Lessons learned